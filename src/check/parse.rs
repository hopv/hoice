//! Parsers used by the checker.

use nom::multispace ;

use check::* ;

named!{
  #[doc = "Comment parser."],
  pub cmt, re_bytes_find!(r#"^;.*[\n\r]*"#)
}

named!{
  #[doc = "Parses comments and spaces."],
  pub spc_cmt<()>, map!(
    many0!( alt_complete!(cmt | multispace) ), |_| ()
  )
}

named!{
  #[doc = "Simple ident parser."],
  pub sident<& str>, map_res!(
    re_bytes_find!(r#"^[a-zA-Z~!@\$%^&\*_\-\+=<>\.\?\^/][a-zA-Z0-9~!@\$%^&\*_\-\+=<>\.\?\^/:]*"#),
    |bytes| ::std::str::from_utf8(bytes).chain_err(
      || "could not convert bytes to utf8"
    )
  )
}

named!{
  #[doc = "Quoted ident parser."],
  pub qident<& str>, map_res!(
    re_bytes_find!(r#"^\|[^\|]*\|"#),
    |bytes| ::std::str::from_utf8(bytes).chain_err(
      || "could not convert bytes to utf8"
    )
  )
}

named!{
  #[doc = "Ident parser."],
  pub ident<String>, alt_complete!(
    map!(sident, |s| format!("|{}|", s)) | map!(qident, |s| s.to_string())
  )
}

named!{
  #[doc = "Type parser."],
  pub typ<Typ>, map!(
    map_res!(
      re_bytes_find!("^[A-Z][a-zA-Z]*"),
      |bytes| ::std::str::from_utf8(bytes).chain_err(
        || "could not convert bytes to utf8"
      )
    ), |s| s.to_string()
  )
}

named!{
  #[doc = "Parses a predicate declaration."],
  pub pred_dec<PredDec>, do_parse!(
    char!('(') >>
    spc_cmt >> tag!("declare-fun") >>
    spc_cmt >> pred: ident >>
    spc_cmt >> char!('(') >>
    spc_cmt >> sig: many0!(
      terminated!(typ, spc_cmt)
    ) >>
    spc_cmt >> char!(')') >>
    spc_cmt >> typ >>
    spc_cmt >> char!(')') >> (
      PredDec { pred, sig }
    )
  )
}

named!{
  #[doc = "Parses an s-expression."],
  pub s_expr<Term>, alt_complete!(
    // (Un)quoted ident.
    ident |
    // Anything but a space or a paren.
    map!(
      map_res!(
        re_bytes_find!(r#"^[^\s()][^\s()]*"#),
        |bytes| ::std::str::from_utf8(bytes).chain_err(
          || "could not convert bytes to utf8"
        )
      ), |s| s.to_string()
    ) |
    // A sequence of terms between parens.
    do_parse!(
      char!('(') >>
      spc_cmt >> terms: many1!(
        terminated!(s_expr, spc_cmt)
      ) >>
      spc_cmt >> char!(')') >> ({
        let mut s = "( ".to_string() ;
        for term in terms {
          s.push_str(& term) ;
          s.push(' ')
        }
        s.push(')') ;
        s
      })
    )
  )
}

named!{
  #[doc = "Parses some arguments."],
  pub arguments<Args>, do_parse!(
    char!('(') >>
    spc_cmt >> args: many0!(
      do_parse!(
        char!('(') >>
        spc_cmt >> id: ident >>
        spc_cmt >> ty: typ >>
        spc_cmt >> char!(')') >>
        spc_cmt >> (
          (id, ty)
        )
      )
    ) >>
    spc_cmt >> char!(')') >> (args)
  )
}

named!{
  #[doc = "Parses a predicate definition."],
  pub pred_def<PredDef>, do_parse!(
    char!('(') >>
    spc_cmt >> tag!("define-fun") >>
    spc_cmt >> pred: ident >>
    spc_cmt >> args: arguments >>
    spc_cmt >> typ >>
    spc_cmt >> body: s_expr >>
    spc_cmt >> char!(')') >> (
      PredDef { pred, args, body }
    )
  )
}

named!{
  #[doc = "Parses a conjunction."],
  pub conjunction< Vec<Term> >, alt_complete!(
    do_parse!(
      char!('(') >>
      spc_cmt >> tag!("and") >>
      spc_cmt >> exprss: many0!(
        terminated!(conjunction, spc_cmt)
      ) >>
      spc_cmt >> char!(')') >> ({
        let mut iter = exprss.into_iter() ;
        if let Some(mut exprs) = iter.next() {
          for es in iter {
            use std::iter::Extend ;
            exprs.extend(es)
          }
          exprs
        } else {
          panic!("nullary `and` application")
        }
      })
    ) |

    map!(s_expr, |s| vec![s])
  )
}

named!{
  #[doc = "Parses a clause."],
  pub clause<Clause>, do_parse!(
    char!('(') >>
    spc_cmt >> tag!("assert") >>
    spc_cmt >> char!('(') >>
    spc_cmt >> clause: alt_complete!(

      do_parse!(
        spc_cmt >> tag!("forall") >>
        spc_cmt >> args: arguments >>
        spc_cmt >> char!('(') >>
        spc_cmt >> tag!("=>") >>
        spc_cmt >> lhs: conjunction >>
        spc_cmt >> rhs: s_expr >>
        spc_cmt >> char!(')') >> (
          Clause { args, lhs, rhs }
        )
      ) |

      do_parse!(
        spc_cmt >> tag!("not") >>
        spc_cmt >> char!('(') >>
        spc_cmt >> tag!("exists") >>
        spc_cmt >> args: arguments >>
        spc_cmt >> lhs: conjunction >>
        spc_cmt >> char!(')') >> (
          Clause { args, lhs, rhs: "false".into() }
        )
      )
    ) >>
    spc_cmt >> char!(')') >>
    spc_cmt >> char!(')') >> (
      clause
    )
  )
}

named!{
  #[doc = "Parses the infer command."],
  pub infer<()>, do_parse!(
    char!('(') >>
    spc_cmt >> tag!("check-sat") >>
    spc_cmt >> char!(')') >> (())
  )
}

named!{
  #[doc = "Parses a `set-info`."],
  pub set_info<()>, do_parse!(
    char!('(') >>
    spc_cmt >> tag!("set-info") >>
    spc_cmt >> re_bytes_find!(r#"^:[a-zA-Z0-9\-]*"#) >>
    spc_cmt >> alt_complete!(
      re_bytes_find!(r#"^"[^"]*""#) |
      re_bytes_find!(r#"^[^)]*"#)
    ) >>
    spc_cmt >> char!(')') >> (())
  )
}

named!{
  #[doc = "Parses a `set-logic`."],
  pub set_logic<()>, do_parse!(
    char!('(') >>
    spc_cmt >> tag!("set-logic") >>
    spc_cmt >> tag!("HORN") >>
    spc_cmt >> char!(')') >> (())
  )
}

named!{
  #[doc = "Parses a `hc` file."],
  pub parse_input<Input>, do_parse!(
    spc_cmt >> many0!(
      terminated!(
        alt_complete!( set_info | set_logic ), spc_cmt
      )
    ) >>
    spc_cmt >> pred_decs: many0!(
      terminated!(pred_dec, spc_cmt)
    ) >>
    spc_cmt >> clauses: many0!(
      terminated!(clause, spc_cmt)
    ) >>
    spc_cmt >> dbg_dmp!(infer) >>
    spc_cmt >> (
      Input { pred_decs, clauses }
    )
  )
}


named!{
  #[doc = "Parses the output of a horn clause run."],
  pub parse_output<Output>, do_parse!(
    spc_cmt >> tag!("sat") >>
    spc_cmt >> char!('(') >>
    spc_cmt >> tag!("model") >>
    spc_cmt >> pred_defs: many0!(
      terminated!(pred_def, spc_cmt)
    ) >>
    spc_cmt >> char!(')') >>
    spc_cmt >> (
      Output { pred_defs }
    )
  )
}


named!{
  #[doc = "Parses the output of an eldarica run."],
  pub parse_eld_output<Output>, do_parse!(
    spc_cmt >> dbg_dmp!(tag!("sat")) >>
    spc_cmt >> pred_defs: many0!(
      terminated!(dbg_dmp!(pred_def), spc_cmt)
    ) >>
    spc_cmt >> (
      Output { pred_defs }
    )
  )
}
//! Parsers used by the checker.

use nom::multispace ;

use errors::* ;
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
    re_bytes_find!("^[a-zA-Z][a-zA-Z0-9_]*"),
    |bytes| ::std::str::from_utf8(bytes).chain_err(
      || "could not convert bytes to utf8"
    )
  )
}

named!{
  #[doc = "Quoted ident parser."],
  pub qident<& str>, alt_complete!(
    delimited!(
      char!('|'), sident, char!('|')
    ) |
    map_res!(
      re_bytes_find!(r#"^\|[^\|]*\|"#),
      |bytes| ::std::str::from_utf8(bytes).chain_err(
        || "could not convert bytes to utf8"
      )
    )
  )
}

named!{
  #[doc = "Ident parser."],
  pub ident<String>, map!(
    alt_complete!(sident | qident), |s| s.to_string()
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
    spc_cmt >> tag!("declare-pred") >>
    spc_cmt >> pred: ident >>
    spc_cmt >> char!('(') >>
    spc_cmt >> sig: many0!(
      terminated!(typ, spc_cmt)
    ) >>
    spc_cmt >> char!(')') >>
    spc_cmt >> char!(')') >> (
      PredDec { pred, sig }
    )
  )
}

named!{
  #[doc = "Parses an s-expression."],
  pub s_expr<Term>, alt_complete!(
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
    ) |
    map!(
      map_res!(
        re_bytes_find!(r#"^[^ ()]"#),
        |bytes| ::std::str::from_utf8(bytes).chain_err(
          || "could not convert bytes to utf8"
        )
      ), |s| s.to_string()
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
    spc_cmt >> tag!("define-pred") >>
    spc_cmt >> pred: ident >>
    spc_cmt >> args: arguments >>
    spc_cmt >> body: s_expr >>
    spc_cmt >> char!(')') >> (
      PredDef { pred, args, body }
    )
  )
}

named!{
  #[doc = "Parses a clause."],
  pub clause<Clause>, do_parse!(
    char!('(') >>
    spc_cmt >> tag!("clause") >>
    spc_cmt >> args: arguments >>
    spc_cmt >> char!('(') >>
    spc_cmt >> lhs: many0!(
      terminated!(s_expr, spc_cmt)
    ) >>
    spc_cmt >> char!(')') >>
    spc_cmt >> rhs: s_expr >>
    spc_cmt >> char!(')') >> (
      Clause { args, lhs, rhs }
    )
  )
}
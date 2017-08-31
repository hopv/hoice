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


/// Parser.
pub struct InParser<'a> {
  /// Predicate definitions.
  pub pred_defs: Vec<PredDef>,
  /// Predicate declarations.
  pub pred_decs: Vec<PredDec>,
  /// Clauses.
  pub clauses: Vec<Clause>,
  /// Characters.
  chars: ::std::str::Chars<'a>,
  /// Buffer storing characters pushed back.
  buf: Vec<char>,
}
impl<'a> InParser<'a> {
  /// Constructor.
  pub fn mk(s: & 'a str) -> Self {
    InParser {
      pred_defs: vec![], pred_decs: vec![], clauses: vec![],
      chars: s.chars(), buf: vec![]
    }
  }

  /// Swaps input characters.
  pub fn swap(& mut self, s: & 'a str) {
    self.chars = s.chars() ;
    assert!( self.buf.is_empty() )
  }

  /// True if there is a next character.
  fn has_next(& mut self) -> bool {
    if ! self.buf.is_empty() {
      true
    } else if let Some(c) = self.next() {
      self.buf.push(c) ;
      true
    } else {
      false
    }
  }

  /// Next character.
  fn next(& mut self) -> Option<char> {
    if let Some(c) = self.buf.pop() {
      Some(c)
    } else {
      self.chars.next()
    }
  }

  /// Pushes back a character.
  fn txen(& mut self, c: char) {
    self.buf.push(c)
  }

  /// Backtracks some characters.
  fn backtrack(& mut self, mut mem: Vec<char>) {
    use std::iter::Extend ;
    mem.reverse() ;
    self.buf.extend(mem) ;
    // print!("done backtracking: `") ;
    // for c in & self.buf {
    //   print!("{}", c)
    // }
    // println!("`")
  }

  /// Parses a tag or fails.
  fn tag(& mut self, tag: & str) -> Res<()> {
    if ! self.tag_opt(tag) {
      bail!("expected tag `{}`", conf.emph(tag))
    } else {
      Ok(())
    }
  }
  /// Tries to parse a tag.
  fn tag_opt(& mut self, tag: & str) -> bool {
    // println!("  tag: {}", tag) ;
    let mut mem = vec![] ;
    for c in tag.chars() {
      if let Some(next) = self.next() {
        mem.push(next) ;
        // println!("  - {}/{}", c, next) ;
        if c != next {
          self.backtrack(mem) ;
          return false
        }
      } else {
        self.backtrack(mem) ;
        return false
      }
    }
    return true
  }

  /// Parses a character or fails.
  fn char(& mut self, c: char) -> Res<()> {
    if ! self.char_opt(c) {
      bail!("expected character `{}`", conf.emph( & c.to_string() ))
    } else {
      Ok(())
    }
  }
  /// Tries to parse a character.
  fn char_opt(& mut self, c: char) -> bool {
    if let Some(next) = self.next() {
      if next == c {
        true
      } else {
        self.txen(next) ;
        false
      }
    } else {
      false
    }
  }

  /// Parses everything it can until (and excluding) some character.
  fn not_char(& mut self, c: char) -> String {
    let mut s = String::new() ;
    while let Some(next) = self.next() {
      if next == c { self.txen(next) ; break } else {
        s.push(next)
      }
    }
    s
  }

  /// Parses an sexpression.
  fn sexpr(& mut self) -> Res<Term> {
    if self.tag_opt("true") {
      return Ok("true".into())
    } else if self.tag_opt("false") {
      return Ok("false".into())
    } else if let Some(id) = self.ident_opt() ? {
      return Ok(id)
    }
    let mut s = String::new() ;
    let mut cnt = 0 ;
    while let Some(next) = self.next() {
      s.push(next) ;
      if next == '(' {
        cnt += 1 ;
      } else if next == ')' {
        cnt -= 1 ;
        if cnt == 0 { break }
      }
    }
    if cnt != 0 {
      bail!("found eof while parsing sexpr")
    }
    // println!("sexpr {{") ;
    // println!("{}", s) ;
    // println!("}}") ;
    Ok(s)
  }

  // /// Parses everything until a whitespace.
  // fn not_ws(& mut self) {
  //   // let mut s = String::new() ;
  //   while let Some(next) = self.next() {
  //     if ! next.is_whitespace() { self.txen(next) ; break } else {
  //       // next.push(next)
  //     }
  //   }
  //   // s
  // }

  /// Reads whitespaces and comments.
  fn ws_cmt(& mut self) {
    'ws: while let Some(next) = self.next() {
      if ! next.is_whitespace() {
        if next == ';' {
          'cmt: while let Some(next) = self.next() {
            if next == '\n' { break 'cmt }
          }
        } else {
          self.txen(next) ;
          break 'ws
        }
      }
    }
  }

  /// Identifier or fails.
  fn ident(& mut self) -> Res<Ident> {
    if let Some(id) = self.ident_opt() ? {
      Ok(id)
    } else {
      bail!("expected identifier")
    }
  }
  /// Identifier.
  fn ident_opt(& mut self) -> Res< Option<Ident> > {
    if let Some(next) = self.next() {
      let id = if next == '|' {
        let id = self.not_char('|') ;
        self.char('|') ? ;
        id
      } else if next.is_alphabetic() {
        let mut id = String::new() ;
        id.push(next) ;
        while let Some(next) = self.next() {
          if next.is_alphanumeric() { id.push(next) } else {
            match next {
              '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' |
              '_' | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/' => id.push(
                next
              ),
              _ => {
                self.txen(next) ;
                break
              },
            }
          }
        }
        id
      } else {
        self.txen(next) ;
        return Ok(None)
      } ;
      Ok( Some( format!("|{}|", id) ) )
    } else {
      Ok(None)
    }
  }

  /// Set-logic.
  fn set_logic(& mut self) -> Res<bool> {
    if ! self.tag_opt("set-logic") {
      return Ok(false)
    }
    // println!("set-logic") ;
    self.ws_cmt() ;
    self.tag("HORN") ? ;
    Ok(true)
  }

  /// Set-info.
  fn set_info(& mut self) -> Res<bool> {
    if ! self.tag_opt("set-info") {
      return Ok(false)
    }
    // println!("set-info") ;
    self.ws_cmt() ;
    self.char(':') ? ;
    self.ident() ? ;
    self.ws_cmt() ;
    if self.char_opt('|') {
      self.not_char('|') ;
      self.char('|') ?
    } else if self.char_opt('"') {
      let _blah = self.not_char('"') ;
      // println!("{}", blah) ;
      self.char('"') ?
    } else {
      let _blah = self.not_char(')') ;
      // println!("{}", blah)
    }
    Ok(true)
  }

  /// Type or fails.
  fn typ(& mut self) -> Res<Typ> {
    if let Some(t) = self.typ_opt() {
      Ok(t)
    } else {
      bail!("expected type")
    }
  }
  /// Type.
  fn typ_opt(& mut self) -> Option<Typ> {
    if self.tag_opt("Bool") {
      Some( "Bool".to_string() )
    } else if self.tag_opt("Int") {
      Some( "Int".to_string() )
    } else {
      None
    }
  }

  /// Declare-fun.
  fn declare_fun(& mut self) -> Res<bool> {
    if ! self.tag_opt("declare-fun") {
      return Ok(false)
    }
    // println!("declare-fun") ;
    self.ws_cmt() ;
    let pred = self.ident() ? ;
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;
    let mut sig = vec![] ;
    loop {
      if let Some(t) = self.typ_opt() {
        sig.push(t)
      } else {
        break
      }
      self.ws_cmt()
    }
    self.ws_cmt() ;
    self.char(')') ? ;
    self.ws_cmt() ;
    self.tag("Bool") ? ;

    self.pred_decs.push(
      PredDec { pred, sig }
    ) ;

    Ok(true)
  }

  /// Arguments.
  fn args(& mut self) -> Res<Args> {
    self.char('(') ? ;
    self.ws_cmt() ;
    let mut args = vec![] ;
    while self.char_opt('(') {
      let id = self.ident() ? ;
      self.ws_cmt() ;
      let ty = self.typ() ? ;
      self.ws_cmt() ;
      self.char(')') ? ;
      self.ws_cmt() ;
      // println!("  {}: {}", id, ty) ;
      args.push( (id, ty) )
    }
    self.char(')') ? ;
    Ok(args)
  }

  /// Assert.
  fn assert(& mut self) -> Res<bool> {
    if ! self.tag_opt("assert") {
      return Ok(false)
    }
    // println!("assert") ;
    self.ws_cmt() ;
    self.char('(') ? ;

    let negated = if self.tag_opt("not") {
      self.ws_cmt() ;
      self.char('(') ? ;
      true
    } else {
      false
    } ;

    let (args, body) = if self.tag_opt("forall") {
      if negated {
        bail!("negated forall in assertion")
      }
      self.ws_cmt() ;
      let args = self.args().chain_err(|| "while parsing arguments") ? ;
      self.ws_cmt() ;
      let body = self.sexpr().chain_err(|| "while parsing body") ? ;
      (args, body)
    } else if self.tag_opt("exists") {
      self.ws_cmt() ;
      let args = self.args().chain_err(|| "while parsing arguments") ? ;
      self.ws_cmt() ;
      let body = self.sexpr().chain_err(|| "while parsing body") ? ;
      (args, body)
    } else {
      bail!("expected forall or exists")
    } ;
    self.ws_cmt() ;

    let body = if negated { format!("(not {})", body) } else { body } ;

    self.char(')').chain_err(|| "closing qualifier") ? ;
    self.ws_cmt() ;
    if negated {
      self.char(')').chain_err(|| "closing negation") ? ;
    }

    self.clauses.push(
      Clause { args, body }
    ) ;

    Ok(true)
  }

  /// Parses an `smt2` file.
  pub fn parse_input(mut self) -> Res<Input> {
    // println!("parsing") ;
    self.ws_cmt() ;

    while self.char_opt('(') {
      self.ws_cmt() ;

      if self.set_logic() ? {
        ()
      } else if self.set_info() ? {
        ()
      } else if self.declare_fun() ? {
        ()
      } else if self.assert() ? {
        ()
      } else if self.tag_opt("check-sat") {
        ()
      } else if self.tag_opt("get-model") {
        ()
      } else {
        print!("> `") ;
        while let Some(next) = self.next() {
          if next != '\n' {
            print!("{}", next)
          } else {
            break
          }
        }
        println!("`") ;
        bail!("expected item")
      }

      self.ws_cmt() ;
      self.char(')').chain_err(|| "closing item") ? ;
      self.ws_cmt()
    }

    if self.has_next() {
      print!("> `") ;
      while let Some(next) = self.next() {
        if next != '\n' {
          print!("{}", next)
        } else {
          break
        }
      }
      println!("`") ;
      bail!("could not parse the whole input file")
    }

    Ok(
      Input { pred_decs: self.pred_decs, clauses: self.clauses }
    )
  }


  /// Define-fun.
  fn define_fun(& mut self) -> Res<bool> {
    if ! self.tag_opt("define-fun") {
      return Ok(false)
    }
    self.ws_cmt() ;
    let pred = self.ident() ? ;
    self.ws_cmt() ;
    let args = self.args() ? ;
    self.ws_cmt() ;
    self.tag("Bool") ? ;
    self.ws_cmt() ;
    let body = self.sexpr() ? ;
    self.ws_cmt() ;
    self.pred_defs.push(
      PredDef { pred, args, body }
    ) ;

    Ok(true)
  }

  /// Parses an `smt2` file.
  pub fn parse_output(mut self) -> Res<Output> {
    // println!("parsing") ;
    self.ws_cmt() ;
    self.tag("sat") ? ;
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;
    self.tag("model") ? ;
    self.ws_cmt() ;

    while self.char_opt('(') {
      self.ws_cmt() ;
        // while let Some(next) = self.next() {
        //   if next != '\n' {
        //     print!("{}", next)
        //   } else {
        //     break
        //   }
        // }
        // println!("`") ;

      if self.define_fun() ? {
        ()
      } else {
        print!("> `") ;
        while let Some(next) = self.next() {
          if next != '\n' {
            print!("{}", next)
          } else {
            break
          }
        }
        println!("`") ;
        bail!("expected define-fun")
      }

      self.ws_cmt() ;
      self.char(')').chain_err(|| "closing define-fun") ? ;
      self.ws_cmt()
    }
    self.char(')').chain_err(|| "closing model") ? ;
    self.ws_cmt() ;

    if self.has_next() {
      print!("> `") ;
      while let Some(next) = self.next() {
        if next != '\n' {
          print!("{}", next)
        } else {
          break
        }
      }
      println!("`") ;
      bail!("could not parse the whole output file")
    }

    Ok(
      Output { pred_defs: self.pred_defs }
    )
  }
}
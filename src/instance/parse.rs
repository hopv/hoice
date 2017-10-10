//! SMT-LIB 2 horn clause problem parser.

use common::* ;
use instance::* ;




/// Result yielded by the parser.
#[derive(PartialEq, Eq)]
pub enum Parsed {
  /// Check-sat.
  CheckSat,
  /// Get-model.
  GetModel,
  /// Exit.
  Exit,
  /// Only parsed some item(s), no query.
  Items,
  /// Reset.
  Reset,
  /// End of file.
  Eof,
}



lazy_static!{
  /// Set of legal special characters in identifiers.
  static ref id_special_chars: HashSet<char> = {
    let mut set = HashSet::with_capacity(17) ;
    set.insert('~') ;
    set.insert('!') ;
    set.insert('@') ;
    set.insert('$') ;
    set.insert('%') ;
    set.insert('^') ;
    set.insert('&') ;
    set.insert('*') ;
    set.insert('_') ;
    set.insert('-') ;
    set.insert('+') ;
    set.insert('=') ;
    set.insert('<') ;
    set.insert('>') ;
    set.insert('.') ;
    set.insert('?') ;
    set.insert('/') ;
    set
  } ;
}



/// Extends `BufRead` with SMT-LIB 2 item parsing.
pub trait ItemRead {
  /// Reads the next item.
  ///
  /// - returns the **number of lines** read, not the number of bytes read
  /// - returns `None` once it finds `eof` and no item prior
  fn read_item(& mut self, buf: & mut String) -> Res<usize> ;
}
impl<T: ::std::io::BufRead> ItemRead for T {
  fn read_item(& mut self, buf: & mut String) -> Res<usize> {
    let mut line_count = 0 ;
    let mut start = buf.len() ;
    let mut char_override: Option<char> = None ;
    let mut opn_parens = 0 ;
    let mut cls_parens = 0 ;

    fn search_char(
      char: char, chars: & mut ::std::str::Chars
    ) -> Option<char> {
      while let Some(c) = chars.next() {
        if char == c {
          return None
        }
      }
      Some(char)
    }

    'read_lines: while self.read_line( buf ) ? != 0 {
      line_count += 1 ;
      debug_assert!( opn_parens >= cls_parens ) ;
      let mut chars = buf[start..].chars() ;
      
      if let Some(char) = char_override {
        char_override = search_char(char, & mut chars)
      }

      'inspect_chars: while let Some(c) = chars.next() {
        debug_assert!( opn_parens >= cls_parens ) ;
        
        match c {
          '(' => opn_parens += 1,
          ')' => cls_parens += 1,
          '|' => {
            debug_assert!( char_override.is_none() ) ;
            char_override = search_char('|', & mut chars)
          },
          '"' => {
            debug_assert!( char_override.is_none() ) ;
            char_override = search_char('"', & mut chars)
          },
          ';' => break 'inspect_chars,
          _ => (),
        }
      }

      if opn_parens > 0 && opn_parens == cls_parens {
        break 'read_lines
      }

      start = buf.len()
    }

    Ok(line_count)
  }
}



/// Parser context.
pub struct ParserCxt {
  /// Term stack to avoid recursion.
  term_stack: Vec< (Op, Vec<Term>, LetCount) >,
  /// Buffer used when backtracking.
  buff: Vec<(usize, char)>,
  /// Memory when parsing tags.
  mem: Vec<(usize, char)>,
  /// Map from predicate names to predicate indices.
  pred_name_map: HashMap<String, PrdIdx>,
}
impl ParserCxt {
  /// Constructor.
  pub fn new() -> Self {
    ParserCxt {
      term_stack: Vec::with_capacity(17),
      buff: Vec::with_capacity(17),
      mem: Vec::with_capacity(17),
      pred_name_map: HashMap::with_capacity(42),
    }
  }
  /// Generates a parser from itself.
  pub fn parser<'cxt, 's>(
    & 'cxt mut self, string: & 's str, line_off: usize
  ) -> Parser<'cxt, 's> {
    Parser {
      cxt: self,
      chars: string.char_indices(),
      string, line_off,
      bindings: Vec::with_capacity(7),
    }
  }

  /// Resets the parser.
  pub fn reset(& mut self) {
    self.pred_name_map.clear()
  }
}


/// Wraps an integer, represents a number of let-bindings parsed.
#[must_use]
struct LetCount {
  n: usize
}
impl LetCount {
  /// True if zero.
  pub fn is_zero(& self) -> bool{ self.n == 0 }
}


/// Parser structure. Generated from a `ParserCxt`.
pub struct Parser<'cxt, 's> {
  /// Parsing context.
  cxt: & 'cxt mut ParserCxt,
  /// Characters being read.
  chars: ::std::str::CharIndices<'s>,
  /// Text being read (for errors).
  string: & 's str,
  /// Line offset (for errors).
  line_off: usize,
  /// Stack of bindings.
  bindings: Vec< HashMap<& 's str, PTTerms> >,
}


impl<'cxt, 's> Parser<'cxt, 's> {

  /// Generates a parse error at the current position.
  fn error_here<S: Into<String>>(& mut self, msg: S) -> ErrorKind {
    if let Some( (pos, _) ) = self.next() {
      self.error(pos, msg)
    } else {
      self.error(self.string.len(), msg)
    }
  }

  /// Generates a parse error at the given position.
  fn error<S: Into<String>>(
    & self, mut char_pos: usize, msg: S
  ) -> ErrorKind {
    let msg = msg.into() ;
    let mut line_count = self.line_off ;
    let (mut pref, mut token, mut suff) = (
      "".to_string(), "<eof>".to_string(), "".to_string()
    ) ;
    for line in self.string.lines() {
      line_count += 1 ;
      if char_pos < line.len() {
        pref = line[0..char_pos].to_string() ;
        token = line[char_pos..(char_pos + 1)].to_string() ;
        suff = line[(char_pos + 1)..line.len()].to_string() ;
        break
      } else if char_pos == line.len() {
        pref = line.into() ;
        token = "\\n".into() ;
        suff = "".into() ;
        break
      } else {
        char_pos -= line.len() + 1
      }
    }
    ErrorKind::ParseError(
      ParseErrorData {
        msg, pref, token, suff, line: Some(line_count)
      }
    )
  }


  /// Returns `true` if there's still things to parse.
  fn has_next(& mut self) -> bool {
    if ! self.cxt.buff.is_empty() { true } else {
      if let Some(next) = self.chars.next() {
        self.cxt.buff.push(next) ;
        true
      } else {
        false
      }
    }
  }
  /// The next character.
  fn next(& mut self) -> Option<(usize, char)> {
    if let Some(res) = self.cxt.buff.pop() {
      Some(res)
    } else {
      self.chars.next()
    }
  }
  /// Opposite of `next`, pushes a character back.
  fn txen(& mut self, pos: usize, c: char) {
    self.cxt.buff.push( (pos, c) )
  }

  /// Pushes something on the memory.
  fn mem(& mut self, pos: usize, char: char) {
    self.cxt.mem.push((pos, char))
  }

  /// Backtracks whatever's in the memory.
  fn backtrack_mem(& mut self) {
    self.cxt.mem.reverse() ;
    for elem in self.cxt.mem.drain(0..) {
      self.cxt.buff.push(elem)
    }
  }
  /// Clears the memory.
  fn clear_mem(& mut self) {
    self.cxt.mem.clear()
  }


  /// Parses a string or fails.
  fn tag(& mut self, tag: & str) -> Res<()> {
    if self.tag_opt(tag) {
      Ok(())
    } else {
      bail!(
        self.error_here(
          format!("expected `{}`", conf.emph(tag))
        )
      )
    }
  }
  /// Tries parsing a string.
  fn tag_opt(& mut self, tag: & str) -> bool {
    for c in tag.chars() {
      if let Some( (pos, char) ) = self.next() {
        self.mem(pos, char) ;
        if char != c {
          self.backtrack_mem() ;
          return false
        }
      } else {
        self.backtrack_mem() ;
        return false
      }
    }
    self.clear_mem() ;
    true
  }

  /// Consumes whitespaces and comments.
  fn ws_cmt(& mut self) {
    'ws_cmt: while let Some( (pos, char) ) = self.next() {
      if ! char.is_whitespace() {
        if char == ';' {
          'comment: while let Some( (_, char) ) = self.next() {
            match char {
              '\n' => break 'comment,
              _ => (),
            }
          }
        } else {
          self.txen(pos, char) ;
          break 'ws_cmt
        }
      }
    }
  }

  /// Parses an ident of fails.
  fn ident(& mut self) -> Res<(usize, & 's str)> {
    if let Some(id) = self.ident_opt() {
      Ok(id)
    } else {
      bail!(
        self.error_here("expected an identifier")
      )
    }
  }
  /// Tries to parse an ident.
  fn ident_opt(& mut self) -> Option<(usize, & 's str)> {
    if let Some( (start_pos, char) ) = self.next() {
      if char == '|' {
        let (mut legal_unquoted, mut is_first) = (true, true) ;
        'quoted: while let Some((pos, char)) = self.next() {
          if char == '|' {
            let (start, end) = if legal_unquoted {
              (start_pos + 1, pos)
            } else {
              (start_pos, pos + 1)
            } ;
            return Some( (start_pos, & self.string[start..end]) )
          } else {
            legal_unquoted = legal_unquoted && (
              (! is_first && char.is_alphanumeric()) ||
              (is_first && char.is_alphabetic()) ||
              id_special_chars.contains(& char)
            ) ;
            is_first = false ;
          }
        }
        panic!("expected '|', found eof")
      } else if char.is_alphabetic() || id_special_chars.contains(& char) {
        let mut end_pos = self.string.len() ;
        'unquoted: while let Some((pos, char)) = self.next() {
          if char.is_alphanumeric() || id_special_chars.contains(& char) {
            ()
          } else {
            self.txen(pos, char) ;
            end_pos = pos ;
            break
          }
        }
        Some( (start_pos, & self.string[start_pos..end_pos]) )
      } else {
        self.txen(start_pos, char) ;
        None
      }
    } else {
      None
    }
  }

  /// Tries to parse a character.
  fn char_opt(& mut self, char: char) -> bool {
    if let Some( (pos, c) ) = self.next() {
      if c != char {
        self.txen(pos, c) ;
        false
      } else {
        true
      }
    } else {
      false
    }
  }
  /// Tries to parse a character, yielding its position.
  fn char_opt_pos(& mut self, char: char) -> Option<usize> {
    if let Some( (pos, c) ) = self.next() {
      if c != char {
        self.txen(pos, c) ;
        None
      } else {
        Some(pos)
      }
    } else {
      None
    }
  }
  /// Parses a character or fails.
  fn char(& mut self, char: char) -> Res<()> {
    if self.char_opt(char) { Ok(()) } else {
      bail!(
        self.error_here(
          format!("expected `{}`", conf.emph(& char.to_string()))
        )
      )
    }
  }

  /// Consumes characters until some character.
  fn eat_until(& mut self, char: char) {
    while let Some((_, c)) = self.next() {
      if c == char { break }
    }
  }

  /// Returns all the characters until some character.
  fn get_until(& mut self, char: char) -> String {
    let mut s = String::new() ;
    while let Some((_, c)) = self.next() {
      if c == char { break }
      s.push(c)
    }
    s
  }

  /// Parses a set-info.
  fn set_info(& mut self) -> Res<bool> {
    if ! self.tag_opt("set-info") {
      return Ok(false)
    }
    self.ws_cmt() ;
    self.char(':') ? ;
    let _ = self.ident() ? ;
    self.ws_cmt() ;
    if self.char_opt('"') {
      self.eat_until('"')
    } else if self.ident_opt().is_some() {
      ()
    }
    Ok(true)
  }

  /// Parses an echo.
  fn echo(& mut self) -> Res< Option<String> > {
    if ! self.tag_opt("echo") {
      return Ok(None)
    }
    self.ws_cmt() ;
    self.char('"') ? ;
    let blah = self.get_until('"') ;
    Ok( Some(blah) )
  }

  /// Parses a set-logic.
  fn set_logic(& mut self) -> Res<bool> {
    if ! self.tag_opt("set-logic") {
      return Ok(false)
    }
    self.ws_cmt() ;
    if ! self.tag_opt("HORN") {
      bail!( self.error_here("unknown logic: ") )
    }
    Ok(true)
  }

  /// Parses a type or fails.
  fn typ(& mut self) -> Res<Typ> {
    if let Some(typ) = self.typ_opt() {
      Ok(typ)
    } else {
      bail!( self.error_here("expected type") )
    }
  }
  /// Tries to parse a type.
  fn typ_opt(& mut self) -> Option<Typ> {
    if self.tag_opt("Int") {
      Some(Typ::Int)
    } else if self.tag_opt("Bool") {
      Some(Typ::Bool)
    } else {
      None
    }
  }

  /// Predicate declaration.
  fn pred_dec(& mut self, instance: & mut Instance) -> Res<bool> {
    if ! self.tag_opt("declare-fun") {
      return Ok(false)
    }
    self.ws_cmt() ;
    let (pos, ident) = self.ident() ? ;
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;

    let mut typs = Vec::with_capacity(11) ;
    while let Some(ty) = self.typ_opt() {
      typs.push(ty) ;
      self.ws_cmt()
    }
    typs.shrink_to_fit() ;

    self.char(')') ? ;
    self.ws_cmt() ;
    if ! self.tag_opt("Bool") {
      bail!(
        self.error_here("expected Bool type")
      )
    }

    let pred_index = instance.push_pred(
      ident.into(), VarMap::of(typs)
    ) ;
    let prev = self.cxt.pred_name_map.insert(ident.into(), pred_index) ;
    if let Some(prev) = prev {
      bail!(
        self.error(
          pos,
          format!(
            "predicate `{}` is already declared",
            conf.bad( & format!("{}", instance[prev]) )
          )
        )
      )
    }

    Ok(true)
  }

  /// Parses some arguments `( (<id> <ty>) ... )`.
  fn args(
    & mut self,
    var_map: & mut VarMap<VarInfo>, hash_map: & mut HashMap<& 's str, VarIdx>
  ) -> Res<()> {
    self.char('(') ? ;
    self.ws_cmt() ;
    while self.char_opt('(') {
      self.ws_cmt() ;
      let (pos, ident) = self.ident() ? ;
      self.ws_cmt() ;
      let typ = self.typ() ? ;
      self.ws_cmt() ;
      self.char(')') ? ;
      self.ws_cmt() ;
      let idx = var_map.next_index() ;
      let prev = hash_map.insert(ident, idx) ;
      if let Some(_) = prev {
        bail!(
          self.error(
            pos, format!(
              "found two qualifier variables named `{}`", conf.bad(ident)
            )
          )
        )
      }
      var_map.push( VarInfo::new(ident.into(), typ, idx) )
    }
    self.char(')') ? ;
    var_map.shrink_to_fit() ;
    hash_map.shrink_to_fit() ;
    Ok(())
  }

  /// Adds a binding to the current bindings.
  fn insert_bind(& mut self, var: & 's str, term: PTTerms) {
    if let Some(bindings) = self.bindings.last_mut() {
      bindings.insert(var, term) ;
    } else {
      panic!("bug, adding binding before pushing a binding scope")
    }
  }
  /// Pushes a binding scopes.
  fn push_bind(& mut self) {
    self.bindings.push( HashMap::with_capacity(17) )
  }
  /// Pops a binding scope.
  fn pop_bind(& mut self) {
    if self.bindings.pop().is_none() {
      panic!("bug, popping binding scope but there's no scope")
    }
  }
  /// Finds what a variable is mapped to.
  fn get_bind(& self, var: & str) -> Option< & PTTerms > {
    for bindings in & self.bindings {
      if let Some(tterms) = bindings.get(var) {
        return Some( tterms )
      }
    }
    None
  }


  /// Parses the end of some consecutive let-bindings.
  #[inline]
  fn close_let_bindings(& mut self, count: LetCount) -> Res<()> {
    for _ in 0..count.n {
      self.ws_cmt() ;
      self.char(')') ? ;
      self.pop_bind()
    }
    Ok(())
  }


  /// Line from a position.
  pub fn line_from(& self, pos: usize) -> & str {
    if pos >= self.string.len() {
      panic!("illegal position {}, length is {}", pos, self.string.len())
    }
    let mut end = pos ;
    for char in self.string[pos..].chars() {
      if char == '\n' {
        break
      } else { end += 1 }
    }
    & self.string[pos .. end]
  }




  /// Parses some consecutive let-bindings.
  ///
  /// - open paren,
  /// - `let` keyword, and
  /// - bindings.
  ///
  /// Returns the number of let-bindings it parsed, *i.e.* the number of
  /// corresponding closing parens.
  #[inline]
  fn let_bindings(
    & mut self, map: & HashMap<& 's str, VarIdx>, instance: & Instance
  ) -> Res<LetCount> {
    let mut n = 0 ;
    'parse_lets: loop {
      self.ws_cmt() ;
      if let Some((pos, c)) = self.next() {
        if c == '(' && {
          self.ws_cmt() ; self.tag_opt("let")
        } {
          self.push_bind() ;
          self.ws_cmt() ;
          self.char('(') ? ;
          while { self.ws_cmt() ; self.char_opt('(') } {
            self.ws_cmt() ;
            let (_, id) = self.ident() ? ;
            self.ws_cmt() ;
            let tterms = self.parse_ptterms(map, instance) ? ;
            self.insert_bind(id, tterms) ;
            self.ws_cmt() ;
            self.char(')') ?
          }
          self.ws_cmt() ;
          self.char(')') ? ;
          n += 1
        } else {
          break 'parse_lets
          self.txen(pos, c)
        }
      } else {
        break 'parse_lets
      }
    }
    Ok( LetCount { n } )
  }

  /// Bool parser.
  fn bool(& mut self) -> Option<bool> {
    if self.tag_opt("true") {
      Some(true)
    } else if self.tag_opt("false") {
      Some(false)
    } else {
      None
    }
  }

  /// Integer parser.
  fn int(& mut self) -> Option<Int> {
    if let Some((start_pos, char)) = self.next() {
      if char.is_numeric() {
        let mut end_pos = self.string.len() ;
        while let Some((pos, char)) = self.next() {
          if ! char.is_numeric() {
            self.txen(pos, char) ;
            end_pos = pos ;
            break
          }
        }
        Some(
          Int::parse_bytes(
            self.string[start_pos..end_pos].as_bytes(), 10
          ).expect("[bug] in integer parsing")
        )
      } else {
        self.txen(start_pos, char) ;
        None
      }
    } else {
      None
    }
  }

  /// Parses an operator or fails.
  fn op(& mut self) -> Res<Op> {
    if let Some(op) = self.op_opt() {
      Ok(op)
    } else {
      bail!( self.error_here("expected operator") )
    }
  }
  /// Tries to parse an operator.
  fn op_opt(& mut self) -> Option<Op> {
    match self.next() {
      Some( (pos_1, 'a') ) => if self.tag_opt("nd") {
        Some(Op::And)
      } else {
        self.txen(pos_1, 'a') ;
        None
      },
      Some( (pos_1, 'o') ) => if self.char_opt('r') {
        Some(Op::Or)
      } else {
        self.txen(pos_1, 'o') ;
        None
      },
      Some( (pos_1, 'n') ) => if self.tag_opt("ot") {
        Some(Op::Not)
      } else {
        self.txen(pos_1, 'n') ;
        None
      },
      Some( (pos_1, 'i') ) => if self.tag_opt("te") {
        Some(Op::Ite)
      } else {
        self.txen(pos_1, 'i') ;
        None
      },
      Some( (_, '=') ) => if self.char_opt('>') {
        Some(Op::Impl)
      } else {
        Some(Op::Eql)
      },
      Some( (_, '>') ) => if self.char_opt('=') {
        Some(Op::Ge)
      } else {
        Some(Op::Gt)
      },
      Some( (_, '<') ) => if self.char_opt('=') {
        Some(Op::Le)
      } else {
        Some(Op::Lt)
      },
      Some( (pos_1, 'm') ) => if self.tag_opt("od") {
        Some(Op::Mod)
      } else {
        self.txen(pos_1, 'm') ;
        None
      },
      Some( (pos_1, 'd') ) => if self.tag_opt("iv") {
        Some(Op::Div)
      } else {
        self.txen(pos_1, 'd') ;
        None
      },
      Some( (_, '+') ) => Some(Op::Add),
      Some( (_, '-') ) => Some(Op::Sub),
      Some( (_, '*') ) => Some(Op::Mul),
      // Some( (_, '/') ) => Some(Op::Div),
      Some( (pos, char) ) => {
        self.txen(pos, char) ;
        None
      },
      None => None,
    }
  }

  /// Parses a sequence of terms.
  fn term_seq(
    & mut self, map: & HashMap<& 's str, VarIdx>, instance: & Instance
  ) -> Res< Vec<Term> > {
    debug_assert!( self.cxt.term_stack.is_empty() ) ;
    let mut seq = Vec::with_capacity(11) ;

    'read_kids: loop {
      self.ws_cmt() ;
      let bind_count = self.let_bindings(map, instance) ? ;
      self.ws_cmt() ;
      let mut term = if self.char_opt('(') {
        self.ws_cmt() ;
        let op = self.op() ? ;
        let kids = Vec::with_capacity(11) ;
        self.cxt.term_stack.push( (op, kids, bind_count) ) ;
        continue 'read_kids
      } else if let Some(int) = self.int() {
        term::int(int)
      } else if let Some(b) = self.bool() {
        term::bool(b)
      } else if let Some((pos, id)) = self.ident_opt() {
        if let Some(idx) = map.get(id) {
          term::var(* idx)
        } else if let Some(ptterms) = self.get_bind(id) {
          ptterms.to_term() ?
        } else {
          bail!(
            self.error(
              pos, format!("unknown variable `{}`", conf.bad(id))
            )
          )
        }
      } else {
        if self.cxt.term_stack.is_empty() {
          self.close_let_bindings(bind_count) ? ;
          break 'read_kids
        } else {
          bail!( self.error_here("expected term") )
        }
      } ;

      'go_up: while let Some(
        (op, mut kids, bind_count)
      ) = self.cxt.term_stack.pop() {
        kids.push(term) ;
        self.ws_cmt() ;
        if self.char_opt(')') {
          term = term::app(op, kids) ;
          self.close_let_bindings(bind_count) ? ;
          continue 'go_up
        } else {
          self.cxt.term_stack.push( (op, kids, bind_count) ) ;
          continue 'read_kids
        }
      }

      seq.push(term)
    }
    debug_assert!( self.cxt.term_stack.is_empty() ) ;

    seq.shrink_to_fit() ;
    Ok(seq)
  }


  /// Parses a top term or fails.
  fn top_term(
    & mut self, map: & HashMap<& 's str, VarIdx>, instance: & Instance
  ) -> Res<PTTerms> {
    if let Some(term) = self.top_term_opt(map, instance) ? {
      Ok(term)
    } else {
      bail!( self.error_here("expected term") )
    }
  }
  /// Tries to parse a top term.
  fn top_term_opt(
    & mut self, map: & HashMap<& 's str, VarIdx>, instance: & Instance
  ) -> Res< Option< PTTerms > > {
    let bind_count = self.let_bindings(map, instance) ? ;
    let res = if self.char_opt('(') {
      self.ws_cmt() ;
      if let Some(op) = self.op_opt() {
        self.ws_cmt() ;
        let args = self.term_seq(map, instance) ? ;
        self.ws_cmt() ;
        self.char(')') ? ;
        Ok( Some(
          PTTerms::tterm( TTerm::T( term::app(op, args) ) )
        ) )
      } else if let Some((pos,ident)) = self.ident_opt() {
        self.ws_cmt() ;
        let args = self.term_seq(map, instance) ? ;
        self.ws_cmt() ;
        self.char(')') ? ;
        let pred = if let Some(idx) = self.cxt.pred_name_map.get(ident) {
          * idx
        } else {
          bail!(
            self.error(
              pos,
              format!("unknown predicate `{}`", conf.bad(ident))
            )
          )
        } ;
        if instance[pred].sig.len() != args.len() {
          bail!(
            self.error(
              pos, format!(
                "illegal application of predicate `{}` to {} arguments, \
                expected {} arguments",
                conf.bad(ident),
                conf.emph(& format!("{}", args.len())),
                conf.emph(& format!("{}", instance[pred].sig.len())),
              )
            )
          )
        }
        Ok( Some(
          PTTerms::tterm( TTerm::P { pred, args: args.into() } )
        ) )
      } else {
        bail!(
          self.error_here("expected operator or predicate")
        )
      }
    } else if let Some(b) = self.bool() {
      Ok( Some( PTTerms::tterm( TTerm::T( term::bool(b) ) ) ) )
    } else if let Some(int) = self.int() {
      Ok( Some( PTTerms::tterm( TTerm::T( term::int(int) ) ) ) )
    } else if let Some((pos,id)) = self.ident_opt() {
      if let Some(idx) = map.get(id) {
        Ok( Some( PTTerms::tterm( TTerm::T( term::var(* idx) ) ) ) )
      } else if let Some(tterms) = self.get_bind(id) {
        Ok( Some( tterms.clone() ) )
      } else {
        bail!(
          self.error(
            pos, format!("unknown variable `{}`", conf.bad(id))
          )
        )
      }
    } else {
      // In theory, we should check if the top term is an ident that's either a
      // quantified or bound variable. In practice, this is done at the level
      // above this one, in `parse_ptterms`.
      Ok(None)
    } ;
    self.close_let_bindings(bind_count) ? ;
    res
  }


  /// Parses a forall.
  fn forall(
    & mut self, instance: & mut Instance
  ) -> Res<bool> {
    if ! self.tag_opt("forall") {
      return Ok(false)
    }
    let (mut var_map, mut hash_map, mut parse_args, mut closing_parens) = (
      VarMap::with_capacity(11), HashMap::with_capacity(11), true, 0
    ) ;
    while parse_args {
      self.ws_cmt() ;
      self.args(& mut var_map, & mut hash_map) ? ;
      self.ws_cmt() ;
      parse_args = if let Some(pos) = self.char_opt_pos('(') {
        self.ws_cmt() ;
        if self.tag_opt("forall") {
          closing_parens += 1 ;
          true
        } else {
          self.txen(pos, '(') ;
          false
        }
      } else {
        false
      }
    }
    self.ws_cmt() ;
    let outter_bind_count = self.let_bindings(& hash_map, instance) ? ;
    self.ws_cmt() ;
    self.parse_clause(var_map, hash_map, instance, false) ? ;
    self.ws_cmt() ;
    self.close_let_bindings(outter_bind_count) ? ;
    for _ in 0..closing_parens {
      self.ws_cmt() ;
      self.char(')') ?
    }
    Ok(true)
  }


  /// Parses a negated exists.
  fn exists(& mut self, instance: & mut Instance) -> Res<bool> {
    if ! self.tag_opt("not") {
      return Ok(false)
    }
    self.ws_cmt() ;
    let outter_bind_count = self.let_bindings(& HashMap::new(), instance) ? ;
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;
    self.tag("exists") ? ;
    self.ws_cmt() ;
    let (mut var_map, mut hash_map, mut parse_args, mut closing_parens) = (
      VarMap::with_capacity(11), HashMap::with_capacity(11), true, 0
    ) ;
    while parse_args {
      self.ws_cmt() ;
      self.args(& mut var_map, & mut hash_map) ? ;
      self.ws_cmt() ;
      parse_args = if let Some(pos) = self.char_opt_pos('(') {
        self.ws_cmt() ;
        if self.tag_opt("exists") {
          closing_parens += 1 ;
          true
        } else {
          self.txen(pos, '(') ;
          false
        }
      } else {
        false
      }
    }
    self.ws_cmt() ;
    self.parse_clause(var_map, hash_map, instance, true) ? ;
    self.ws_cmt() ;
    self.char(')') ? ;
    self.ws_cmt() ;
    self.close_let_bindings(outter_bind_count) ? ;
    for _ in 0..closing_parens {
      self.ws_cmt() ;
      self.char(')') ?
    }
    Ok(true)
  }

  /// Adds a clause to an instance.
  fn add_clause(
    & self, instance: & mut Instance,
    var_map: VarMap<VarInfo>, lhs: Vec<TTerm>, rhs: TTerm
  ) -> Res<()> {
    let mut nu_lhs = Vec::with_capacity( lhs.len() ) ;
    let mut lhs_is_false = false ;
    for lhs in lhs {
      if ! lhs.is_true() {
        if lhs.is_false() {
          lhs_is_false = true ;
          break
        } else {
          nu_lhs.push(lhs)
        }
      }
    }
    if ! lhs_is_false {
      instance.push_clause(
        Clause::new(var_map.clone(), nu_lhs.clone(), rhs)
      ) ?
    }
    Ok(())
  }


  /// Parses an assert.
  fn assert(& mut self, instance: & mut Instance) -> Res<bool> {
    if ! self.tag_opt("assert") {
      return Ok(false)
    }
    self.ws_cmt() ;
    let bind_count = self.let_bindings(& HashMap::new(), instance) ? ;
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;

    if self.forall(instance) ? {
      ()
    } else if self.exists(instance) ? {
      ()
    } else {
      bail!(
        self.error_here("expected forall or negated exists")
      )
    } ;
    self.ws_cmt() ;
    self.char(')') ? ;

    self.close_let_bindings(bind_count) ? ;

    Ok(true)
  }

  /// Parses a check-sat.
  fn check_sat(& mut self) -> bool {
    if self.tag_opt("check-sat") {
      true
    } else {
      false
    }
  }

  /// Parses a get-model.
  fn get_model(& mut self) -> bool {
    if self.tag_opt("get-model") {
      true
    } else {
      false
    }
  }

  /// Parses an exit command.
  fn exit(& mut self) -> bool {
    if self.tag_opt("exit") {
      true
    } else {
      false
    }
  }

  /// Parses an reset command.
  fn reset(& mut self) -> bool {
    if self.tag_opt("reset") {
      true
    } else {
      false
    }
  }

  /// Parses items, returns true if it found a check-sat.
  pub fn parse(
    mut self, instance: & mut Instance
  ) -> Res<Parsed> {
    self.ws_cmt() ;
    let mut res = Parsed::Eof ;
    self.cxt.term_stack.clear() ;

    while self.has_next() {
      self.char('(') ? ;
      self.ws_cmt() ;

      res = if self.set_info() ? {
        Parsed::Items
      } else if self.set_logic() ? {
        Parsed::Items
      } else if self.pred_dec(instance) ? {
        Parsed::Items
      } else if self.assert(instance) ? {
        Parsed::Items
      } else if self.check_sat() {
        Parsed::CheckSat
      } else if self.get_model() {
        Parsed::GetModel
      } else if self.exit() {
        Parsed::Exit
      } else if self.reset() {
        Parsed::Reset
      } else if let Some(blah) = self.echo() ? {
        println!("{}", blah) ;
        Parsed::Items
      } else {
        bail!(
          self.error_here("expected top-level item")
        )
      } ;

      self.ws_cmt() ;
      self.char(')') ? ;
      self.ws_cmt() ;

      debug_assert!( self.cxt.term_stack.is_empty() ) ;
      debug_assert!( self.cxt.buff.is_empty() ) ;
      debug_assert!( self.cxt.mem.is_empty() ) ;
      debug_assert!( self.chars.next().is_none() ) ;

      if res != Parsed::Items {
        return Ok(res)
      }
    }

    debug_assert!( self.cxt.term_stack.is_empty() ) ;
    debug_assert!( self.cxt.buff.is_empty() ) ;
    debug_assert!( self.cxt.mem.is_empty() ) ;
    debug_assert!( self.chars.next().is_none() ) ;

    Ok(res)
  }


  fn parse_clause(
    & mut self,
    var_map: VarMap<VarInfo>,
    map: HashMap<& 's str, VarIdx>,
    instance: & mut Instance,
    negated: bool,
  ) -> Res<()> {
    let mut ptterms = self.parse_ptterms(& map, instance) ? ;
    if negated {
      ptterms = PTTerms::not(ptterms) ?
    }
    // ptterms.print("> ") ;
    let mut clauses = ptterms.to_clauses()?.into_iter() ;
    if let Some((last_lhs, last_rhs)) = clauses.next() {
      for (lhs, rhs) in clauses {
        self.add_clause(instance, var_map.clone(), lhs, rhs) ?
      }
      self.add_clause(instance, var_map.clone(), last_lhs, last_rhs) ?
    }
    Ok(())
  }


  fn parse_ptterms(
    & mut self, map: & HashMap<& 's str, VarIdx>, instance: & Instance
  ) -> Res<PTTerms> {
    enum Frame {
      And(Vec<PTTerms>), Or(Vec<PTTerms>), Impl(Vec<PTTerms>),
      Not, Let(LetCount)
    }
    let mut stack: Vec<Frame> = vec![] ;

    'go_down: loop {
      self.ws_cmt() ;

      let bind_count = self.let_bindings(& map, instance) ? ;
      if ! bind_count.is_zero() {
        stack.push( Frame::Let(bind_count) ) ;
        self.ws_cmt()
      }

      let mut ptterm = if let Some(pos) = self.char_opt_pos('(') {
        self.ws_cmt() ;

        if self.tag_opt("and") {
          self.ws_cmt() ;
          stack.push( Frame::And(vec![]) ) ;
          continue 'go_down
        } else if self.tag_opt("or") {
          self.ws_cmt() ;
          stack.push( Frame::Or(vec![]) ) ;
          continue 'go_down
        } else if self.tag_opt("not") {
          stack.push( Frame::Not ) ;
          continue 'go_down
        } else if self.tag_opt("=>") {
          stack.push( Frame::Impl(vec![]) ) ;
          continue 'go_down
        } else {
          self.txen(pos, '(') ;
          self.top_term(& map, instance) ?
        }

      } else {
        self.top_term(& map, instance) ?
      } ;

      'go_up: loop {
        self.ws_cmt() ;
        match stack.pop() {
          Some( Frame::And(mut args) ) => {
            args.push(ptterm) ;
            if self.char_opt(')') {
              ptterm = PTTerms::and(args) ;
              continue 'go_up
            } else {
              stack.push( Frame::And(args) ) ;
              continue 'go_down
            }
          },
          Some( Frame::Or(mut args) ) => {
            args.push(ptterm) ;
            if self.char_opt(')') {
              ptterm = PTTerms::or(args) ;
              continue 'go_up
            } else {
              stack.push( Frame::Or(args) ) ;
              continue 'go_down
            }
          },
          Some( Frame::Impl(mut args) ) => {
            args.push(ptterm) ;
            if self.char_opt(')') {
              if args.len() != 2 {
                bail!(
                  "unexpected implication over {} (!= 2) arguments", args.len()
                )
              }
              let (rhs, lhs) = (args.pop().unwrap(), args.pop().unwrap()) ;
              ptterm = PTTerms::or( vec![ PTTerms::not(lhs) ?, rhs ] ) ;
              continue 'go_up
            } else {
              stack.push( Frame::Impl(args) ) ;
              continue 'go_down
            }
          },
          Some( Frame::Not ) => {
            ptterm = PTTerms::not(ptterm) ? ;
            self.char(')') ? ;
            continue 'go_up
          },
          Some( Frame::Let(bind_count) ) => {
            self.close_let_bindings(bind_count) ? ;
            continue 'go_up
          },
          None => break 'go_down Ok(ptterm),
        }
      }

    }
  }
}





/// Boolean combination of top terms used by the parser.
#[derive(Clone)]
pub enum PTTerms {
  And( Vec<PTTerms> ),
  Or( Vec<PTTerms> ),
  NTTerm( TTerm ),
  TTerm( TTerm ),
}
impl PTTerms {
  pub fn and(mut tterms: Vec<PTTerms>) -> Self {
    use std::iter::Extend ;
    debug_assert!( ! tterms.is_empty() ) ;
    let mut nu_tterms = Vec::with_capacity(17) ;
    let mut cnt = 0 ;
    while cnt < tterms.len() {
      if let PTTerms::And(_) = tterms[cnt] {
        let and = tterms.swap_remove(cnt) ;
        if let PTTerms::And(tts) = and {
          nu_tterms.extend(tts)
        } else {
          unreachable!()
        }
      } else {
        cnt += 1
      }
    }
    tterms.extend( nu_tterms ) ;
    if tterms.len() == 1 {
      tterms.pop().unwrap()
    } else {
      PTTerms::And(tterms)
    }
  }

  pub fn or(mut tterms: Vec<PTTerms>) -> Self {
    use std::iter::Extend ;
    debug_assert!( ! tterms.is_empty() ) ;
    let mut nu_tterms = Vec::with_capacity(17) ;
    let mut cnt = 0 ;
    while cnt < tterms.len() {
      if let PTTerms::Or(_) = tterms[cnt] {
        let or = tterms.swap_remove(cnt) ;
        if let PTTerms::Or(tts) = or {
          nu_tterms.extend(tts)
        } else {
          unreachable!()
        }
      } else {
        cnt += 1
      }
    }
    tterms.extend( nu_tterms ) ;
    if tterms.len() == 1 {
      tterms.pop().unwrap()
    } else {
      PTTerms::Or(tterms)
    }
  }

  pub fn not(mut tterms: PTTerms) -> Res<Self> {
    enum Frame {
      And( Vec<PTTerms>, Vec<PTTerms> ),
      Or( Vec<PTTerms>, Vec<PTTerms> ),
    }
    let mut stack: Vec<Frame> = vec![] ;

    'go_down: loop {

      tterms = match tterms {
        PTTerms::And(mut args) => if let Some(first) = args.pop() {
          tterms = first ;
          args.reverse() ;
          let done = Vec::with_capacity( args.len() + 1 ) ;
          stack.push( Frame::Or(args, done) ) ;
          continue 'go_down
        } else {
          bail!("nullary conjunction")
        },

        PTTerms::Or(mut args) => if let Some(first) = args.pop() {
          tterms = first ;
          args.reverse() ;
          let done = Vec::with_capacity( args.len() + 1 ) ;
          stack.push( Frame::And(args, done) ) ;
          continue 'go_down
        } else {
          bail!("nullary disjunction")
        },

        PTTerms::NTTerm(tt) => PTTerms::TTerm(tt),

        PTTerms::TTerm(tt) => PTTerms::NTTerm(tt),

      } ;

      'go_up: loop {
        match stack.pop() {
          Some( Frame::And(mut to_do, mut done) ) => {
            done.push(tterms) ;
            if let Some(tt) = to_do.pop() {
              stack.push( Frame::And(to_do, done) ) ;
              tterms = tt ;
              continue 'go_down
            } else {
              tterms = Self::and(done) ;
              continue 'go_up
            }
          },
          Some( Frame::Or(mut to_do, mut done) ) => {
            done.push(tterms) ;
            if let Some(tt) = to_do.pop() {
              stack.push( Frame::Or(to_do, done) ) ;
              tterms = tt ;
              continue 'go_down
            } else {
              tterms = Self::or(done) ;
              continue 'go_up
            }
          },
          None => break 'go_down Ok(tterms)
        }
      }

    }
  }

  pub fn tterm(tterm: TTerm) -> Self {
    PTTerms::TTerm( tterm )
  }

  pub fn to_clauses(self) -> Res< Vec< (Vec<TTerm>, TTerm) > > {
    match self {
      PTTerms::TTerm(tterm) => Ok(
        vec![ (vec![], tterm) ]
      ),
      PTTerms::NTTerm(tterm) => Ok(
        vec![ (vec![ tterm ], TTerm::fls()) ]
      ),

      PTTerms::Or(ptterms) => {
        let mut lhs = Vec::with_capacity( ptterms.len() ) ;
        let mut rhs = None ;

        for ptt in ptterms {
          match ptt {
            PTTerms::TTerm(tt) => if let TTerm::T(term) = tt {
              lhs.push( TTerm::T( term::not(term) ) )
            } else if rhs.is_none() {
              rhs = Some( vec![ tt ] )
            } else {
              bail!("ill-formed horn clause (or, 1)")
            },

            PTTerms::NTTerm(tt) => lhs.push(tt),

            PTTerms::And(ptts) => {
              let mut tts = Vec::with_capacity( ptts.len() ) ;
              for ptt in ptts {
                match ptt {
                  PTTerms::TTerm(tterm) => tts.push(tterm),
                  PTTerms::NTTerm(tterm) => if let TTerm::T(term) = tterm {
                    tts.push( TTerm::T(term::not(term)) )
                  } else {
                    bail!("ill-formed horn clause (or, 2)")
                  },
                  _ => bail!("ill-formed horn clause (or, 3)"),
                }
              }
              rhs = Some(tts)
            },

            _ => bail!("ecountered normalization issue (or, 4)"),
          }
        }

        if let Some(rhs) = rhs {
          let mut res = Vec::with_capacity( rhs.len() ) ;
          let mut rhs = rhs.into_iter() ;
          if let Some(last) = rhs.next() {
            for rhs in rhs {
              res.push( (lhs.clone(), rhs) )
            }
            res.push((lhs, last))
          }
          Ok(res)
        } else {
          Ok( vec![ (lhs, TTerm::fls()) ] )
        }
      },

      PTTerms::And(ppterms) => {
        let mut clauses = Vec::with_capacity(ppterms.len()) ;
        for ppt in ppterms {
          clauses.extend( ppt.to_clauses() ? )
          //              ^^^^^^^^^^^^^^^^
          // This is a recursive call, but there can be no other rec call
          // inside it because
          //
          // - there can be no `PTTerms::And` inside a `PTTerms::And` by
          //   construction
          // - this is the only place `to_clauses` calls itself.
        }
        Ok(clauses)
      },

    }
  }

  /// Transforms a parser's combination of top terms into a term, if possible.
  pub fn to_term(& self) -> Res<Term> {
    let mut stack = Vec::with_capacity(17) ;

    let mut ptterm = self ;

    'go_down: loop {

      let mut term = match * ptterm {
        PTTerms::And(ref args) => {
          let mut args = args.iter() ;
          if let Some(head) = args.next() {
            stack.push((Op::And, args, vec![])) ;
            ptterm = head ;
            continue 'go_down
          } else {
            bail!("illegal nullary conjunction")
          }
        },
        PTTerms::Or(ref args) => {
          let mut args = args.iter() ;
          if let Some(head) = args.next() {
            stack.push((Op::Or, args, vec![])) ;
            ptterm = head ;
            continue 'go_down
          } else {
            bail!("illegal nullary conjunction")
          }
        },
        PTTerms::TTerm(ref tterm) => if let Some(term) = tterm.term() {
          term.clone()
        } else {
          bail!("failed to convert `PTTerms` to `Term` (1)")
        },
        PTTerms::NTTerm(ref tterm) => if let Some(term) = tterm.term() {
          term::not( term.clone() )
        } else {
          bail!("failed to convert `PTTerms` to `Term` (2)")
        },
      } ;

      'go_up: loop {
        if let Some((op, mut to_do, done)) = stack.pop() {
          if let Some(next) = to_do.next() {
            stack.push( (op, to_do, done) ) ;
            ptterm = next ;
            continue 'go_down
          } else {
            term = term::app(op, done) ;
            continue 'go_up
          }
        } else {
          break 'go_down Ok(term)
        }
      }

    }
  }

  pub fn print(& self, pref: & str) {
    match * self {
      PTTerms::And(ref args) => {
        println!("{}(and", pref) ;
        for arg in args {
          arg.print(& format!("{}  ", pref))
        }
        println!("{})", pref)
      },
      PTTerms::Or(ref args) => {
        println!("{}(or", pref) ;
        for arg in args {
          arg.print(& format!("{}  ", pref))
        }
        println!("{})", pref)
      },
      PTTerms::NTTerm(ref arg) => println!(
        "{}(not {})", pref, arg
      ),
      PTTerms::TTerm(ref tt) => {
        println!("{}{}", pref, tt)
      },
    }
  }
}
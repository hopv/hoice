//! Instance builder.
//!
//! # TODO
//!
//! - investigate further the `unused variable` warnings in the parsers
//!
#![allow(unused_variables)]

use nom::multispace ;

use common::* ;
use instance::* ;

/// Returns the data in an error if it's an error.
macro_rules! erreturn {
  ($e:expr) => (
    match $e {
      Ok(something) => something,
      Err(e) => return e,
    }
  ) ;
}


lazy_static!{
  #[doc = "
    Regex identifying the token to highlight when reconstructing a parse error.
  "]
  static ref token_regex: ::regex::Regex = ::regex::Regex::new(
    r"^(?P<token> |\t|\n|\r|\(|\)|[^( |\t\(\)]*)(?P<tail>.*)$"
  ).expect("problem in `token_regex`") ;
}

/// Parse error alias type.
#[derive(Debug)]
pub struct InternalParseError {
  /// Error message.
  pub msg: String,
  /// Position of the error from **the end** of the byte slice.
  pub from_end: usize,
}
impl InternalParseError {
  /// Constructor.
  pub fn mk(msg: String, from_end: usize) -> Self {
    InternalParseError { msg, from_end }
  }

  /// Turns a parse error in a regular error.
  ///
  /// The weird `line` argument works as follows: if it is
  ///
  /// - `None`, then the data generated will have no line info (useful when
  ///   reading from `stdin`) ;
  /// - `Some(off)`, then the data will have a line info which is the line 
  ///   where the error token appears in `input` plus `off` (useful when
  ///   reading a file incrementally to add an offset to error messages). 
  ///
  pub fn to_error(self, input: & [u8], line: Option<usize>) -> Error {
    let (msg, from_end) = (self.msg, self.from_end) ;

    let nl_u8s = {
      let mut set = HashSet::new() ;
      let bytes = "\n".as_bytes() ;
      assert_eq!(bytes.len(), 1) ;
      let _ = set.insert(bytes[0]) ;
      let bytes = "\r".as_bytes() ;
      assert_eq!(bytes.len(), 1) ;
      let _ = set.insert(bytes[0]) ;
      set
    } ;

    assert!( from_end <= input.len() ) ;
    let position = input.len() - from_end ;


    // Find next newline backwards.
    let line_start = match position {
      0 => 0,
      mut cnt => if nl_u8s.contains(& input[cnt]) { cnt } else {
        while cnt > 0 {
          if nl_u8s.contains(& input[cnt - 1]) { break } else {
            cnt -= 1
          }
        }
        cnt
      },
    } ;

    let line = if let Some(line) = line {
      let mut cnt = 1 + line ;
      for byte in & input[0..line_start] {
        if nl_u8s.contains(byte) { cnt += 1 }
      }
      Some(cnt)
    } else {
      None
    } ;

    // Find next newline forwards.
    let line_end = if position == input.len() { position } else {
      let mut cnt = position ;
      while cnt < input.len() {
        if nl_u8s.contains(& input[cnt]) { break } else { cnt += 1 }
      }
      cnt
    } ;

    let pref = erreturn!(
      ::std::str::from_utf8(
        & input[line_start..position]
      ).chain_err(
        || format!("utf8 conversion error while reconstructing parse error")
      ).chain_err(
        || msg.clone()
      )
    ).into() ;

    let line_tail = erreturn!(
      ::std::str::from_utf8(
        & input[position..line_end]
      ).chain_err(
        || format!("utf8 conversion error while reconstructing parse error")
      ).chain_err(
        || msg.clone()
      )
    ) ;

    let (token, suff) = if let Some(caps) = token_regex.captures(
      & line_tail
    ) {
      (caps["token"].to_string(), caps["tail"].to_string())
    } else {
      (line_tail.to_string(), "".to_string())
    } ;

    ErrorKind::ParseError(
      ParseErrorData { msg, pref, token, suff, line }
    ).into()
  }
}
impl<'a, S: Into<String>> From< (S, & 'a [u8] ) > for InternalParseError {
  fn from((msg, bytes): (S, & 'a [u8])) -> Self {
    InternalParseError::mk(msg.into(), bytes.len())
  }
}
impl<'a, S: Into<String>> From< (S, usize ) > for InternalParseError {
  fn from((msg, from_end): (S, usize)) -> Self {
    InternalParseError::mk(msg.into(), from_end)
  }
}


/// Instance builder.
pub struct InstBuild<'a> {
  /// The instance under construction.
  instance: Instance,
  /// Profiler.
  _profiler: Profile,
  /// Term stack to avoid recursion.
  term_stack: Vec< (Op, Vec<Term>) >,
  /// Characters being read.
  chars: ::std::str::CharIndices<'a>,
  /// Text being parsed.
  string: & 'a str,
  /// Buffer used when backtracking.
  buff: Vec<(usize, char)>,
  /// Memory when parsing tags.
  mem: Vec<(usize, char)>,
  /// Map from predicate names to predicate indices.
  new_pred_name_map: HashMap<& 'a str, PrdIdx>,
}
impl<'a> InstBuild<'a> {
  /// Creates an instance builder.
  pub fn mk(string: & 'a str) -> Self {
    InstBuild {
      instance: Instance::mk(300, 42, 42),
      _profiler: Profile::mk(),
      term_stack: Vec::with_capacity(17),
      chars: string.char_indices(),
      string,
      buff: Vec::with_capacity(17),
      mem: Vec::with_capacity(17),
      new_pred_name_map: HashMap::with_capacity(42),
    }
  }

  /// Detects predicates that can only be tautologies given the clauses.
  ///
  /// Returns the number of tautologies detected.
  pub fn simplify_tautologies(& mut self) -> Res<usize> {
    // Look for trivial predicates: those appearing in clauses of the form
    // `true => P(v_1, v_2, ...)` where all `v_i`s are different.
    let mut res = 0 ;
    let mut cls_idx = ClsIdx::zero() ;
    'trivial_preds: while cls_idx < self.instance.clauses().next_index() {
      let maybe_pred = if self.instance.clauses()[cls_idx].lhs().is_empty() {
        if let TTerm::P {
          pred, ref args
        } = * self.instance.clauses()[cls_idx].rhs() {
          // rhs is a predicate application...
          let mut vars = VarSet::with_capacity(args.len()) ;
          let mut okay = true ;
          for term in args {
            let arg_okay = if let Some(idx) = term.var_idx() {
              let is_new = vars.insert(idx) ;
              is_new
            } else {
              // Not a variable.
              false
            } ;
            okay = okay && arg_okay
          }
          if okay {
            Some(pred)
          } else {
            None
          }
        } else { None }
      } else { None } ;
      if let Some(pred) = maybe_pred {
        res += 1 ;
        let term = self.instance.bool(true) ;
        log_info!{
          "trivial predicate {}: forcing to {}", self.instance[pred], term
        }
        self.instance.force_pred(pred, term) ? ;
        let _clause = self.instance.forget_clause(cls_idx) ;
        log_info!{
          "dropped associated clause {}",
          _clause.string_do( & self.instance.preds, |s| s.to_string() ) ?
        }
      } else {
        cls_idx.inc()
      }
    }
    Ok(res)
  }


  /// Goes through the clauses and replaces forced predicates with their term.
  ///
  /// Returns the number of propagations: predicates replaced + clauses
  /// dropped.
  ///
  /// Only works with predicates that are `true` for now.
  pub fn propagate_forced(& mut self) -> Res<usize> {
    let mut res = 0 ;
    let mut cls_idx = ClsIdx::zero() ;

    'clause_iter: while cls_idx < self.instance.clauses().next_index() {

      // If `rhs` is true, remove clause.
      if let TTerm::P { pred, .. }  = self.instance.clauses[cls_idx].rhs {
        match self.instance.preds_term[pred].as_ref().map(
          |t| t.is_true()
        ) {
          Some(true) => {
            res += 1 ;
            let _clause = self.instance.forget_clause(cls_idx) ;
            log_info!{
              "dropping clause {}, rhs is true",
              _clause.string_do( & self.instance.preds, |s| s.to_string() ) ?
            }
            continue 'clause_iter
          },
          Some(false) => bail!(
            "progation for terms that are not `true` is not implemented"
          ),
          _ => (),
        }
      }

      let clause = & mut self.instance.clauses[cls_idx] ;
      let mut cnt = 0 ;
      'lhs_iter: while cnt < clause.lhs.len() {
        if let TTerm::P { pred, .. } = clause.lhs[cnt] {
          match self.instance.preds_term[pred].as_ref().map(
            |t| t.is_true()
          ) {
            Some(true) => {
              let _ = clause.lhs.swap_remove(cnt) ;
              res += 1 ;
              continue 'lhs_iter
            },
            Some(false) => bail!(
              "progation for terms that are not `true` is not implemented"
            ),
            None => (),
          }
        }
        cnt += 1
      }

      cls_idx.inc()
    }

    Ok(res)
  }

  /// Destructs the builder and yields the instance.
  ///
  /// The weird `line` argument works as follows: if it is
  ///
  /// - `None`, then the data generated will have no line info (useful when
  ///   reading from `stdin`) ;
  /// - `Some(off)`, then the data will have a line info which is the line 
  ///   where the error token appears in `input` plus `off` (useful when
  ///   reading a file incrementally to add an offset to error messages). 
  pub fn to_instance(
    mut self // , input: & [u8], line: Option<usize>
  ) -> Res<Instance> {
    'simplify: loop {
      let _tautologies = self.simplify_tautologies() ? ;
      log_info!{ "{} predicates found to be tautologies", _tautologies }
      let propagations = self.propagate_forced() ? ;
      if propagations == 0 {
        log_info!{ "done simplifying\n" }
        break 'simplify
      } else {
        log_info!{ "{} propagations\n", propagations }
      }
    }

    // if self.errors.is_empty() {
      self.instance.shrink_to_fit() ;
      Ok(self.instance)
    // } else {
    //   Err( self.to_error(input, line) )
    // }
  }

  /// Predicate accessor.
  pub fn preds(& self) -> & PrdMap<PrdInfo> {
    self.instance.preds()
  }
  /// Clause accessor.
  pub fn clauses(& self) -> & ClsMap<Clause> {
    self.instance.clauses()
  }



  // /// Reduces the instance.
  // pub fn reduce(& mut self) -> Res<()> {
  //   Ok(())
  // }


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
    let mut line_count = 0 ;
    let (mut pref, mut token, mut suff) = (
      "".to_string(), "<eof>".to_string(), "".to_string()
    ) ;
    for line in self.string.lines() {
      line_count += 1 ;
      if char_pos <= line.len() {
        pref = line[0..char_pos].to_string() ;
        token = if char_pos < line.len() {
          line[char_pos..char_pos].to_string()
        } else {
          ".".into()
        } ;
        suff = if char_pos + 1 < line.len() {
          line[(char_pos + 1)..].to_string()
        } else {
          "".into()
        } ;
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
    if ! self.buff.is_empty() { true } else {
      if let Some(next) = self.chars.next() {
        self.buff.push(next) ;
        true
      } else {
        false
      }
    }
  }
  /// The next character.
  fn next(& mut self) -> Option<(usize, char)> {
    if let Some(res) = self.buff.pop() {
      Some(res)
    } else {
      self.chars.next()
    }
  }
  /// Opposite of `next`, pushes a character back.
  fn txen(& mut self, pos: usize, c: char) {
    self.buff.push( (pos, c) )
  }

  /// Pushes something on the memory.
  fn mem(& mut self, pos: usize, char: char) {
    self.mem.push((pos, char))
  }

  /// Backtracks whatever's in the memory.
  fn backtrack_mem(& mut self) {
    self.mem.reverse() ;
    for elem in self.mem.drain(0..) {
      self.buff.push(elem)
    }
  }
  /// Clears the memory.
  fn clear_mem(& mut self) {
    self.mem.clear()
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
  fn ident(& mut self) -> Res<(usize, & 'a str)> {
    if let Some(id) = self.ident_opt() {
      Ok(id)
    } else {
      bail!(
        self.error_here("expected an identifier")
      )
    }
  }
  /// Tries to parse an ident.
  fn ident_opt(& mut self) -> Option<(usize, & 'a str)> {
    if let Some( (start_pos, char) ) = self.next() {
      if char == '|' {
        'quoted: while let Some((pos, char)) = self.next() {
          if char == '|' {
            return Some( (start_pos, & self.string[start_pos..(pos + 1)]) )
          }
        }
        panic!("expected '|', found eof")
      } else if char.is_alphabetic() {
        let mut end_pos = self.string.len() ;
        'unquoted: while let Some((pos, char)) = self.next() {
          if char.is_alphanumeric() {
            ()
          } else {
            match char {
              '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' |
              '=' | '<' | '>' | '.' | '?' | '/' => (),
              _ => {
                self.txen(pos, char) ;
                end_pos = pos ;
                break
              },
            }
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

  /// The next token, used for errors.
  fn next_token(& mut self) -> (usize, String) {
    if let Some( (pos, token) ) = self.ident_opt() {
      (pos, token.into())
    } else {
      self.next().map(
        |(pos, c)| if c == '\n' {
          (pos, "<new line>".to_string())
        } else {
          (pos, c.to_string())
        }
      ).unwrap_or( (self.string.len(), "eof".to_string()) )
    }
  }

  // /// Fails at the current position.
  // fn fail<S: AsRef<str>>(& mut self, blah: S) -> ErrorKind {
  //   let (pos, token) = self.next_token() ;
  //   ErrorKind::Msg(
  //     format!("parse error at {}: {} `{}`", pos, blah.as_ref(), token)
  //   )
  // }

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
  /// Parses a character or fails.
  fn char(& mut self, char: char) -> Res<()> {
    if self.char_opt(char) { Ok(()) } else {
      let (pos, token) = self.next_token() ;
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
    }
    Ok(true)
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
  fn pred_dec(& mut self) -> Res<bool> {
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

    let pred_index = self.instance.push_pred(
      ident.into(), VarMap::of(typs)
    ) ;
    let prev = self.new_pred_name_map.insert(ident, pred_index) ;
    if let Some(prev) = prev {
      bail!(
        self.error(
          pos,
          format!(
            "predicate `{}` is already declared",
            conf.bad( & format!("{}", self.instance[prev]) )
          )
        )
      )
    }

    Ok(true)
  }

  /// Parses some arguments `( (<id> <ty>) ... )`.
  fn args(& mut self) -> Res<
    (VarMap<VarInfo>, HashMap<& 'a str, VarIdx>)
  > {
    let (mut var_map, mut hash_map) = (
      VarMap::with_capacity(11), HashMap::with_capacity(11)
    ) ;
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
      var_map.push( VarInfo { name: ident.into(), typ, idx } )
    }
    self.char(')') ? ;
    var_map.shrink() ;
    hash_map.shrink_to_fit() ;
    Ok((var_map, hash_map))
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
      Some( (pos_1, '=') ) => if self.char_opt('>') {
        Some(Op::Impl)
      } else {
        Some(Op::Eql)
      },
      Some( (pos_1, '>') ) => if self.char_opt('=') {
        Some(Op::Ge)
      } else {
        Some(Op::Gt)
      },
      Some( (pos_1, '<') ) => if self.char_opt('=') {
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
      Some( (pos_1, '+') ) => Some(Op::Add),
      Some( (pos_1, '-') ) => Some(Op::Sub),
      Some( (pos_1, '*') ) => Some(Op::Mul),
      Some( (pos_1, '/') ) => Some(Op::Div),
      Some( (pos, char) ) => {
        self.txen(pos, char) ;
        None
      },
      None => None,
    }
  }

  /// Parses a sequence of terms.
  fn term_seq(
    & mut self, map: & HashMap<& 'a str, VarIdx>
  ) -> Res< Vec<Term> > {
    debug_assert!( self.term_stack.is_empty() ) ;
    let mut seq = Vec::with_capacity(11) ;

    'read_kids: loop {
      self.ws_cmt() ;
      let mut term = if self.char_opt('(') {
        self.ws_cmt() ;
        let op = self.op() ? ;
        let kids = Vec::with_capacity(11) ;
        self.term_stack.push( (op, kids) ) ;
        continue 'read_kids
      } else if let Some(int) = self.int() {
        self.instance.int(int)
      } else if let Some(b) = self.bool() {
        self.instance.bool(b)
      } else if let Some((pos, id)) = self.ident_opt() {
        if let Some(idx) = map.get(id) {
          self.instance.var(* idx)
        } else {
          bail!(
            self.error(
              pos, format!("unknown variable `{}`", conf.bad(id))
            )
          )
        }
      } else {
        if self.term_stack.is_empty() {
          break 'read_kids
        } else {
          bail!( self.error_here("expected term") )
        }
      } ;

      'go_up: while let Some(
        (op, mut kids)
      ) = self.term_stack.pop() {
        kids.push(term) ;
        self.ws_cmt() ;
        if self.char_opt(')') {
          term = self.instance.op(op, kids) ;
          continue 'go_up
        } else {
          self.term_stack.push( (op, kids) ) ;
          continue 'read_kids
        }
      }

      seq.push(term)
    }
    debug_assert!( self.term_stack.is_empty() ) ;

    seq.shrink_to_fit() ;
    Ok(seq)
  }


  /// Parses a top term or fails.
  fn top_term(& mut self, map: & HashMap<& 'a str, VarIdx>) -> Res<TTerm> {
    if let Some(term) = self.top_term_opt(map) ? {
      Ok(term)
    } else {
      bail!( self.error_here("expected term") )
    }
  }
  /// Tries to parse a term.
  fn top_term_opt(
    & mut self, map: & HashMap<& 'a str, VarIdx>
  ) -> Res< Option<TTerm> > {
    let res = if self.char_opt('(') {
      self.ws_cmt() ;
      if let Some(op) = self.op_opt() {
        self.ws_cmt() ;
        let args = self.term_seq(map) ? ;
        self.ws_cmt() ;
        self.char(')') ? ;
        Ok( Some(
          TTerm::T( self.instance.op(op, args) )
        ) )
      } else if let Some((pos,ident)) = self.ident_opt() {
        self.ws_cmt() ;
        let args = self.term_seq(map) ? ;
        self.ws_cmt() ;
        self.char(')') ? ;
        let pred = if let Some(idx) = self.new_pred_name_map.get(ident) {
          * idx
        } else {
          bail!(
            self.error(
              pos,
              format!("unknown predicate `{}`", conf.bad(ident))
            )
          )
        } ;
        Ok( Some(
          TTerm::P { pred, args: args.into() }
        ) )
      } else {
        bail!(
          self.error_here("expected operator or predicate")
        )
      }
    } else if let Some(b) = self.bool() {
      Ok( Some( TTerm::T( self.instance.bool(b) ) ) )
    } else if let Some(int) = self.int() {
      Ok( Some( TTerm::T( self.instance.int(int) ) ) )
    } else if let Some((pos,id)) = self.ident_opt() {
      if let Some(idx) = map.get(id) {
        Ok( Some( TTerm::T( self.instance.var(* idx) ) ) )
      } else {
        bail!(
          self.error(
            pos, format!("unknown variable `{}`", conf.bad(id))
          )
        )
      }
    } else {
      Ok(None)
    } ;
    res
  }


  // /// Tries parsing a top term.
  // fn top_term(
  //   & mut self, var_map: & HashMap<& 'a str, VarIdx>
  // ) -> Res< Option<TTerm> > {
  //   if Some( (pos, ') self.char_opt('(') {
  //     let (pos, ident) = if let Some(res) = self.ident_opt() { res } else {
  //       bail!(
  //         self.fail("expected operator or identifier")
  //       )
  //     } ;
  //     let pred = if let Some(idx) = self.new_pred_name_map.get(ident) {
  //       * idx
  //     } else {
  //       bail!(//         "unknown predicate `{}`", pos, conf.bad(ident) //       )
  //     } ;
  //     self.ws_cmt() ;
  //     let mut args = VarMap::with_capacity(11) ;
  //     while let Some(term) = self.term_opt(var_map) ? {
  //       args.push(term) ;
  //       self.ws_cmt()
  //     }
  //     self.char(')') ? ;
  //     args.shrink() ;
  //     Ok( Some( TTerm::P { pred, args } ) )
  //   } else if let Some(term) = self.term_opt(var_map) ? {
  //     Ok( Some( TTerm::T(term) ) )
  //   } else {
  //     Ok(None)
  //   }
  // }


  /// Parses a conjunction.
  fn conjunction(
    & mut self, var_map: & HashMap<& 'a str, VarIdx>
  ) -> Res< Vec<TTerm> > {
    if self.char_opt('(') {
      self.ws_cmt() ;
      self.tag("and") ? ;
      self.ws_cmt() ;
      let mut conj = Vec::with_capacity(11) ;
      while let Some(tterm) = self.top_term_opt(var_map) ? {
        conj.push(tterm) ;
        self.ws_cmt()
      }
      self.char(')') ? ;
      Ok(conj)
    } else {
      Ok( vec![ self.top_term(var_map) ? ] )
    }
  }


  /// Parses a forall.
  fn forall(& mut self) -> Res<
    Option< (VarMap<VarInfo>, Vec<TTerm>, TTerm) >
  > {
    if ! self.tag_opt("forall") {
      return Ok(None)
    }
    self.ws_cmt() ;
    let (var_map, hash_map) = self.args() ? ;
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;
    self.tag("=>") ? ;
    self.ws_cmt() ;
    let lhs = self.conjunction(& hash_map) ? ;
    self.ws_cmt() ;
    let rhs = if let Some(top_term) = self.top_term_opt(& hash_map) ? {
      top_term
    } else {
      bail!( self.error_here("expected top term") )
    } ;
    self.ws_cmt() ;
    self.char(')') ? ;
    Ok( Some((var_map, lhs, rhs)) )
  }


  /// Parses a negated exists.
  fn exists(& mut self) -> Res<
    Option< (VarMap<VarInfo>, Vec<TTerm>, TTerm) >
  > {
    if ! self.tag_opt("not") {
      return Ok(None)
    }
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;
    self.tag("exists") ? ;
    self.ws_cmt() ;
    let (var_map, hash_map) = self.args() ? ;
    self.ws_cmt() ;
    let lhs = self.conjunction(& hash_map) ? ;
    self.ws_cmt() ;
    self.char(')') ? ;
    Ok(
      Some( (var_map, lhs, TTerm::T(self.instance.bool(false))) )
    )
  }


  /// Parses an assert.
  fn assert(& mut self) -> Res<bool> {
    if ! self.tag_opt("assert") {
      return Ok(false)
    }
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;

    let (var_map, lhs, rhs) = if let Some(res) = self.forall() ? {
      res
    } else if let Some(res) = self.exists() ? {
      res
    } else {
      bail!(
        self.error_here("expected forall or negated exists")
      )
    } ;
    self.ws_cmt() ;
    self.char(')') ? ;

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
      self.instance.push_clause(
        Clause::mk(var_map, nu_lhs, rhs)
      )
    }

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

  /// Parses items, returns true if it found a check-sat.
  pub fn new_parse(& mut self) -> Res<bool> {
    self.ws_cmt() ;

    while self.has_next() {
      self.char('(') ? ;
      self.ws_cmt() ;

      if self.set_info() ? {
        ()
      } else if self.set_logic() ? {
        ()
      } else if self.pred_dec() ? {
        ()
      } else if self.assert() ? {
        ()
      } else if self.check_sat() {
        return Ok(true)
      } else {
        bail!(
          self.error_here("expected top-level item")
        )
      }

      self.ws_cmt() ;
      self.char(')') ? ;
      self.ws_cmt()
    }
    Ok(false)
  }
}


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
  #[doc = "Integer parser."],
  pub int<Int>, map!(
    re_bytes_find!("^([1-9][0-9]*|0)"),
    |bytes| Int::parse_bytes(bytes, 10).expect(
      "[bug] problem in integer parsing"
    )
  )
}
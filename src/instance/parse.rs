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
  /// Nothing.
  None,
}
impl Parsed {
  /// True if `None`.
  pub fn is_none(& self) -> bool {
    self == & Parsed::None
  }
}

/// Parser structure.
pub struct Parser<'a> {
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
  pred_name_map: HashMap<& 'a str, PrdIdx>,
}


impl<'a> Parser<'a> {
  /// Constructor.
  pub fn mk(string: & 'a str) -> Self {
    Parser {
      term_stack: Vec::with_capacity(17),
      chars: string.char_indices(),
      string,
      buff: Vec::with_capacity(17),
      mem: Vec::with_capacity(17),
      pred_name_map: HashMap::with_capacity(42),
    }
  }

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

  // /// The next token, used for errors.
  // fn next_token(& mut self) -> (usize, String) {
  //   if let Some( (pos, token) ) = self.ident_opt() {
  //     (pos, token.into())
  //   } else {
  //     self.next().map(
  //       |(pos, c)| if c == '\n' {
  //         (pos, "<new line>".to_string())
  //       } else {
  //         (pos, c.to_string())
  //       }
  //     ).unwrap_or( (self.string.len(), "eof".to_string()) )
  //   }
  // }

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
    let prev = self.pred_name_map.insert(ident, pred_index) ;
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
    & mut self, map: & HashMap<& 'a str, VarIdx>, instance: & Instance
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
        instance.int(int)
      } else if let Some(b) = self.bool() {
        instance.bool(b)
      } else if let Some((pos, id)) = self.ident_opt() {
        if let Some(idx) = map.get(id) {
          instance.var(* idx)
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
          term = instance.op(op, kids) ;
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
  fn top_term(
    & mut self, map: & HashMap<& 'a str, VarIdx>, instance: & Instance
  ) -> Res<TTerm> {
    if let Some(term) = self.top_term_opt(map, instance) ? {
      Ok(term)
    } else {
      bail!( self.error_here("expected term") )
    }
  }
  /// Tries to parse a term.
  fn top_term_opt(
    & mut self, map: & HashMap<& 'a str, VarIdx>, instance: & Instance
  ) -> Res< Option<TTerm> > {
    let res = if self.char_opt('(') {
      self.ws_cmt() ;
      if let Some(op) = self.op_opt() {
        self.ws_cmt() ;
        let args = self.term_seq(map, instance) ? ;
        self.ws_cmt() ;
        self.char(')') ? ;
        Ok( Some(
          TTerm::T( instance.op(op, args) )
        ) )
      } else if let Some((pos,ident)) = self.ident_opt() {
        self.ws_cmt() ;
        let args = self.term_seq(map, instance) ? ;
        self.ws_cmt() ;
        self.char(')') ? ;
        let pred = if let Some(idx) = self.pred_name_map.get(ident) {
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
      Ok( Some( TTerm::T( instance.bool(b) ) ) )
    } else if let Some(int) = self.int() {
      Ok( Some( TTerm::T( instance.int(int) ) ) )
    } else if let Some((pos,id)) = self.ident_opt() {
      if let Some(idx) = map.get(id) {
        Ok( Some( TTerm::T( instance.var(* idx) ) ) )
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
  //     let pred = if let Some(idx) = self.pred_name_map.get(ident) {
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
    & mut self, var_map: & HashMap<& 'a str, VarIdx>, instance: & Instance
  ) -> Res< Vec<TTerm> > {
    if self.char_opt('(') {
      self.ws_cmt() ;
      self.tag("and") ? ;
      self.ws_cmt() ;
      let mut conj = Vec::with_capacity(11) ;
      while let Some(tterm) = self.top_term_opt(var_map, instance) ? {
        conj.push(tterm) ;
        self.ws_cmt()
      }
      self.char(')') ? ;
      Ok(conj)
    } else {
      Ok( vec![ self.top_term(var_map, instance) ? ] )
    }
  }


  /// Parses a forall.
  fn forall(& mut self, instance: & Instance) -> Res<
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
    let lhs = self.conjunction(& hash_map, instance) ? ;
    self.ws_cmt() ;
    let rhs = if let Some(top_term) = self.top_term_opt(
      & hash_map, instance
    ) ? {  top_term } else {
      bail!( self.error_here("expected top term") )
    } ;
    self.ws_cmt() ;
    self.char(')') ? ;
    Ok( Some((var_map, lhs, rhs)) )
  }


  /// Parses a negated exists.
  fn exists(& mut self, instance: & mut Instance) -> Res<
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
    let lhs = self.conjunction(& hash_map, instance) ? ;
    self.ws_cmt() ;
    self.char(')') ? ;
    Ok(
      Some( (var_map, lhs, TTerm::T(instance.bool(false))) )
    )
  }


  /// Parses an assert.
  fn assert(& mut self, instance: & mut Instance) -> Res<bool> {
    if ! self.tag_opt("assert") {
      return Ok(false)
    }
    self.ws_cmt() ;
    self.char('(') ? ;
    self.ws_cmt() ;

    let (var_map, lhs, rhs) = if let Some(res) = self.forall(instance) ? {
      res
    } else if let Some(res) = self.exists(instance) ? {
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
      instance.push_clause(
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

  /// Parses a get-model.
  fn get_model(& mut self) -> bool {
    if self.tag_opt("get-model") {
      true
    } else {
      false
    }
  }

  /// Parses items, returns true if it found a check-sat.
  pub fn parse(
    & mut self, instance: & mut Instance
  ) -> Res<Parsed> {
    self.ws_cmt() ;

    while self.has_next() {
      self.char('(') ? ;
      self.ws_cmt() ;

      let res = if self.set_info() ? {
        Parsed::None
      } else if self.set_logic() ? {
        Parsed::None
      } else if self.pred_dec(instance) ? {
        Parsed::None
      } else if self.assert(instance) ? {
        Parsed::None
      } else if self.check_sat() {
        Parsed::CheckSat
      } else if self.get_model() {
        Parsed::GetModel
      } else {
        bail!(
          self.error_here("expected top-level item")
        )
      } ;

      self.ws_cmt() ;
      self.char(')') ? ;
      self.ws_cmt() ;

      if ! res.is_none() {
        return Ok(res)
      }
    }
    Ok(Parsed::None)
  }
}
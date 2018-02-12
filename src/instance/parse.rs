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
  static ref id_special_chars: HashSet<& 'static str> = {
    let mut set = HashSet::with_capacity(17) ;
    set.insert("~") ;
    set.insert("!") ;
    set.insert("@") ;
    set.insert("$") ;
    set.insert("%") ;
    set.insert("^") ;
    set.insert("&") ;
    set.insert("*") ;
    set.insert("_") ;
    set.insert("-") ;
    set.insert("+") ;
    set.insert("=") ;
    set.insert("<") ;
    set.insert(">") ;
    set.insert(".") ;
    set.insert("?") ;
    set.insert("/") ;
    set
  } ;
}



/// String extensions, lift char functions.
pub trait StringExt {
  /// Lifts `char::is_alphanumeric`.
  fn is_alphanumeric(& self) -> bool ;
  /// Lifts `char::is_alphabetic`.
  fn is_alphabetic(& self) -> bool ;
  /// Lifts `char::is_numeric`.
  fn is_numeric(& self) -> bool ;
}
impl StringExt for str {
  fn is_alphanumeric(& self) -> bool {
    for char in self.chars() {
      if ! char.is_alphanumeric() { return false }
    }
    true
  }
  fn is_alphabetic(& self) -> bool {
    for char in self.chars() {
      if ! char.is_alphabetic() { return false }
    }
    true
  }
  fn is_numeric(& self) -> bool {
    for char in self.chars() {
      if ! char.is_numeric() { return false }
    }
    true
  }
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
      } else if opn_parens < cls_parens {
        // Something's wrong, let the parser handle it.
        break 'read_lines
      }

      start = buf.len()
    }

    Ok(line_count)
  }
}


/// String cursor.
pub type Cursor = usize ;
/// Position in the text.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Pos(usize) ;
impl ::std::ops::Deref for Pos {
  type Target = usize ;
  fn deref(& self) -> & usize { & self.0 }
}


/// Parser context.
pub struct ParserCxt {
  /// Term stack to avoid recursion.
  term_stack: Vec<
    (Op, Pos, Vec<(Typ, Pos)>, Vec<Term>, LetCount)
  >,
  /// Memory for backtracking.
  mem: Vec<Cursor>,
  /// Map from predicate names to predicate indices.
  pred_name_map: HashMap<String, PrdIdx>,
}
impl ParserCxt {
  /// Constructor.
  pub fn new() -> Self {
    ParserCxt {
      term_stack: Vec::with_capacity(17),
      mem: Vec::with_capacity(17),
      pred_name_map: HashMap::with_capacity(42),
    }
  }
  /// Generates a parser from itself.
  pub fn parser<'cxt, 's>(
    & 'cxt mut self, string: & 's str, line_off: usize
  ) -> Parser<'cxt, 's> {
    debug_assert!( self.mem.is_empty() ) ;
    Parser {
      cxt: self,
      string,
      cursor: 0,
      line_off,
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
  /// Text being read (for errors).
  string: & 's str,
  /// Current position in the text.
  cursor: Cursor,
  /// Line offset (for errors).
  line_off: usize,
  /// Stack of bindings.
  bindings: Vec< HashMap<& 's str, (PTTerms, Typ)> >,
}


impl<'cxt, 's> Parser<'cxt, 's> {

  /// Generates a parse error at the current position.
  fn error_here<S: Into<String>>(& mut self, msg: S) -> ErrorKind {
    let pos = self.pos() ;
    self.error(pos, msg)
  }

  /// Generates a parse error at the given position.
  fn error<S: Into<String>>(
    & self, char_pos: Pos, msg: S
  ) -> ErrorKind {
    let mut char_pos = * char_pos ;
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
  #[inline]
  fn has_next(& self) -> bool {
    self.cursor < self.string.len()
  }
  /// The next character, does not move the cursor.
  fn peek(& self) -> Option<& 's str> {
    if self.has_next() {
      Some(
        & self.string[ self.cursor .. self.cursor + 1 ]
      )
    } else {
      None
    }
  }


  /// True if the current character is a legal unquoted identifier character.
  fn legal_id_char(& self) -> bool {
    if self.cursor >= self.string.len() {
      false
    } else {
      let char = & self.string[ self.cursor .. self.cursor + 1 ] ;
      char.is_alphanumeric()
      || id_special_chars.contains(& char)
    }
  }

  /// The next character.
  fn next(& mut self) -> Option<& 's str> {
    if self.has_next() {
      self.cursor += 1 ;
      Some(
        & self.string[ self.cursor - 1 .. self.cursor ]
      )
    } else {
      None
    }
  }
  /// Moves the cursor back by `n` character.
  ///
  /// # Panic
  ///
  /// - if `self.cursor < n`
  fn move_back(& mut self, n: usize) {
    debug_assert! { self.cursor >= n }
    self.cursor -= n
  }

  /// Backtracks to a precise position.
  fn backtrack_to(& mut self, Pos(pos): Pos) {
    self.cursor = pos
  }

  /// Returns the current position.
  fn pos(& mut self) -> Pos {
    Pos( self.cursor )
  }

  /// Consumes whitespaces and comments.
  fn ws_cmt(& mut self) {
    let mut done = false ;
    while ! done {
      // Eat spaces.
      let rest = & self.string[ self.cursor .. ] ;
      let trimmed = rest.trim_left() ;
      let diff = rest.len() - trimmed.len() ;
      done = diff == 0 ;
      self.cursor += diff ;

      // Eat comments.
      match self.next() {
        Some(";") => {
          done = false ;
          'eat_line: while let Some(char) = self.next() {
            if char == "\n" || char == "\r" {
              break 'eat_line
            }
          }
        },
        Some(_) => self.move_back(1),
        None => (),
      }
    }
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
  /// Parses a string or fails with error customization.
  fn tag_err<S>(& mut self, tag: & str, err: S) -> Res<()>
  where S: Into<String> {
    if self.tag_opt(tag) {
      Ok(())
    } else {
      bail!(
        self.error_here(
          format!("{}", err.into())
        )
      )
    }
  }
  /// Tries parsing a string.
  fn tag_opt(& mut self, tag: & str) -> bool {
    self.tag_opt_pos(tag).is_some()
  }
  /// Tries parsing a string. Returns the position of the start of the tag.
  fn tag_opt_pos(& mut self, tag: & str) -> Option<Pos> {
    if self.string.len() < self.cursor + tag.len() {
      None
    } else if & self.string[
      self.cursor .. self.cursor + tag.len()
    ] == tag {
      let res = Some(self.pos()) ;
      self.cursor = self.cursor + tag.len() ;
      res
    } else {
      None
    }
  }

  /// Parses an ident of fails.
  fn ident(& mut self) -> Res< (Pos, & 's str) > {
    if let Some(id) = self.ident_opt() ? {
      Ok(id)
    } else {
      bail!(
        self.error_here("expected an identifier")
      )
    }
  }
  /// Tries to parse an ident.
  fn ident_opt(& mut self) -> Res< Option< (Pos, & 's str) > > {
    let ident_start_pos = self.pos() ;
    if let Some(id) = self.unsafe_ident_opt() ? {
      if keywords::is_keyword(id) {
        bail!(
          self.error(
            ident_start_pos,
            format!(
              "illegal usage of keyword `{}`",
              conf.bad(id)
            )
          )
        )
      } else {
        Ok( Some((ident_start_pos, id)) )
      }
    } else {
      Ok(None)
    }
  }
  /// Tries to parse an ident, does not check anything about the ident.
  fn unsafe_ident_opt(& mut self) -> Res< Option<& 's str> > {
    let ident_start_pos = self.pos() ;
    if let Some(char) = self.next() {
      if char == "|" {
        let (mut legal_unquoted, mut is_first) = (true, true) ;
        'quoted: while let Some(char) = self.next() {
          if char == "|" {
            return Ok(
              Some(
                if legal_unquoted {
                  & self.string[ * ident_start_pos + 1 .. self.cursor - 1 ]
                } else {
                  & self.string[ * ident_start_pos .. self.cursor ]
                }
              )
            )
          } else {
            legal_unquoted = legal_unquoted && (
              ( ! is_first && char.is_alphanumeric() ) ||
              (   is_first && char.is_alphabetic()   ) ||
              id_special_chars.contains(char)
            ) ;
            is_first = false ;
          }
        }
        bail!(
          self.error(
            ident_start_pos, format!(
              "expected `|` closing this quoted identifier, found eof"
            )
          )
        )
      } else if char.is_alphabetic() || id_special_chars.contains(& char) {
        'unquoted: while let Some(char) = self.next() {
          if ! (
            char.is_alphanumeric() || id_special_chars.contains(& char)
          ) {
            self.move_back(1) ;
            break
          }
        }
        Ok(
          Some(
            & self.string[ * ident_start_pos .. self.cursor ]
          )
        )
      } else {
        self.backtrack_to(ident_start_pos) ;
        Ok(None)
      }
    } else {
      Ok(None)
    }
  }

  /// Consumes characters until and **including** some character.
  ///
  /// Returns `true` iff `char` was found. Hence, returns `false` iff `eof` was
  /// reached.
  fn eat_until(& mut self, char: char) -> bool {
    for c in self.string[ self.cursor .. ].chars() {
      self.cursor += 1 ;
      if char == c {
        return true
      }
    }
    false
  }

  /// Returns all the characters until some character.
  ///
  /// `None` iff `char` was not found, i.e. `eat_until` returns `false`.
  fn get_until(& mut self, char: char) -> Option<& 's str> {
    let start_pos = self.pos() ;
    let found_id = self.eat_until(char) ;
    if found_id {
      Some( & self.string[ * start_pos .. self.cursor ] )
    } else {
      None
    }
  }

  /// Parses a set-info.
  fn set_info(& mut self) -> Res<bool> {
    if ! self.tag_opt("set-info") {
      return Ok(false)
    }
    self.ws_cmt() ;
    self.tag(":") ? ;
    self.ws_cmt() ;
    let _ = self.ident() ? ;
    self.ws_cmt() ;
    if self.tag_opt("\"") {
      let found_it = self.eat_until('"') ;
      if ! found_it {
        bail!(
          self.error_here("expected closing `\"`, found <eof>")
        )
      }
    } else if self.ident_opt()?.is_some() {
      ()
    }
    Ok(true)
  }

  /// Parses an echo.
  fn echo(& mut self) -> Res< Option<& 's str> > {
    if ! self.tag_opt("echo") {
      return Ok(None)
    }
    self.ws_cmt() ;
    self.tag("\"") ? ;
    let blah = self.get_until('"') ;
    if let Some(blah) = blah {
      Ok( Some(blah) )
    } else {
      bail!(
        self.error_here("expected closing `\"`, found <eof>")
      )
    }
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

  /// Parses a sort or fails.
  fn sort(& mut self) -> Res<Typ> {
    if let Some(sort) = self.sort_opt() {
      Ok(sort)
    } else {
      bail!( self.error_here("expected sort (Int or Bool)") )
    }
  }
  /// Tries to parse a sort.
  fn sort_opt(& mut self) -> Option<Typ> {
    let start_pos = self.pos() ;
    if self.tag_opt("Int") {
      if ! self.legal_id_char() {
        Some(Typ::Int)
      } else {
        self.backtrack_to(start_pos) ;
        None
      }
    } else if self.tag_opt("Real") {
      if ! self.legal_id_char() {
        Some(Typ::Real)
      } else {
        self.backtrack_to(start_pos) ;
        None
      }
    } else if self.tag_opt("Bool") {
      if ! self.legal_id_char() {
        Some(Typ::Bool)
      } else {
        self.backtrack_to(start_pos) ;
        None
      }
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
    self.tag("(") ? ;

    let mut sorts = Vec::with_capacity(11) ;
    self.ws_cmt() ;
    while let Some(ty) = self.sort_opt() {
      self.ws_cmt() ;
      sorts.push(ty) ;
    }
    sorts.shrink_to_fit() ;

    self.ws_cmt() ;
    self.tag(")") ? ;
    self.ws_cmt() ;
    if ! self.tag_opt("Bool") {
      bail!(
        self.error_here("expected Bool sort")
      )
    }

    let pred_index = instance.push_pred(
      ident.into(), VarMap::of(sorts)
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
    self.tag("(") ? ;

    self.ws_cmt() ;
    while self.tag_opt("(") {
      self.ws_cmt() ;
      let (pos, ident) = self.ident() ? ;
      self.ws_cmt() ;
      let sort = self.sort() ? ;
      self.ws_cmt() ;
      self.tag(")") ? ;
      self.ws_cmt() ;
      let idx = var_map.next_index() ;
      let prev = hash_map.insert(ident, idx) ;
      if let Some(_) = prev {
        bail!(
          self.error(
            pos, format!(
              "found two quantifier variables named `{}`", conf.bad(ident)
            )
          )
        )
      }
      var_map.push( VarInfo::new(ident.into(), sort, idx) )
    }
    self.tag(")") ? ;
    var_map.shrink_to_fit() ;
    hash_map.shrink_to_fit() ;
    Ok(())
  }

  /// Adds a binding to the current bindings.
  fn insert_bind(
    & mut self, var: & 's str, term: PTTerms, typ: Typ
  ) -> Res<()> {
    if let Some(bindings) = self.bindings.last_mut() {
      bindings.insert(var, (term, typ)) ;
      Ok(())
    } else {
      bail!("bug, adding binding before pushing a binding scope")
    }
  }
  /// Pushes a binding scopes.
  fn push_bind(& mut self) {
    self.bindings.push( HashMap::with_capacity(17) )
  }
  /// Pops a binding scope.
  fn pop_bind(& mut self) -> Res<()> {
    if self.bindings.pop().is_none() {
      bail!("bug, popping binding scope but there's no scope")
    }
    Ok(())
  }
  /// Finds what a variable is mapped to.
  fn get_bind(& self, var: & str) -> Option< (& PTTerms, Typ) > {
    for bindings in & self.bindings {
      if let Some(& (ref tterms, typ)) = bindings.get(var) {
        return Some( (tterms, typ) )
      }
    }
    None
  }


  /// Parses the end of some consecutive let-bindings.
  #[inline]
  fn close_let_bindings(& mut self, count: LetCount) -> Res<()> {
    for _ in 0..count.n {
      self.ws_cmt() ;
      self.tag(")") ? ;
      self.pop_bind() ?
    }
    Ok(())
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
    & mut self,
    var_map: & VarMap<VarInfo>,
    map: & HashMap<& 's str, VarIdx>,
    instance: & Instance
  ) -> Res<LetCount> {
    let mut n = 0 ;
    
    'parse_lets: loop {
      if let Some(pos) = self.tag_opt_pos("(") {

        self.ws_cmt() ;
        if self.tag_opt( keywords::let_ ) {
          n += 1 ;
          self.push_bind() ;
          self.ws_cmt() ;
          self.tag("(") ? ;
          self.ws_cmt() ;
          while self.tag_opt("(") {
            self.ws_cmt() ;
            let (_, id) = self.ident() ? ;
            self.ws_cmt() ;
            let (tterms, typ) = self.parse_ptterms(
              var_map, map, instance
            ) ? ;
            self.insert_bind(id, tterms, typ) ? ;
            self.ws_cmt() ;
            self.tag(")") ? ;
            self.ws_cmt() ;
          }
          self.ws_cmt() ;
          self.tag_err(
            ")", format!(
              "expected binding or `{}` closing the list of bindings",
              conf.emph(")")
            )
          ) ? ;
        } else {
          self.backtrack_to(pos) ;
          break 'parse_lets
        }
      } else {
        break 'parse_lets
      }
      self.ws_cmt()
    }

    Ok( LetCount { n } )
  }

  /// Bool parser.
  fn bool(& mut self) -> Option<bool> {
    let start_pos = self.pos() ;
    if self.tag_opt("true") {
      if ! self.legal_id_char() {
        Some(true)
      } else {
        self.backtrack_to(start_pos) ;
        None
      }
    } else if self.tag_opt("false") {
      if ! self.legal_id_char() {
        Some(false)
      } else {
        self.backtrack_to(start_pos) ;
        None
      }
    } else {
      None
    }
  }

  /// Numeral parser.
  fn numeral(& mut self) -> Option<Int> {
    let start_pos = self.pos() ;

    if let Some(char) = self.next() {
      if char.is_numeric() {
        // If there's more numbers after this one, then the first one cannot be
        // zero.
        let mut cannot_be_zero = false ;
        while let Some(char) = self.next() {
          if ! char.is_numeric() {
            self.move_back(1) ;
            break
          }
          cannot_be_zero = true ;
        }
        if cannot_be_zero && char == "0" {
          self.backtrack_to(start_pos) ;
          None
        } else {
          Some(
            Int::parse_bytes(
              self.string[
                * start_pos .. self.cursor
              ].as_bytes(), 10
            ).expect("[bug] in integer parsing")
          )
        }
      } else {
        self.backtrack_to(start_pos) ;
        None
      }
    } else {
      None
    }
  }

  /// Decimal parser.
  #[allow(dead_code)]
  fn decimal(& mut self) -> Option<Rat> {
    let start_pos = self.pos() ;
    macro_rules! if_not_give_up {
      (( $($cond:tt)* ) => $thing:expr) => (
        if $($cond)* {
          $thing
        } else {
          self.backtrack_to(start_pos) ;
          return None
        }
      )
    }
    let num = if_not_give_up! {
      (let Some(num) = self.numeral()) => num
    } ;
    if_not_give_up! {
      ( self.tag_opt(".") ) => ()
    }
    let mut den: Int = 1.into() ;
    let ten = || consts::ten.clone() ;
    while self.tag_opt("0") { den = den * ten() }
    let dec_start_pos = self.pos() ;
    if let Some(dec) = self.numeral() {
      for _ in * dec_start_pos .. * self.pos() {
        den = den * ten()
      }
      Some( Rat::new( num * den.clone() + dec, den ) )
    } else if den != 1.into() {
      Some( Rat::new(num, 1.into()) )
    } else {
      self.backtrack_to(start_pos) ;
      None
    }
  }

  /// Integer parser (numeral not followed by a `.`).
  fn int(& mut self) -> Option<Int> {
    let start_pos = self.pos() ;
    let num = self.numeral() ;
    if num.is_some() {
      if self.peek() == Some(".") {
        self.backtrack_to(start_pos) ;
        return None
      }
    }
    num
  }

  /// Type checks an operator application.
  fn op_type_check(
    & self, op: Op, op_pos: Pos, args: Vec<(Typ, Pos)>
  ) -> Res<Typ> {
    match op.type_check(args) {
      Ok(typ) => Ok(typ),
      Err(Either::Left((Some(exp), (found, pos)))) => err_chain! {
        self.error(
          pos, format!(
            "expected an expression of sort {}, found {}", exp, found
          )
        )
        => self.error(op_pos, "in this operator application")
      },
      Err(Either::Left((None, (found, pos)))) => err_chain! {
        self.error(
          pos, format!(
            "expected the expression starting here has sort {} \
            which is illegal here", found
          )
        )
        => self.error(op_pos, "in this operator application")
      },
      Err(Either::Right(blah)) => bail!(
        self.error(
          op_pos, blah
        )
      ),
    }
  }

  /// Real parser.
  ///
  /// Decimal or fraction.
  fn real(& mut self) -> Res< Option<Rat> > {
    let start_pos = self.pos() ;

    if let Some(res) = self.decimal() {
      return Ok( Some(res) )
    }

    if self.tag_opt("(") {
      self.ws_cmt() ;
      if self.tag_opt("/") {
        self.ws_cmt() ;
        if let Some(num) = self.numeral() {
          self.tag_opt(".0") ;
          self.ws_cmt() ;
          let den_pos = self.pos() ;
          if let Some(den) = self.numeral() {
            self.tag_opt(".0") ;
            self.ws_cmt() ;
            if self.tag_opt(")") {
              if den.is_zero() {
                bail!(
                  self.error(
                    den_pos, "division by zero is not supported"
                  )
                )
              }
              return Ok(
                Some( Rat::new(num, den) )
              )
            } else {
              bail!(
                self.error(
                  start_pos, "division applied to more than two operands"
                )
              )
            }
          }
        }
      }
    }

    self.backtrack_to(start_pos) ;
    Ok(None)
  }

  /// Parses an operator or fails.
  fn op(& mut self) -> Res<Op> {
    if let Some(op) = self.op_opt() ? {
      Ok(op)
    } else {
      bail!( self.error_here("expected operator") )
    }
  }
  /// Tries to parse an operator.
  fn op_opt(& mut self) -> Res< Option<Op> > {
    macro_rules! none_if_ident_char_else {
      ($e:expr) => (
        if self.legal_id_char() {
          None
        } else { Some($e) }
      )
    }
    let start_pos = self.pos() ;
    let res = match self.next() {
      Some("a") => if self.tag_opt("nd") {
        none_if_ident_char_else!(Op::And)
      } else {
        None
      },
      Some("o") => if self.tag_opt("r") {
        none_if_ident_char_else!(Op::Or)
      } else {
        None
      },
      Some("n") => if self.tag_opt("ot") {
        none_if_ident_char_else!(Op::Not)
      } else {
        None
      },
      Some("i") => if self.tag_opt("te") {
        none_if_ident_char_else!(Op::Ite)
      } else {
        None
      },
      Some("m") => if self.tag_opt("od") {
        none_if_ident_char_else!(Op::Mod)
      } else {
        None
      },
      Some("r") => if self.tag_opt("em") {
        none_if_ident_char_else!(Op::Rem)
      } else {
        None
      },
      Some("d") => if self.tag_opt("iv") {
        none_if_ident_char_else!(Op::IDiv)
      } else {
        None
      },
      Some("t") => if self.tag_opt("o_int") {
        none_if_ident_char_else!(Op::ToInt)
      } else if self.tag_opt("o_real") {
        none_if_ident_char_else!(Op::ToReal)
      } else {
        None
      },
      Some("=") => if self.tag_opt(">") {
        Some(Op::Impl)
      } else {
        Some(Op::Eql)
      },
      Some(">") => if self.tag_opt("=") {
        Some(Op::Ge)
      } else {
        Some(Op::Gt)
      },
      Some("<") => if self.tag_opt("=") {
        Some(Op::Le)
      } else {
        Some(Op::Lt)
      },
      Some("+") => Some(Op::Add),
      Some("-") => Some(Op::Sub),
      Some("*") => Some(Op::Mul),
      Some("/") => Some(Op::Div),
      Some(_) => None,
      None => None,
    } ;

    if res.is_none() {
      self.backtrack_to(start_pos)
    }

    Ok( res )
  }

  /// Parses a single term.
  pub fn term_opt(
    & mut self,
    var_map: & VarMap<VarInfo>,
    map: & HashMap<& 's str, VarIdx>,
    instance: & Instance
  ) -> Res< Option<(Term, Typ)> > {
    debug_assert! { self.cxt.term_stack.is_empty() }
    let start_pos = self.pos() ;

    // The correct (non-error) way to exit this loop is
    //
    // `break 'read_kids <val>`
    //
    // If `<val> == None`, the code below will automatically backtrack to
    // `start_pos` and clear the `term_stack`, so there's no need to do it in
    // the loop.
    let res = 'read_kids: loop {

      let bind_count = self.let_bindings(var_map, map, instance) ? ;

      self.ws_cmt() ;
      let mut term_pos = self.pos() ;
      let (mut term, mut typ) = if let Some(int) = self.int() {
        ( term::int(int), Typ::Int )
      } else if let Some(real) = self.real() ? {
        ( term::real(real), Typ::Real )
      } else if let Some(b) = self.bool() {
        ( term::bool(b), Typ::Bool )
      } else if let Some((pos, id)) = self.ident_opt()? {

        if let Some(idx) = map.get(id) {
          ( term::var(* idx), var_map[* idx].typ )
        } else if let Some((ptterms, typ)) = self.get_bind(id) {
          if let Some(term) = ptterms.to_term().chain_err(
            || format!("while retrieving binding for {}", conf.emph(id))
          ) ? {
            (term, typ)
          } else {
            // Not in a legal term.
            break 'read_kids None
          }
        } else if self.cxt.pred_name_map.get(id).is_some() {
          // Identifier is a predicate, we're not in a legal term.
          break 'read_kids None
        } else {
          bail!(
            self.error(
              pos, format!("unknown identifier `{}`", conf.bad(id))
            )
          )
        }

      } else if self.tag_opt("(") {

        self.ws_cmt() ;
        let op_pos = self.pos() ;
        if let Some(op) = self.op_opt() ? {
          let typs = Vec::with_capacity(11) ;
          let kids = Vec::with_capacity(11) ;
          self.cxt.term_stack.push( (op, op_pos, typs, kids, bind_count) ) ;
          continue 'read_kids
        } else if self.cxt.term_stack.is_empty() {
          break 'read_kids None
        } else {
          self.op() ? ;
          unreachable!()
        }

      } else {

        break 'read_kids None

      } ;

      'go_up: while let Some(
        (op, op_pos, mut typs, mut kids, bind_count)
      ) = self.cxt.term_stack.pop() {
        debug_assert_eq! { typs.len(), kids.len() }
        typs.push( (typ, term_pos) ) ;
        kids.push(term) ;
        self.ws_cmt() ;
        if self.tag_opt(")") {
          typ = self.op_type_check(op, op_pos, typs) ? ;
          term = term::app(op, kids) ;
          term_pos = op_pos ;
          self.ws_cmt() ;
          self.close_let_bindings(bind_count) ? ;
          continue 'go_up
        } else {
          self.cxt.term_stack.push( (op, op_pos, typs, kids, bind_count) ) ;
          continue 'read_kids
        }
      }

      // Stack is empty, done.
      debug_assert!( self.cxt.term_stack.is_empty() ) ;
      break 'read_kids Some((term, typ))
    } ;

    if res.is_none() {
      self.cxt.term_stack.clear() ;
      self.backtrack_to(start_pos) ;
    }

    Ok(res)
  }

  /// Parses arguments for a predicate application and type-checks it.
  fn pred_args(
    & mut self,
    pred: PrdIdx,
    pred_pos: Pos,
    var_map: & VarMap<VarInfo>,
    map: & HashMap<& 's str, VarIdx>,
    instance: & Instance
  ) -> Res< Option<PTTerms> > {
    let mut args = VarMap::with_capacity(11) ;
    let mut typs = Vec::with_capacity(11) ;

    let mut backtrack_pos = self.pos() ;
    let mut term_pos = self.pos() ;

    while let Some((term, typ)) = self.term_opt(
      var_map, map, instance
    ) ? {
      typs.push( (typ, term_pos) ) ;
      args.push(term) ;
      backtrack_pos = self.pos() ;
      self.ws_cmt() ;
      term_pos = self.pos()
    }

    self.backtrack_to(backtrack_pos) ;

    args.shrink_to_fit() ;

    let sig = & instance[pred].sig ;

    if sig.len() != typs.len() {
      bail!(
        self.error(
          pred_pos, format!(
            "predicate {} takes {} arguments, but is applied to {}",
            conf.emph(& instance[pred].name), sig.len(), typs.len()
          )
        )
      )
    } else {
      let mut count = 0 ;
      for (exp, (found, pos)) in sig.iter().zip( typs.into_iter() ) {
        count += 1 ;
        if exp != & found {
          err_chain! {
            self.error(
              pos, format!(
                "expected an expression of sort {}, found {}",
                exp, found
              )
            )
            => self.error(
              pred_pos, format!(
                "in this application of {}, parameter #{}",
                conf.emph(& instance[pred].name), count
              )
            )
          }
        }
      }
    }

    Ok(
      Some(
        PTTerms::tterm( TTerm::P { pred, args: args.into() } )
      )
    )
  }


  /// Parses a top term or fails.
  #[allow(dead_code)]
  fn top_term(
    & mut self,
    var_map: & VarMap<VarInfo>,
    map: & HashMap<& 's str, VarIdx>,
    instance: & Instance,
  ) -> Res<(PTTerms, Typ)> {
    if let Some(res) = self.top_term_opt(var_map, map, instance) ? {
      Ok(res)
    } else {
      bail!( self.error_here("expected term") )
    }
  }
  /// Tries to parse a top term.
  fn top_term_opt(
    & mut self,
    var_map: & VarMap<VarInfo>,
    map: & HashMap<& 's str, VarIdx>,
    instance: & Instance,
  ) -> Res< Option< (PTTerms, Typ) > > {
    let bind_count = self.let_bindings(var_map, map, instance) ? ;

    self.ws_cmt() ;
    let start_pos = self.pos() ;

    let res = if let Some((term, typ)) = self.term_opt(
      var_map, map, instance
    ) ? {
      Ok( Some(
        ( PTTerms::tterm( TTerm::T( term ) ), typ )
      ) )
    } else if let Some((pos, id)) = self.ident_opt() ? {
      if let Some(idx) = self.cxt.pred_name_map.get(id) {
        let idx = * idx ;
        if instance[idx].sig.is_empty() {
          Ok( Some(
            (
              PTTerms::TTerm(
                TTerm::P { pred: idx, args: VarMap::with_capacity(0).into() }
              ), Typ::Bool
            )
          ) )
        } else {
          bail!(
            self.error(
              pos, format!(
                "illegal nullary application of predicate `{}`, \
                this predicate takes {} arguments",
                conf.bad(& instance[idx].name), instance[idx].sig.len()
              )
            )
          )
        }
      } else if let Some((ptterms, typ)) = self.get_bind(id) {
        Ok( Some( (ptterms.clone(), typ) ) )
      } else {
        bail!(
          self.error(
            pos, format!(
              "unknown ident `{}`", conf.bad(id)
            )
          )
        )
      }
    } else if self.tag_opt("(") {
      self.ws_cmt() ;

      if self.tag_opt(keywords::forall) {
        bail!(
          self.error(
            start_pos,
            format!("unable to work on clauses that are not ground")
          )
        )
      } else if self.tag_opt(keywords::exists) {
        bail!(
          self.error(
            start_pos,
            format!("unable to work on clauses that are not ground")
          )
        )
      } else if let Some((pred_pos,ident)) = self.ident_opt()? {
        if let Some(idx) = self.cxt.pred_name_map.get(ident).map(|i| * i) {
          let res = self.pred_args(idx, pred_pos, var_map, map, instance) ? ;
          self.ws_cmt() ;
          self.tag(")") ? ;
          Ok(res.map(|res| (res, Typ::Bool)))
        } else {
          bail!(
            self.error(
              pred_pos,
              format!("unknown predicate `{}`", conf.bad(ident))
            )
          )
        }
      } else {
        bail!(
          self.error_here("expected operator, let binding or predicate")
        )
      }

    } else {
      // In theory, we should check if the top term is an ident that's either a
      // quantified or bound variable. In practice, this is done at the level
      // above this one, in `parse_ptterms`.
      Ok(None)
    } ;

    self.ws_cmt() ;
    self.close_let_bindings(bind_count) ? ;

    res
  }


  /// Parses some top terms (parsing variant, for simplifications).
  fn parse_ptterms(
    & mut self,
    var_map: & VarMap<VarInfo>,
    map: & HashMap<& 's str, VarIdx>,
    instance: & Instance,
  ) -> Res<(PTTerms, Typ)> {
    enum Frame {
      And(Vec<PTTerms>), Or(Vec<PTTerms>), Impl(Vec<PTTerms>),
      Not, Let(LetCount)
    }
    let mut stack: Vec<Frame> = vec![] ;

    'go_down: loop {
      self.ws_cmt() ;

      let bind_count = self.let_bindings(var_map, & map, instance) ? ;
      if ! bind_count.is_zero() {
        stack.push( Frame::Let(bind_count) ) ;
      }

      self.ws_cmt() ;

      let start_pos = self.pos() ;
      let mut ptterm = if let Some(pos) = self.tag_opt_pos("(") {

        self.ws_cmt() ;

        if self.tag_opt("and") {
          stack.push( Frame::And(vec![]) ) ;
          continue 'go_down
        } else if self.tag_opt("or") {
          stack.push( Frame::Or(vec![]) ) ;
          continue 'go_down
        } else if self.tag_opt("not") {
          stack.push( Frame::Not ) ;
          continue 'go_down
        } else if self.tag_opt("=>") {
          stack.push( Frame::Impl(vec![]) ) ;
          continue 'go_down
        } else {
          self.backtrack_to(pos) ;
          if let Some((top, typ)) = self.top_term_opt(
            var_map, & map, instance
          ) ? {
            if typ.is_bool() {
              top
            } else
            // If we get here, it means what we're parsing does not have type
            // bool. Which means we're not inside a top-term (we're most likely
            // parsing a let-binding).
            if stack.is_empty() {
              return Ok(
                (top, typ)
              )
            } else {
              err_chain! {
                "while parsing top term"
                => self.error(
                  start_pos, format!(
                    "expected expression of type Bool, found {}", typ
                  )
                )
              }
            }
          } else if let Some((top, typ)) = self.term_opt(
            var_map, & map, instance
          ) ? {
            if typ.is_bool() {
              PTTerms::TTerm( TTerm::T(top) )
            } else
            // If we get here, it means what we're parsing does not have type
            // bool. Which means we're not inside a top-term (we're most likely
            // parsing a let-binding).
            if stack.is_empty() {
              return Ok(
                ( PTTerms::TTerm( TTerm::T(top) ), typ )
              )
            } else {
              err_chain! {
                "while parsing subterm"
                => self.error(
                  start_pos, format!(
                    "expected expression of type Bool, found {}", typ
                  )
                )
              }
            }
          } else {
            bail!(
              self.error(
                start_pos, "failed to parse expression top term"
              )
            )
          }
        }
      } else {
        if let Some((top, typ)) = self.top_term_opt(
          var_map, & map, instance
        ) ? {
          if typ.is_bool() {
            top
          } else
          // If we get here, it means what we're parsing does not have type
          // bool. Which means we're not inside a top-term (we're most likely
          // parsing a let-binding).
          if stack.is_empty() {
            return Ok(
              (top, typ)
            )
          } else {
            err_chain! {
              "while parsing top term"
              => self.error(
                start_pos, format!(
                  "expected expression of type Bool, found {}", typ
                )
              )
            }
          }
        } else if let Some((top, typ)) = self.term_opt(
          var_map, & map, instance
        ) ? {
          if typ.is_bool() {
            PTTerms::TTerm( TTerm::T(top) )
          } else
          // If we get here, it means what we're parsing does not have type
          // bool. Which means we're not inside a top-term (we're most likely
          // parsing a let-binding).
          if stack.is_empty() {
            return Ok(
              ( PTTerms::TTerm( TTerm::T(top) ), typ )
            )
          } else {
            err_chain! {
              "while parsing subterm (ident or constant)"
              => self.error(
                start_pos, format!(
                  "expected expression of type Bool, found {}", typ
                )
              )
            }
          }
        } else {
          bail!(
            self.error(
              start_pos, "failed to parse top expression"
            )
          )
        }
      } ;

      'go_up: loop {
        match stack.pop() {
          Some( Frame::And(mut args) ) => {
            args.push(ptterm) ;
            self.ws_cmt() ;
            if self.tag_opt(")") {
              ptterm = PTTerms::and(args) ;
              continue 'go_up
            } else {
              stack.push( Frame::And(args) ) ;
              continue 'go_down
            }
          },
          Some( Frame::Or(mut args) ) => {
            args.push(ptterm) ;
            self.ws_cmt() ;
            if self.tag_opt(")") {
              ptterm = PTTerms::or(args) ;
              continue 'go_up
            } else {
              stack.push( Frame::Or(args) ) ;
              continue 'go_down
            }
          },
          Some( Frame::Impl(mut args) ) => {
            args.push(ptterm) ;
            self.ws_cmt() ;
            if self.tag_opt(")") {
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
            self.ws_cmt() ;
            ptterm = PTTerms::not(ptterm) ? ;
            self.tag(")") ? ;
            continue 'go_up
          },
          Some( Frame::Let(bind_count) ) => {
            self.close_let_bindings(bind_count) ? ;
            continue 'go_up
          },
          None => break 'go_down Ok( (ptterm, Typ::Bool) ),
        }
      }

    }
  }


  /// Parses a forall.
  fn forall(
    & mut self, instance: & mut Instance
  ) -> Res<bool> {
    if ! self.tag_opt(keywords::forall) {
      return Ok(false)
    }

    let (mut var_map, mut hash_map, mut parse_args, mut closing_parens) = (
      VarMap::with_capacity(11), HashMap::with_capacity(11), true, 0
    ) ;

    while parse_args {
      self.ws_cmt() ;
      self.args(& mut var_map, & mut hash_map) ? ;

      self.ws_cmt() ;
      parse_args = if let Some(pos) = self.tag_opt_pos("(") {
        self.ws_cmt() ;
        if self.tag_opt(keywords::forall) {
          closing_parens += 1 ;
          true
        } else {
          self.backtrack_to(pos) ;
          false
        }
      } else {
        false
      }
    }

    self.ws_cmt() ;
    let outter_bind_count = self.let_bindings(
      & var_map, & hash_map, instance
    ) ? ;

    self.ws_cmt() ;
    self.parse_clause(
      var_map, hash_map, instance, false
    ) ? ;

    self.ws_cmt() ;
    self.close_let_bindings(outter_bind_count) ? ;

    for _ in 0..closing_parens {
      self.ws_cmt() ;
      self.tag(")") ?
    }

    Ok(true)
  }


  /// Parses a negated exists.
  fn nexists(& mut self, instance: & mut Instance) -> Res<bool> {
    if ! self.tag_opt(keywords::op::not_) {
      return Ok(false)
    }
    self.ws_cmt() ;
    let outter_bind_count = self.let_bindings(
      & VarMap::new(), & HashMap::new(), instance
    ) ? ;

    self.ws_cmt() ;
    self.tag("(") ? ;

    self.ws_cmt() ;
    self.tag(keywords::exists) ? ;

    let (mut var_map, mut hash_map, mut parse_args, mut closing_parens) = (
      VarMap::with_capacity(11), HashMap::with_capacity(11), true, 0
    ) ;

    while parse_args {
      self.ws_cmt() ;
      self.args(& mut var_map, & mut hash_map) ? ;

      self.ws_cmt() ;
      parse_args = if let Some(pos) = self.tag_opt_pos("(") {
        self.ws_cmt() ;
        if self.tag_opt(keywords::exists) {
          closing_parens += 1 ;
          true
        } else {
          self.backtrack_to(pos) ;
          false
        }
      } else {
        false
      }
    }

    self.ws_cmt() ;
    self.parse_clause(var_map, hash_map, instance, true) ? ;

    self.ws_cmt() ;
    self.tag(")") ? ;

    self.ws_cmt() ;
    self.close_let_bindings(outter_bind_count) ? ;

    for _ in 0..closing_parens {
      self.ws_cmt() ;
      self.tag(")") ?
    }

    Ok(true)
  }


  fn parse_clause(
    & mut self,
    var_map: VarMap<VarInfo>,
    map: HashMap<& 's str, VarIdx>,
    instance: & mut Instance,
    negated: bool,
  ) -> Res<()> {
    self.ws_cmt() ;

    let start_pos = self.pos() ;
    let (mut ptterms, typ) = self.parse_ptterms(
      & var_map, & map, instance
    ) ? ;
    if ! typ.is_bool() {
      err_chain! {
        "while parsing clause terms"
        => self.error(
          start_pos, format!(
            "expected expression of type Bool, got {}", typ
          )
        )
      }
    }
    if negated {
      ptterms = PTTerms::not(ptterms) ?
    }

    let mut clauses = ptterms.to_clauses()?.into_iter() ;
    if let Some((last_lhs, last_rhs)) = clauses.next() {
      for (lhs, rhs) in clauses {
        self.add_clause(instance, var_map.clone(), lhs, rhs) ?
      }
      self.add_clause(instance, var_map, last_lhs, last_rhs) ?
    }
    Ok(())
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
    let rhs = match rhs {
      TTerm::P { pred, args } => Some((pred, args)),
      TTerm::T(t) => {
        if t.bool() != Some(false) {
          nu_lhs.push( TTerm::T( term::not(t) ) )
        }
        None
      },
    } ;
    if ! lhs_is_false {
      instance.push_clause(
        Clause::new(var_map.clone(), nu_lhs, rhs)
      ) ?
    }
    Ok(())
  }


  /// Parses an assert.
  fn assert(& mut self, instance: & mut Instance) -> Res<bool> {
    if ! self.tag_opt(keywords::cmd::assert) {
      return Ok(false)
    }

    self.ws_cmt() ;
    let bind_count = self.let_bindings(
      & VarMap::new(), & HashMap::new(), instance) ? ;

    if self.tag_opt("(") {
      self.ws_cmt() ;

      if self.forall(instance) ? {
        ()
      } else if self.nexists(instance) ? {
        ()
      } else {
        bail!(
          self.error_here("expected forall or negated exists")
        )
      } ;

      self.ws_cmt() ;
      self.tag(")") ? ;
    } else if self.tag_opt("true") {
      ()
    } else if self.tag_opt("false") {
      instance.set_unsat()
    } else {
      bail!(
        self.error_here("expected negation, qualifier, `true` or `false`")
      )
    }

    self.ws_cmt() ;
    self.close_let_bindings(bind_count) ? ;

    Ok(true)
  }

  /// Parses a check-sat.
  fn check_sat(& mut self) -> bool {
    if self.tag_opt(keywords::cmd::check_sat) {
      true
    } else {
      false
    }
  }

  /// Parses a get-model.
  fn get_model(& mut self) -> bool {
    if self.tag_opt(keywords::cmd::get_model) {
      true
    } else {
      false
    }
  }

  /// Parses an exit command.
  fn exit(& mut self) -> bool {
    if self.tag_opt(keywords::cmd::exit) {
      true
    } else {
      false
    }
  }

  /// Parses an reset command.
  fn reset(& mut self) -> bool {
    if self.tag_opt(keywords::cmd::reset) {
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
      self.ws_cmt() ;
      self.tag_err(
        "(", format!(
          "expected `{}` opening top-level item",
          conf.emph("(")
        )
      ) ? ;
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
      self.tag(")") ? ;
      self.ws_cmt() ;

      debug_assert!( self.cxt.term_stack.is_empty() ) ;
      debug_assert!( self.cxt.mem.is_empty() ) ;

      if res != Parsed::Items {
        return Ok(res)
      }
    }

    debug_assert!( self.cxt.term_stack.is_empty() ) ;
    debug_assert!( self.cxt.mem.is_empty() ) ;

    Ok(res)
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

  /// True if `PTTerms` does not contain a non-negated predicate.
  pub fn is_legal_lhs(& self) -> bool {
    let mut to_do = Vec::with_capacity(37) ;
    to_do.push(self) ;

    while let Some(ptterm) = to_do.pop() {
      match * ptterm {
        PTTerms::And(ref args) => for arg in args {
          to_do.push(arg)
        },
        PTTerms::Or(ref args) => for arg in args {
          to_do.push(arg)
        },
        PTTerms::NTTerm(_) => (),
        PTTerms::TTerm(ref term) => if term.pred().is_some() {
          return false
        },
      }
    }

    true
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
        let mut multipliers = Vec::with_capacity(3) ;
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
              let mut positive_preds = None ;
              for ptt in ptts {
                match ptt {
                  PTTerms::NTTerm(tterm) => tts.push(tterm),
                  PTTerms::TTerm(tterm) => match tterm {
                    TTerm::T(term) => tts.push( TTerm::T(term::not(term)) ),
                    tterm => {
                      let positive_preds = positive_preds.get_or_insert_with(
                        || Vec::with_capacity(7)
                      ) ;
                      positive_preds.push( tterm )
                    },
                  },
                  ptt => if let Some(term) = ptt.to_term() ? {
                    tts.push( TTerm::T( term::not(term) ) )
                  } else {
                    bail!("ill-formed horn clause (or, 2)")
                  },
                }
              }
              if let Some(pos_preds) = positive_preds {
                tts.extend( pos_preds ) ;
                rhs = Some( tts )
              } else {
                multipliers.push(tts)
              }
            },

            _ => bail!("ecountered normalization issue (or, 3)"),
          }
        }

        let nu_lhs = if multipliers.len() <= 2 {

          let mut nu_lhs = Vec::with_capacity(
            multipliers.len() * 2
          ) ;
          nu_lhs.push(lhs) ;
          let mut tmp_lhs = Vec::with_capacity(nu_lhs.len()) ;
          for mut vec in multipliers {
            if let Some(last) = vec.pop() {
              tmp_lhs.clear() ;
              for tterm in vec {
                for lhs in & nu_lhs {
                  let mut lhs = lhs.clone() ;
                  lhs.push( tterm.clone() ) ;
                  tmp_lhs.push( lhs )
                }
              }
              for mut lhs in nu_lhs.drain(0..) {
                lhs.push(last.clone()) ;
                tmp_lhs.push( lhs )
              }
              ::std::mem::swap(& mut nu_lhs, & mut tmp_lhs)
            }
          }

          nu_lhs

        } else {

          for disj in multipliers {
            let mut nu_disj = Vec::with_capacity( disj.len() ) ;
            for tterm in disj {
              if let TTerm::T(term) = tterm {
                nu_disj.push(term)
              } else {
                bail!("error during clause conversion")
              }
            }
            lhs.push(
              TTerm::T( term::or(nu_disj) )
            )
          }
          vec![ lhs ]

        } ;

        if let Some(rhs) = rhs {
          let mut res = Vec::with_capacity( rhs.len() ) ;
          let mut rhs = rhs.into_iter() ;
          if let Some(last) = rhs.next() {
            for rhs in rhs {
              for lhs in & nu_lhs {
                res.push( (lhs.clone(), rhs.clone()) )
              }
            }
            for lhs in nu_lhs {
              res.push((lhs, last.clone()))
            }
          }
          Ok(res)
        } else {
          Ok(
            nu_lhs.into_iter().map(
              |lhs| (lhs, TTerm::fls())
            ).collect()
          )
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
  pub fn to_term(& self) -> Res<Option<Term>> {
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
          return Ok(None)
        },
        PTTerms::NTTerm(ref tterm) => if let Some(term) = tterm.term() {
          term::not( term.clone() )
        } else {
          return Ok(None)
        },
      } ;

      'go_up: loop {
        if let Some((op, mut to_do, mut done)) = stack.pop() {
          done.push(term) ;
          if let Some(next) = to_do.next() {
            stack.push( (op, to_do, done) ) ;
            ptterm = next ;
            continue 'go_down
          } else {
            term = term::app(op, done) ;
            continue 'go_up
          }
        } else {
          break 'go_down Ok( Some(term) )
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
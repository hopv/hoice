//! Instance builder.

use nom::{ IResult, multispace } ;

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

/// Tries to parse something. If it fails, parses anything and returns an
/// error.
macro_rules! err {
  ($bytes:expr, $sub_mac:ident!( $($args:tt)* ), $e:expr) => (
    return_error!(
      $bytes,
      ::nom::ErrorKind::Custom(
        InternalParseError::from( ($e, $bytes) )
      ),
      $sub_mac!($($args)*)
    )
  ) ;
  ($bytes:expr, $fun:ident, $e:expr) => (
    return_error!(
      $bytes,
      ::nom::ErrorKind::Custom(
        InternalParseError::from( ($e, $bytes) )
      ),
      $fun
    )
  ) ;
  ($bytes:expr, ident) => (
    err!( $bytes, ident, "expected identifier" )
  ) ;
  ($bytes:expr, op) => (
    err!( $bytes, call!( Op::parse ), "expected operator" )
  ) ;
  ($bytes:expr, typ) => (
    err!( $bytes, call!( Typ::parse ), "expected type" )
  ) ;
  ($bytes:expr, char $c:expr, $e:expr) => (
    err!( $bytes, char!($c), format!("expected `{}` {}", $c, $e) )
  ) ;
}

/// Calls a function on some values, early returns in case of custom error,
/// propagates otherwise.
macro_rules! try_call {
  ($bytes:expr, $slf:ident.$sub:ident($($args:tt)*)) => (
    match $slf.$sub($bytes, $($args)*) {
      IResult::Error(e) => match e {
        ::nom::ErrorKind::Custom(e) => return IResult::Error(
          ::nom::ErrorKind::Custom(e)
        ),
        _ => IResult::Error(::nom::ErrorKind::Fix),
      },
      IResult::Done(i,o) => IResult::Done(i,o),
      IResult::Incomplete(n) => IResult::Incomplete(n),
    }
  ) ;
}


macro_rules! with_from_end {
  ($bytes:expr, $($tail:tt)*) => (
    map!($bytes, $($tail)*, |res| (res, $bytes.len()))
  ) ;
}

named!{
  #[doc = "Comment parser."],
  pub cmt, re_bytes_find!(r#"^;;.*[\n\r]*"#)
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
  pub ident<& str>, alt_complete!(
    sident | qident
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

named!{
  #[doc = "Boolean parser."],
  pub bool<bool>, alt_complete!(
    map!( tag!("true"), |_| true ) |
    map!( tag!("false"), |_| false )
  )
}

/// Parser that Fails whatever the input.
pub fn fail<T>(_bytes: & [u8]) -> IResult<& [u8], T> {
  IResult::Error(
    error_position!(
      ::nom::ErrorKind::Custom(0), _bytes
    )
  )
}


/// Instance builder.
pub struct InstBuild {
  /// The instance under construction.
  instance: Instance,
  /// Errors.
  errors: Vec<InternalParseError>,
  /// Map from predicate names to predicate indices.
  pred_name_map: HashMap<String, PrdIdx>,
}
impl InstBuild {
  /// Creates an instance builder.
  pub fn mk() -> Self {
    InstBuild {
      instance: Instance::mk(300, 42, 42),
      errors: vec![],
      pred_name_map: HashMap::with_capacity(42),
    }
  }

  /// Destroys the builder into its errors.
  ///
  /// The weird `line` argument works as follows: if it is
  ///
  /// - `None`, then the data generated will have no line info (useful when
  ///   reading from `stdin`) ;
  /// - `Some(off)`, then the data will have a line info which is the line 
  ///   where the error token appears in `input` plus `off` (useful when
  ///   reading a file incrementally to add an offset to error messages). 
  pub fn to_error(self, input: & [u8], line: Option<usize>) -> Error {
    // Print all errors but the last one, which we propagate upward.
    let count = self.errors.len() ;
    for err in self.errors {
      print_err( err.to_error(input, line) )
    }
    if count > 0 {
      format!(
        "parsing failed with {} errors",
        conf.bad(& format!("{}", count))
      ).into()
    } else {
      "[bug] parsing failed because of an unknown error".into()
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
        info!{
          "trivial predicate {}: forcing to {}", self.instance[pred], term
        }
        self.instance.force_pred(pred, term) ? ;
        let clause = self.instance.forget_clause(cls_idx) ;
        info!{
          "dropped associated clause {}",
          clause.string_do( & self.instance.preds, |s| s.to_string() ) ?
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
            let clause = self.instance.forget_clause(cls_idx) ;
            info!{
              "dropping clause {}, rhs is true",
              clause.string_do( & self.instance.preds, |s| s.to_string() ) ?
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
    mut self, input: & [u8], line: Option<usize>
  ) -> Res<Instance> {
    'simplify: loop {
      let _tautologies = self.simplify_tautologies() ? ;
      info!{ "{} predicates found to be tautologies", _tautologies }
      let propagations = self.propagate_forced() ? ;
      if propagations == 0 {
        info!{ "done simplifying\n" }
        break 'simplify
      } else {
        info!{ "{} propagations\n", propagations }
      }
    }

    if self.errors.is_empty() {
      self.instance.shrink_to_fit() ;
      Ok(self.instance)
    } else {
      Err( self.to_error(input, line) )
    }
  }

  /// Predicate accessor.
  pub fn preds(& self) -> & PrdMap<PrdInfo> {
    self.instance.preds()
  }
  /// Clause accessor.
  pub fn clauses(& self) -> & ClsMap<Clause> {
    self.instance.clauses()
  }

  /// Parses a term.
  #[allow(unused_variables)]
  pub fn parse_term<'b>(
    & mut self, bytes: & 'b [u8], vars: & HashMap<& 'b str, VarIdx>
  ) -> IResult<& 'b [u8], Term, InternalParseError> {
    fix_error!(
      bytes,
      InternalParseError,
      alt_complete!(
        map!(
          int, |n| {
            let cst = self.instance.int(n.clone() + 1) ;
            let _ = self.instance.consts.insert( cst.clone() ) ;
            let cst = self.instance.int(n.clone() - 1) ;
            let _ = self.instance.consts.insert( cst.clone() ) ;
            let cst = self.instance.int(n) ;
            let _ = self.instance.consts.insert( cst.clone() ) ;
            cst
          }
        ) |
        map!(bool, |n| self.instance.bool(n)) |
        map!(
          with_from_end!(ident),
          |(id, from_end)| if let Some(idx) = vars.get(id) {
            self.instance.var(* idx)
          } else {
            self.errors.push(
              (format!("unknown variable `{}`", id), from_end).into()
            ) ;
            self.instance.var( vars.len().into() )
          }
        ) |
        do_parse!(
          char!('(') >>
          spc_cmt >> op: err!( op ) >>
          spc_cmt >> args: many0!(
            terminated!(
              try_call!( self.parse_term(vars) ),
              spc_cmt
            )
          ) >>
          spc_cmt >> err!( char ')', "closing operator application" ) >> (
            self.instance.op(op, args)
          )
        )
      )
    )
  }

  /// Parses a predicate declaration.
  #[allow(unused_variables)]
  pub fn parse_dec_pred<'b>(
    & self, bytes: & 'b [u8]
  ) -> IResult<& 'b [u8], (String, usize, Vec<Typ>), InternalParseError> {
    fix_error!(
      bytes,
      InternalParseError,
      do_parse!(
        spc_cmt >>
        id: with_from_end!( err!(ident) ) >>
        spc_cmt >>
        err!( char '(', "opening predicate signature" ) >>
        spc_cmt >>
        sig: many0!(
          terminated!(
            fix_error!(u32, call!(Typ::parse) ), spc_cmt
          )
        ) >>
        err!( char ')', "closing predicate signature" ) >>
        ( (id.0.into(), id.1, sig) )
      )
    )
  }


  /// Parses a top term.
  #[allow(unused_variables)]
  pub fn parse_top_term<'b>(
    & mut self, bytes: & 'b [u8], vars: & HashMap<& 'b str, VarIdx>
  ) -> IResult<& 'b [u8], TTerm, InternalParseError> {
    fix_error!(
      bytes,
      InternalParseError,
      alt_complete!(
        // Negation of a term.
        do_parse!(
          char!('(') >>
          spc_cmt >> tag!("not") >>
          spc_cmt >> term: try_call!( self.parse_term(& vars) ) >>
          spc_cmt >> char!(')') >> (
            TTerm::N(term)
          )
        ) |
        // Predicate application.
        do_parse!(
          char!('(') >>
          spc_cmt >> not!( peek!( call!(Op::parse) ) ) >>
          id: with_from_end!( err!(ident) ) >>
          spc_cmt >> args: many0!(
            terminated!(
              try_call!( self.parse_term(& vars) ),
              spc_cmt
            )
          ) >>
          spc_cmt >> err!(
            char ')', "closing predicate application"
          ) >> ({
            let pred = if let Some(pred) = self.pred_name_map.get(id.0) {
              * pred
            } else {
              self.errors.push(
                (format!("unknown predicate `{}`", id.0), id.1).into()
              ) ;
              self.instance.preds.next_index()
            } ;
            TTerm::P { pred, args: args.into() }
          })
        ) |
        // Just a term.
        do_parse!(
          term: try_call!( self.parse_term(& vars) ) >> (
            TTerm::T(term)
          )
        )
      )
    )
  }

  /// Parses a predicate declaration.
  #[allow(unused_variables)]
  pub fn parse_clause<'b>(
    & mut self, bytes: & 'b [u8]
  ) -> IResult<& 'b [u8], (), InternalParseError> {
    let mut var_name_map = HashMap::<& 'b str, VarIdx>::new() ;
    let mut var_map = VarMap::with_capacity(7) ;
    fix_error!(
      bytes,
      InternalParseError,
      do_parse!(
        err!( char '(', "opening clause's signature" ) >>
        spc_cmt >> vars: many0!(
          do_parse!(
            char!('(') >>
            spc_cmt >> i: with_from_end!( err!(ident) ) >>
            spc_cmt >> t: err!(typ) >>
            spc_cmt >> err!(
              char ')', "closing clause parameter declaration"
            ) >>
            spc_cmt >> ({
              let (name, typ, idx) = (
                i.0.to_string(), t, var_map.next_index()
              ) ;
              let prev = var_name_map.insert(i.0, idx) ;
              if let Some(_) = prev {
                self.errors.push((
                  format!("found two horn clause variables named `{}`", i.0),
                  i.1
                ).into())
              }
              var_map.push( VarInfo { name, typ, idx } )
            })
          )
        ) >>
        spc_cmt >> err!( char ')', "closing clause's signature" ) >>
        spc_cmt >> err!( char '(', "opening clause's left-hand side" ) >>
        spc_cmt >> lhs: many0!(
          terminated!(
            try_call!( self.parse_top_term(& var_name_map) ), spc_cmt
          )
        ) >>
        spc_cmt >> err!( char ')', "closing clause's left-hand side" ) >>
        spc_cmt >> rhs: try_call!(
          self.parse_top_term(& var_name_map)
        ) >> ({
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
        })
      )
    )
  }

  /// Parses some declarations.
  #[allow(unused_variables)]
  pub fn internal_parse_data<'b>(
    & mut self, bytes: & 'b [u8]
  ) -> IResult<& 'b [u8], (), InternalParseError> {
    fix_error!(
      bytes,
      InternalParseError,
      do_parse!(
        spc_cmt >> parsed: many0!(

          // Predicate declaration.
          do_parse!(
            char!('(') >>
            spc_cmt >> alt_complete!(
              do_parse!(
                tag!( ::common::consts::keywords::prd_dec ) >>
                spc_cmt >> pred_info: try_call!( self.parse_dec_pred() ) >> ({
                  let (name, from_end, map) = pred_info ;
                  let pred_index = self.instance.push_pred(
                    name.clone(), VarMap::of(map)
                  ) ;
                  let prev = self.pred_name_map.insert(name, pred_index) ;
                  if let Some(prev) = prev {
                    self.errors.push((
                      format!("predicate `{}` is already declared", prev),
                      from_end
                    ).into())
                  }
                  ()
                })
              ) |

              // Clause.
              do_parse!(
                tag!( ::common::consts::keywords::clause_def ) >>
                spc_cmt >> clause: try_call!( self.parse_clause() ) >>
                (())
              )
            ) >>
            spc_cmt >> err!(
              char ')', "closing predicate declaration or clause"
            ) >>
            spc_cmt >> (())
          )
        ) >>
        ( () )
      )

    )
  }

  /// Parses some declarations and an optional `infer` command.
  #[allow(unused_variables)]
  pub fn internal_parse_all<'b>(
    & mut self, bytes: & 'b [u8]
  ) -> IResult<& 'b [u8], bool, InternalParseError> {
    fix_error!(
      bytes,
      InternalParseError,
      do_parse!(
        try_call!( self.internal_parse_data() ) >>
        spc_cmt >> done: alt_complete!(
          do_parse!(
            char!('(') >>
            spc_cmt >> err!(
              tag!("infer"),
              "expected predicate declaration, clause, or `infer` command"
            ) >>
            spc_cmt >> err!( char ')', "closing `infer` command" ) >>
            (true)
          ) |
          map!( eof!(), |_| false )
        ) >>
        ( done )
      )
    )
  }

  /// Parses some declarations.
  pub fn parse<'b>(
    & mut self, bytes: & 'b [u8]
  ) -> Option<(usize, bool)> {
    match self.internal_parse_all(bytes) {
      IResult::Done( i, done ) => Some( (i.len(), done) ),
      IResult::Error( ::nom::ErrorKind::Custom(err) ) => {
        self.errors.push(err) ;
        None
      },
      e => {
        self.errors.push(
          (format!("unexpected parse result: {:?}", e), bytes).into()
        ) ;
        None
      },
    }
  }



  /// Reduces the instance.
  pub fn reduce(& mut self) -> Res<()> {
    Ok(())
  }
}
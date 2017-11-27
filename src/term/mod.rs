//! Hashconsed terms.
//!
//! # Terms
//!
//! The factory is a `static_ref` for easy creation. The `R`eal term structure
//! is [`RTerm`](enum.RTerm.html) which is hashconsed into
//! [`Term`](type.Term.html). The factory
//! ([`HashConsign`](https://crates.io/crates/hashconsing)) is not directly
//! accessible. Terms are created *via* the functions in this module, such as
//! [var](fn.var.html), [int](fn.int.html), [app](fn.app.html), *etc.*
//!
//! ```
//! # use hoice::term ;
//! # use hoice::term::{ Op, RTerm } ;
//! let some_term = term::eq(
//!   term::int(11), term::app(
//!     Op::Mul, vec![ term::var(5), term::int(2) ]
//!   )
//! ) ;
//! // A `Term` dereferences to an `RTerm`:
//! match * some_term {
//!   RTerm::App { op: Op::Eql, ref args } => {
//!     assert_eq!( args.len(), 2 ) ;
//!     assert_eq!( term::int(11), args[0] ) ;
//!     if let RTerm::App { op: Op::Mul, ref args } = * args[1] {
//!       assert_eq!( term::var(5), args[0] ) ;
//!       assert_eq!( term::int(2), args[1] )
//!     } else { panic!("not a multiplication") }
//!   },
//!   _ => panic!("not an equality"),
//! }
//! ```
//!
//! Terms are not typed at all. A predicate application is **not** a term, only
//! operator applications are.
//!
//! Terms are simplified (when possible) at creation. In particular, the order
//! of the arguments can change, double negations will be simplified, *etc.*
//! See [`normalize`](fn.normalize.html) for more details.
//!
//! # Top-level terms
//!
//! A [`TTerm`](enum.tterm.html) is either a term or a predicate application to
//! some terms. Top-level terms are not hashconsed as they are shallow.
//!
//! # Variables
//!
//! A variable is a `usize` wrapped in a zero-cost
//! [`VarIdx`](../common/struct.VarIdx.html) for safety. It has no semantics at
//! all by itself. Variables are given meaning by
//!
//! - the `sig` field of a [`PrdInfo`](../instance/info/struct.PrdInfo.html),
//!   which gives them types;
//! - the [`VarInfo`s](../instance/info/struct.VarInfo.html) stored in a
//!   [`Clause`](../instance/struct.Clause.html), which give them a name and a
//!   type.

use hashconsing::* ;

use common::* ;

#[macro_use]
mod factory ;
mod val ;
#[cfg(test)]
mod test ;

pub use self::factory::* ;
pub use self::val::Val ;




/// Types.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Typ {
  /// Integers.
  Int,
  /// Booleans.
  Bool,
}
impl Typ {
  /// Default value of a type.
  pub fn default_val(& self) -> Val {
    match * self {
      Typ::Int => Val::I( Int::zero() ),
      Typ::Bool => Val::B( true ),
    }
  }
}
impl ::rsmt2::to_smt::Sort2Smt for Typ {
  fn sort_to_smt2<Writer>(
    & self, w: &mut Writer
  ) -> SmtRes<()> where Writer: Write {
    write!(w, "{}", self) ? ;
    Ok(())
  }
}
impl_fmt!{
  Typ(self, fmt) {
    match * self {
      Typ::Int => fmt.write_str("Int"),
      Typ::Bool => fmt.write_str("Bool"),
    }
  }
}



/// A real term.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum RTerm {
  /// A clause variable.
  Var(VarIdx),
  /// An integer.
  Int(Int),
  /// A boolean.
  Bool(bool),
  /// An operator application.
  App {
    /// The operator.
    op: Op,
    /// The arguments.
    args: Vec<Term>,
  },
}
impl RTerm {
  /// The operator and the kids of a term.
  pub fn app_inspect(& self) -> Option< (Op, & Vec<Term>) > {
    match * self {
      RTerm::App { op, ref args } => Some((op, args)),
      _ => None,
    }
  }
  /// Returns the kid of conjunctions.
  pub fn conj_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::And, ref args } => Some(args),
      _ => None,
    }
  }
  /// Returns the kid of disjunctions.
  pub fn disj_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Or, ref args } => Some(args),
      _ => None,
    }
  }

  /// Write a real term using a special function to write variables.
  pub fn write<W, WriteVar>(
    & self, w: & mut W, write_var: WriteVar
  ) -> IoRes<()>
  where W: Write, WriteVar: Fn(& mut W, VarIdx) -> IoRes<()> {
    let mut stack = vec![
      (vec![self], "", "")
    // ^^^^^^^^^|  ^|  ^^~~~ termination string (written once vector's empty)
    //          |   |~~~~~~~ prefix string      (written before next element)
    //          |~~~~~~~~~~~ elements to write
    ] ;
    while let Some( (mut to_do, sep, end) ) = stack.pop() {
      use self::RTerm::* ;
      if let Some(term) = to_do.pop() {
        stack.push( (to_do, sep, end) ) ;
        match * term {
          Var(v) => {
            write!(w, "{}", sep) ? ;
            write_var(w, v) ?
          },
          Int(ref i) => {
            write!(w, "{}", sep) ? ;
            if i.is_negative() {
              write!(w, "(- {})", - i) ?
            } else {
              write!(w, "{}", i) ?
            }
          },
          Bool(b) => write!(w, "{}{}", sep, b) ?,
          App { op, ref args } => {
            write!(w, "{}({}", sep, op) ? ;
            stack.push(
              (args.iter().rev().map(|t| t.get()).collect(), " ", ")")
            )
          },
        }
      } else { w.write_all( end.as_bytes() ) ? }
    }
    Ok(())
  }

  /// Term evaluation (int).
  pub fn int_eval(& self, model: & VarMap<Val>) -> Res< Option<Int> > {
    self.eval(model)?.to_int()
  }

  /// Term evaluation (bool).
  pub fn bool_eval(& self, model: & VarMap<Val>) -> Res< Option<bool> > {
    self.eval(model)?.to_bool()
  }

  /// True if the term has no variables and evaluates to true.
  ///
  /// ```
  /// use hoice::term ;
  /// use hoice::term::Op ;
  ///
  /// let term = term::tru() ;
  /// println!("true") ;
  /// assert!( term.is_true() ) ;
  /// let term = term::fls() ;
  /// println!("false") ;
  /// assert!( ! term.is_true() ) ;
  /// let term = term::eq(
  ///   term::int(7), term::var(1)
  /// ) ;
  /// println!("7 = v_1") ;
  /// assert!( ! term.is_true() ) ;
  /// let term = term::eq(
  ///   term::int(9), term::int(9)
  /// ) ;
  /// println!("9 = 9") ;
  /// assert!( term.is_true() ) ;
  /// let term = term::eq(
  ///   term::int(1), term::int(9)
  /// ) ;
  /// println!("1 = 9") ;
  /// assert!( ! term.is_true() ) ;
  /// let term = term::le(
  ///   term::app(
  ///     Op::Add, vec![ term::int(3), term::int(4) ]
  ///   ), term::int(9)
  /// ) ;
  /// println!("3 + 4 = 9") ;
  /// assert!( term.is_true() ) ;
  /// ```
  pub fn is_true(& self) -> bool {
    match self.bool_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(b)) => b,
      _ => false,
    }
  }
  
  /// True if the term has no variables and evaluates to true.
  ///
  /// ```
  /// use hoice::term ;
  /// use hoice::term::Op ;
  ///
  /// let term = term::tru() ;
  /// println!("true") ;
  /// assert!( ! term.is_false() ) ;
  /// let term = term::fls() ;
  /// println!("false") ;
  /// assert!( term.is_false() ) ;
  /// let term = term::eq(
  ///   term::int(7), term::var(1)
  /// ) ;
  /// println!("7 = v_1") ;
  /// assert!( ! term.is_false() ) ;
  /// let term = term::eq(
  ///   term::int(9), term::int(9)
  /// ) ;
  /// println!("9 = 9") ;
  /// assert!( ! term.is_false() ) ;
  /// let term = term::eq(
  ///   term::int(1), term::int(9)
  /// ) ;
  /// println!("1 = 9") ;
  /// assert!( term.is_false() ) ;
  /// let term = term::le(
  ///   term::int(9), term::app(
  ///     Op::Add, vec![ term::int(3), term::int(4) ]
  ///   )
  /// ) ;
  /// println!("9 <= 3 + 4") ;
  /// assert!( term.is_false() ) ;
  /// ```
  pub fn is_false(& self) -> bool {
    match self.bool_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(b)) => ! b,
      _ => false,
    }
  }
  /// Boolean a constant boolean term evaluates to.
  pub fn bool(& self) -> Option<bool> {
    match self.bool_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(b)) => Some(b),
      _ => None
    }
  }
  /// Integer a constant integer term evaluates to.
  pub fn int(& self) -> Option<Int> {
    match self.int_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(i)) => Some(i),
      _ => None
    }
  }

  /// The kids of this term, if any.
  pub fn kids(& self) -> Option<& [Term]> {
    if let RTerm::App{ ref args, .. } = * self {
      Some(args)
    } else {
      None
    }
  }
  /// Checks whether the term is a relation.
  pub fn is_relation(& self) -> bool {
    match * self {
      RTerm::App { op: Op::Eql, .. } |
      RTerm::App { op: Op::Gt, .. } |
      RTerm::App { op: Op::Ge, .. } |
      RTerm::App { op: Op::Lt, .. } |
      RTerm::App { op: Op::Le, .. } => true,
      RTerm::App { op: Op::Not, ref args } => args[0].is_relation(),
      _ => false,
    }
  }
  /// Checks whether a term is an equality.
  pub fn is_eq(& self) -> bool {
    match * self {
      RTerm::App { op: Op::Eql, .. } => true,
      _ => false,
    }
  }


  /// Term evaluation.
  pub fn eval(& self, model: & VarMap<Val>) -> Res<Val> {
    use self::RTerm::* ;
    let mut current = self ;
    let mut stack = vec![] ;

    'eval: loop {

      // Go down applications.
      let mut evaled = match * current {
        App { op, ref args } => {
          current = & args[0] ;
          stack.push( (op, & args[1..], vec![]) ) ;
          continue 'eval
        },
        // Rest are leaves, going up.
        Var(v) => if v < model.len() {
          model[v].clone()
        } else {
          bail!("model is too short")
        },
        Int(ref i) => Val::I( i.clone() ),
        Bool(b) => Val::B(b),
      } ;

      // Go up.
      'go_up: loop {
        if let Some( (op, to_do, mut values) ) = stack.pop() {
          if to_do.is_empty() {
            values.push(evaled) ;
            evaled = op.eval(values).chain_err(
              || format!("while evaluating operator `{}`", op)
            ) ? ;
            continue 'go_up
          } else {
            // Going down the first element of `to_do`.
            current = & to_do[0] ;
            values.push(evaled) ;
            stack.push( (op, & to_do[1..], values) ) ;
            // Go down.
            continue 'eval
          }
        } else {
          // We are at the top level, done.
          return Ok(evaled)
        }
      }

    }
  }

  /// If the term's an integer constants, returns the value.
  pub fn int_val(& self) -> Option<Int> {
    if let RTerm::Int(ref i) = * self { Some( i.clone() ) } else { None }
  }

  /// The highest variable index appearing in the term.
  pub fn highest_var(& self) -> Option<VarIdx> {
    let mut to_do = vec![ self ] ;
    let mut max = None ;
    while let Some(term) = to_do.pop() {
      match * term {
        RTerm::Var(i) => max = Some(
          ::std::cmp::max( i, max.unwrap_or(0.into()) )
        ),
        RTerm::Int(_) => (),
        RTerm::Bool(_) => (),
        RTerm::App{ ref args, .. } => for arg in args {
          to_do.push(arg)
        },
      }
    }
    max
  }

  /// All the variables appearing in a term.
  pub fn vars(& self) -> VarSet {
    let mut to_do = vec![ self ] ;
    let mut set = VarSet::with_capacity(11) ;
    while let Some(term) = to_do.pop() {
      match * term {
        RTerm::Var(i) => {
          let _ = set.insert(i) ; ()
        },
        RTerm::Int(_) => (),
        RTerm::Bool(_) => (),
        RTerm::App{ ref args, .. } => for arg in args {
          to_do.push(arg)
        },
      }
    }
    set.shrink_to_fit() ;
    set
  }

  /// Returns the variable index if the term is a variable.
  pub fn var_idx(& self) -> Option<VarIdx> {
    match * self {
      RTerm::Var(i) => Some(i),
      _ => None,
    }
  }

  /// If the term is a negation, returns what's below the negation.
  pub fn rm_neg(& self) -> Option<Term> {
    match * self {
      RTerm::App { op: Op::Not, ref args } => {
        debug_assert_eq!( args.len(), 1 ) ;
        Some( args[0].clone() )
      },
      _ => None,
    }
  }


  /// Turns a real term in a hashconsed one.
  #[inline]
  pub fn to_hcons(& self) -> Term {
    term( self.clone() )
  }



  /// Variable substitution.
  ///
  /// The `total` flag causes substitution to fail if a variable that's not in
  /// `map`.
  ///
  /// The boolean returned is true if at least on substitution occured.
  pub fn subst_custom<Map: VarIndexed<Term>>(
    & self, map: & Map, total: bool
  ) -> Option<(Term, bool)> {
    let mut current = & self.to_hcons() ;
    // Stack for traversal.
    let mut stack = vec![] ;
    // Number of substitutions performed.
    let mut subst_count = 0 ;

    'go_down: loop {

      // Go down.
      let mut term = match * current.get() {
        RTerm::Var(var) => if let Some(term) = map.var_get(var) {
          subst_count += 1 ;
          term.clone()
        } else if total {
          return None
        } else {
          current.clone()
        },
        RTerm::App { op, ref args } => {
          current = & args[0] ;
          stack.push(
            (op, & args[1..], Vec::with_capacity( args.len() ))
          ) ;
          continue 'go_down
        },
        _ => current.clone(),
      } ;

      // Go up.
      'go_up: while let Some(
        (op, args, mut new_args)
      ) = stack.pop() {
        new_args.push( term ) ;
        
        if args.is_empty() {
          term = app(op, new_args) ;
          continue 'go_up // Just for readability
        } else {
          current = & args[0] ;
          stack.push( (op, & args[1..], new_args) ) ;
          continue 'go_down
        }
      }

      // Only way to get here is if the stack is empty, meaning we're done.
      return Some( (term, subst_count > 0) )
    }
  }

  /// Variable substitution.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occured.
  ///
  /// Used for substitutions in the same clause / predicate scope.
  #[inline]
  pub fn subst<Map: VarIndexed<Term>>(
    & self, map: & Map
  ) -> (Term, bool) {
    self.subst_custom(map, false).expect("total substitution can't fail")
  }

  /// Fixed-point (partial) variable substitution.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occured.
  pub fn subst_fp<Map: VarIndexed<Term>>(
    & self, map: & Map
  ) -> (Term, bool) {
    let (mut term, mut changed) = self.subst(map) ;
    while changed {
      let (new_term, new_changed) = term.subst(map) ;
      term = new_term ;
      changed = new_changed
    }
    (term, changed)
  }

  /// Total variable substition, returns `None` if there was a variable in the
  /// term that was not in the map.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occsured.
  ///
  /// Used for substitutions between different same clause / predicate scopes.
  pub fn subst_total<Map: VarIndexed<Term>>(
    & self, map: & Map
  ) -> Option< (Term, bool) > {
    self.subst_custom(map, true)
  }



  /// Attempts to invert a term.
  ///
  /// More precisely, if the term only mentions one variable `v`, attempts to
  /// find a `f` that's a solution of `var = term <=> v = f(var)`.
  ///
  /// Currently, only works when `v` appears exactly once. That is, it will
  /// fail on `var = 3.v + 7.v` for instance. (This would be fine if
  /// normalization handled this kind cases though.)
  ///
  /// Also, only works when all operators are binary (expect for unary minus).
  ///
  /// ```
  /// use hoice::term ;
  ///
  /// let term = term::u_minus( term::var(0) ) ;
  /// assert_eq!{
  ///   term.invert( 1.into() ),
  ///   Some( (0.into(), term::u_minus( term::var(1) ) ) )
  /// }
  /// let term = term::sub( vec![ term::var(0), term::int(7) ] ) ;
  /// assert_eq!{
  ///   term.invert( 1.into() ),
  ///   Some( (0.into(), term::add( vec![ term::var(1), term::int(7) ] ) ) )
  /// }
  /// let term = term::add( vec![ term::int(7), term::var(0) ] ) ;
  /// assert_eq!{
  ///   term.invert( 1.into() ),
  ///   Some( (0.into(), term::sub( vec![ term::var(1), term::int(7) ] ) ) )
  /// }
  /// ```
  pub fn invert(& self, var: VarIdx) -> Option<(VarIdx, Term)> {
    let mut solution = term::var(var) ;
    let mut term = self ;

    loop {
      match * term {
        RTerm::App { op, ref args } => {
          let (po, symmetric) = match op {
            Op::Add => (Op::Sub, true),
            Op::Sub if args.len() == 1 => {
              solution = term::u_minus( solution ) ;
              term = & args[0] ;
              continue
            },
            Op::Sub => (Op::Add, false),
            Op::Div => (Op::Mul, false),
            Op::Mul => (Op::Div, true),
            _ => return None,
          } ;
          if args.len() != 2 { return None }

          if let Some(i) = args[0].int() {
            if symmetric {
              solution = term::app( po, vec![ solution, term::int(i) ] )
            } else {
              solution = term::app( op, vec![ term::int(i), solution ] )
            }
            term = & args[1]
          } else if let Some(i) = args[1].int() {
            solution = term::app( po, vec![ solution, term::int(i) ] ) ;
            term = & args[0]
          } else {
            return None
          }
        },
        RTerm::Var(v) => return Some((v, solution)),
        _ => return None,
      }
    }
  }


}
impl_fmt!{
  RTerm(self, fmt) {
    let mut buf = Vec::with_capacity(250) ;
    self.write(& mut buf, |w, var| var.default_write(w)).expect(
      "fatal error during real term pretty printing"
    ) ;
    let s = ::std::str::from_utf8(& buf).expect(
      "fatal error during real term pretty printing"
    ) ;
    write!(fmt, "{}", s)
  }
}
impl<'a> PebcakFmt<'a> for RTerm {
  type Info = & 'a VarMap< ::instance::info::VarInfo > ;
  fn pebcak_err(& self) -> ErrorKind {
    "during term pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, vars: & 'a VarMap< ::instance::info::VarInfo >
  ) -> IoRes<()> {
    self.write(
      w, |w, var| w.write_all( vars[var].as_bytes() )
    )
  }
}




/// Hash consed term.
pub type Term = HConsed<RTerm> ;




/// Top term, as they appear in clauses.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TTerm {
  /// A predicate application.
  P {
    /// Predicate applied.
    pred: PrdIdx,
    /// The arguments.
    args: VarMap<Term>,
  },
  /// Just a term.
  T(Term),
}
impl TTerm {
  /// The false top term.
  pub fn fls() -> Self {
    TTerm::T( term::fls() )
  }

  /// True if the top term is a term with no variables and evaluates to true.
  pub fn is_true(& self) -> bool {
    self.bool() == Some(true)
  }
  /// True if the top term is a term with no variables and evaluates to false.
  pub fn is_false(& self) -> bool {
    self.bool() == Some(false)
  }
  /// Boolean corresponding to the top term if it's a bool constant.
  pub fn bool(& self) -> Option<bool> {
    match * self {
      TTerm::T(ref t) => t.bool(),
      _ => None,
    }
  }
  /// Boolean corresponding to the top term if it's an integer constant.
  pub fn int(& self) -> Option<Int> {
    match * self {
      TTerm::T(ref t) => t.int(),
      _ => None,
    }
  }
  /// The operator and the kids of a top term, if it's an operator application.
  pub fn app_inspect(& self) -> Option< (Op, & Vec<Term>) > {
    match * self {
      TTerm::T(ref t) => t.app_inspect(),
      _ => None,
    }
  }
  /// If the top term is simply a term, returns that term.
  #[inline]
  pub fn term(& self) -> Option<& Term> {
    if let TTerm::T(ref t) = * self { Some(t) } else { None }
  }

  /// The predicate a top term is an application of, if any.
  pub fn pred(& self) -> Option<PrdIdx> {
    match * self {
      TTerm::P { pred, .. } => Some(pred),
      _ => None,
    }
  }

  /// The arguments of a top term if it's a predicate application.
  pub fn args(& self) -> Option<& VarMap<Term>> {
    match * self {
      TTerm::P { ref args, .. } => Some(args),
      _ => None,
    }
  }

  /// Variables appearing in a top term.
  pub fn vars(& self) -> VarSet {
    match * self {
      TTerm::P { ref args, .. } => {
        use std::iter::Extend ;
        let mut vars = VarSet::with_capacity(17) ;
        for term in args {
          vars.extend( term.vars() )
        }
        vars
      },
      TTerm::T(ref term) => term.vars(),
    }
  }

  /// In-place variable substitution for top terms.
  ///
  /// Used for substitutions in the same clause / predicate scope.
  pub fn subst<Map: VarIndexed<Term>>(
    & mut self, map: & Map
  ) -> bool {
    match * self {
      TTerm::T(ref mut term) => {
        let (t, b) = term.subst(map) ;
        * term = t ;
        b
      },
      TTerm::P { ref mut args, .. } => {
        let mut changed = false ;
        for arg in args.iter_mut() {
          let (t, b) = arg.subst(map) ;
          * arg = t ;
          changed = changed || b
        }
        changed
      },
    }
  }

  /// Total variable substitution for top terms.
  ///
  /// Used for substitutions in different clause / predicate scope.
  pub fn subst_total<Map: VarIndexed<Term>>(
    & self, map: & Map
  ) -> Res<TTerm> {
    match * self {
      TTerm::P { pred, ref args } => {
        let mut new_args = VarMap::with_capacity( args.len() ) ;
        for term in args {
          if let Some((term, _)) = term.subst_total(map) {
            new_args.push(term)
          } else {
            bail!("total substitution failed (predicate)")
          }
        }
        Ok( TTerm::P { pred, args: new_args } )
      },
      TTerm::T(ref term) => if let Some((term, _)) = term.subst_total(map) {
        Ok( TTerm::T(term) )
      } else {
        bail!("total substitution failed (term)")
      },
    }
  }

  /// Writes a top term using special functions for writing predicates and
  /// variables.
  pub fn write<W, WriteVar, WritePrd>(
    & self, w: & mut W, write_var: WriteVar, write_prd: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WriteVar: Fn(& mut W, VarIdx) -> IoRes<()>,
  WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    use self::TTerm::* ;
    match * self {
      P { pred, ref args } => write_prd(w, pred, args),
      T(ref t) => t.write(w, write_var),
    }
  }

  /// Writes a top term smt2 style using a special function for writing
  /// predicates.
  pub fn write_smt2<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    self.write(
      w, |w, var| var.default_write(w), write_prd
    )
  }
}
impl_fmt!{
  TTerm(self, fmt) {
    match * self {
      TTerm::P { pred, ref args } => {
        write!(fmt, "(p_{}", pred) ? ;
        for arg in args {
          write!(fmt, " {}", arg) ?
        }
        write!(fmt, ")")
      },
      TTerm::T(ref t) => write!(fmt, "{}", t),
    }
  }
}


/// Either true, false, a conjunction or a disjunction of top terms.
#[derive(Clone, PartialEq, Eq)]
pub enum TTerms {
  /// True.
  True,
  /// False.
  False,
  /// Conjunction.
  And( Vec<TTerm> ),
  /// Disjunction.
  Or { pos: Vec<TTerm>, neg: Vec<TTerm> },
  /// Almost a DNF: a disjunction of conjunctions of `TTerm`s.
  ///
  /// Quantified variables are quantified **existentially**.
  Dnf( Vec< (Quantfed, Vec<TTerm>) > ),
}
impl TTerms {
  /// True.
  #[inline]
  pub fn tru() -> Self { TTerms::True }
  /// True?
  #[inline]
  pub fn is_tru(& self) -> bool { * self == TTerms::True }
  /// False.
  #[inline]
  pub fn fls() -> Self { TTerms::False }
  /// False?
  #[inline]
  pub fn is_fls(& self) -> bool { * self == TTerms::False }
  /// Constructor from a boolean.
  #[inline]
  pub fn of_bool(b: bool) -> Self {
    if b { Self::tru() } else { Self::fls() }
  }
  /// Boolean value if `True` or `False`.
  #[inline]
  pub fn bool(& self) -> Option<bool> {
    match * self {
      TTerms::True => Some(true),
      TTerms::False => Some(false),
      _ => None,
    }
  }

  /// Simplifies some top terms given some definitions for the predicates.
  pub fn simplify_pred_apps<'a>(& self, model: & 'a Model) -> Self {
    macro_rules! def_of {
      ($pred:ident in $model:expr) => ({
        let mut res = None ;
        for & (ref idx, _, ref tterms) in $model {
          if * idx == $pred { res = Some(tterms) }
        }
        res
      })
    }
    match * self {
      TTerms::True |
      TTerms::False => self.clone(),
      TTerms::And(ref tterms) => {
        let mut nu_tterms = Vec::with_capacity( tterms.len() ) ;
        for tterm in tterms {
          if let Some(pred) = tterm.pred() {
            match def_of!(pred in model).and_then(|t| t.bool()) {
              Some(true) => continue,
              Some(false) => return TTerms::False,
              None => (),
            }
          }
          nu_tterms.push( tterm.clone() )
        }
        Self::conj(nu_tterms)
      },
      TTerms::Or { ref pos, ref neg } => {
        let (mut nu_pos, mut nu_neg) = (
          Vec::with_capacity( pos.len() ), Vec::with_capacity( neg.len() )
        ) ;
        for tterm in pos {
          if let Some(pred) = tterm.pred() {
            match def_of!(pred in model).and_then(|t| t.bool()) {
              Some(false) => continue,
              Some(true) => return TTerms::True,
              None => (),
            }
          }
          nu_pos.push( tterm.clone() )
        }
        for tterm in neg {
          if let Some(pred) = tterm.pred() {
            match def_of!(pred in model).and_then(|t| t.bool()) {
              Some(true) => continue,
              Some(false) => return TTerms::True,
              None => (),
            }
          }
          nu_neg.push( tterm.clone() )
        }
        nu_pos.shrink_to_fit() ;
        nu_neg.shrink_to_fit() ;
        Self::disj(nu_pos, nu_neg)
      },
      TTerms::Dnf(ref disj) => {
        let mut nu_disj = Vec::with_capacity( disj.len() ) ;
        'build_disj: for & (ref qvars, ref conj) in disj {
          let mut nu_conj = Vec::with_capacity( conj.len() ) ;
          'build_conj: for tterm in conj {
            if let Some(pred) = tterm.pred() {
              match def_of!(pred in model).and_then(|t| t.bool()) {
                Some(true) => continue 'build_conj,
                Some(false) => continue 'build_disj,
                None => (),
              }
            }
            nu_conj.push( tterm.clone() )
          }
          nu_disj.push( (qvars.clone(), nu_conj) )
        }
        Self::dnf(nu_disj)
      },
    }
  }

  /// True if the top terms contain an application of `pred`.
  pub fn mention_pred(& self, pred: PrdIdx) -> bool {
    match * self {
      TTerms::And(ref tterms) => for tterm in tterms {
        if let Some(p) = tterm.pred() {
          if p == pred { return true }
        }
      },
      TTerms::Or { ref pos, ref neg } => for tterm in pos.iter().chain(
        neg.iter()
      ) {
        if let Some(p) = tterm.pred() {
          if p == pred { return true }
        }
      },
      TTerms::Dnf( ref disj ) => for & (_, ref conj) in disj {
        for tterm in conj {
          if tterm.pred() == Some(pred) {
            return true
          }
        }
      },
      TTerms::True | TTerms::False => (),
    }
    false
  }

  /// Constructor for a single top term.
  #[inline]
  pub fn of_tterm(tterm: TTerm) -> Self {
    if tterm.is_true() {
      TTerms::True
    } else if tterm.is_false() {
      TTerms::False
    } else {
      TTerms::And( vec![tterm] )
    }
  }
  /// Constructor for a conjunction.
  #[inline]
  pub fn conj(mut tterms: Vec<TTerm>) -> Self {
    let mut cnt = 0 ;
    while cnt < tterms.len() {
      match tterms[cnt].bool() {
        Some(true) => { tterms.swap_remove(cnt) ; },
        Some(false) => return TTerms::fls(),
        None => cnt += 1,
      }
    }
    if tterms.is_empty() {
      TTerms::tru()
    } else {
      TTerms::And(tterms)
    }
  }
  /// Constructor for a disjunction.
  #[inline]
  pub fn disj(mut pos: Vec<TTerm>, mut neg: Vec<TTerm>) -> Self {
    let mut cnt = 0 ;
    while cnt < pos.len() {
      match pos[cnt].bool() {
        Some(true) => return TTerms::tru(),
        Some(false) => { pos.swap_remove(cnt) ; },
        None => cnt += 1,
      }
    }
    while cnt < neg.len() {
      match neg[cnt].bool() {
        Some(false) => return TTerms::tru(),
        Some(true) => { neg.swap_remove(cnt) ; },
        None => cnt += 1,
      }
    }
    if pos.len() + neg.len() == 0 {
      TTerms::fls()
    } else if pos.len() == 1 && neg.len() == 0 {
      TTerms::And(pos)
    } else {
      TTerms::Or { pos, neg }
    }
  }
  /// Constructor for a DNF.
  #[inline]
  pub fn dnf(mut disj: Vec< (Quantfed, Vec<TTerm>) >) -> Self {
    if disj.is_empty() { return TTerms::fls() }
    if disj.len() == 1 && disj[0].0.is_empty() {
      let (_, conj) = disj.pop().unwrap() ;
      return Self::conj(conj)
    }
    let mut disj_cnt = 0 ;
    'disj: while disj_cnt < disj.len() {
      let mut conj_cnt = 0 ;
      'conj: while conj_cnt < disj[disj_cnt].1.len() {
        if let Some(b) = disj[disj_cnt].1[conj_cnt].bool() {
          if b {
            disj[disj_cnt].1.swap_remove(conj_cnt) ;
            continue 'conj
          } else {
            disj.swap_remove(disj_cnt) ;
            continue 'disj
          }
        } else {
          conj_cnt += 1
        }
      }
      if disj[disj_cnt].1.is_empty() {
        // Everyting was true, dnf is trivially true.
        return TTerms::True
      } else {
        disj_cnt += 1
      }
    }
    if disj.is_empty() {
      TTerms::False
    } else {
      TTerms::Dnf(disj)
    }
  }

  /// The predicates appearing in some top terms.
  pub fn preds(& self) -> PrdSet {
    let mut set = PrdSet::new() ;
    match * self {
      TTerms::And(ref tterms) => for tterm in tterms {
        if let Some(pred) = tterm.pred() { set.insert(pred) ; }
      },
      TTerms::Or { ref pos, ref neg } => for tterm in pos.iter().chain(
        neg.iter()
      ) {
        if let Some(pred) = tterm.pred() { set.insert(pred) ; }
      },
      TTerms::Dnf( ref disj ) => for & (_, ref conj) in disj {
        for tterm in conj {
          if let Some(pred) = tterm.pred() {
            set.insert(pred) ;
          }
        }
      },
      TTerms::True | TTerms::False => (),
    }
    set
  }

  /// Total variable substitution for top terms.
  ///
  /// Used for substitutions in different clause / predicate scope.
  pub fn subst_total<Map: VarIndexed<Term>>(
    & self, map: & Map
  ) -> Res<TTerms> {
    match * self {
      TTerms::And(ref tterms) => {
        let mut nu_tterms = Vec::with_capacity( tterms.len() ) ;
        for tterm in tterms {
          let tterm = tterm.subst_total(map) ? ;
          if let Some(b) = tterm.bool() {
            if ! b { return Ok( Self::fls() ) }
          } else {
            nu_tterms.push(tterm)
          }
        }
        if nu_tterms.is_empty() {
          Ok( TTerms::tru() )
        } else {
          Ok( TTerms::And(nu_tterms) )
        }
      },
      TTerms::Or { ref pos, ref neg } => {
        let mut nu_pos = Vec::with_capacity( pos.len() ) ;
        for tterm in pos {
          let tterm = tterm.subst_total(map) ? ;
          nu_pos.push( tterm )
        }
        let mut nu_neg = Vec::with_capacity( neg.len() ) ;
        for tterm in neg {
          let tterm = tterm.subst_total(map) ? ;
          nu_neg.push( tterm )
        }
        Ok( Self::disj(nu_pos, nu_neg) )
      },
      TTerms::Dnf(ref disj) => {
        let mut nu_disj = Vec::with_capacity( disj.len() ) ;
        for & (ref qvars, ref conj) in disj {
          let mut nu_conj = Vec::with_capacity( conj.len() ) ;
          for tterm in conj {
            nu_conj.push( tterm.subst_total(map) ? )
          }
          nu_disj.push( (qvars.clone(), nu_conj) )
        }
        Ok( Self::dnf(nu_disj) )
      },
      TTerms::True | TTerms::False => Ok( self.clone() ),
    }
  }

  /// Writes some top terms using special functions for writing predicates and
  /// variables.
  pub fn write<W, WriteVar, WritePrd>(
    & self, w: & mut W, write_var: WriteVar, write_prd: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WriteVar: Fn(& mut W, VarIdx) -> IoRes<()>,
  WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    match * self {
      TTerms::True => return write!(w, "true"),
      TTerms::False => return write!(w, "false"),
      TTerms::And(ref tterms) if tterms.len() > 1 => {
        write!(w, "(and") ? ;
        for tterm in tterms {
          write!(w, " ") ? ;
          tterm.write(w, & write_var, & write_prd) ?
        }
        write!(w, ")")
      },
      TTerms::And(ref tterms) => tterms[0].write(
        w, & write_var, & write_prd
      ),
      TTerms::Or { ref pos, ref neg } => {
        write!(w, "(or") ? ;
        for tterm in pos {
          write!(w, " ") ? ;
          tterm.write(w, & write_var, & write_prd) ?
        }
        for tterm in neg {
          write!(w, " (not ") ? ;
          tterm.write(w, & write_var, & write_prd) ? ;
          write!(w, ")") ?
        }
        write!(w, ")")
      },
      TTerms::Dnf(ref disj) => {
        write!(w, "(or ") ? ;
        for & (ref qvars, ref conj) in disj {
          let suff = if qvars.is_empty() { "" } else {
            write!(w, "(exists (") ? ;
            for (var, typ) in qvars {
              write!(w, " ({} {})", var.default_str(), typ) ?
            }
            write!(w, " )") ? ;
            ")"
          } ;
          write!(w, " (and") ? ;
          for tterm in conj {
            write!(w, " ") ? ;
            tterm.write(w, & write_var, & write_prd) ?
          }
          write!(w, "){}", suff) ?
        }
        write!(w, ")")
      },
    }
  }

  /// Writes some top terms smt2 style using a special function for writing
  /// predicates.
  pub fn write_smt2<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    self.write(
      w, |w, var| var.default_write(w), write_prd
    )
  }
}


impl_fmt!{
  TTerms(self, fmt) {
    match * self {
      TTerms::True => return write!(fmt, "true"),
      TTerms::False => return write!(fmt, "false"),
      TTerms::And(ref tterms) => {
        write!(fmt, "(and") ? ;
        for tterm in tterms {
          write!(fmt, " ") ? ;
          tterm.fmt(fmt) ?
        }
        write!(fmt, ")")
      },
      TTerms::Or { ref pos, ref neg } => {
        write!(fmt, "(or") ? ;
        for tterm in pos {
          write!(fmt, " ") ? ;
          tterm.fmt(fmt) ?
        }
        for tterm in neg {
          write!(fmt, " (not ") ? ;
          tterm.fmt(fmt) ? ;
          write!(fmt, ")") ?
        }
        write!(fmt, ")")
      },
      TTerms::Dnf(ref disj) => {
        write!(fmt, "(or ") ? ;
        for & (ref qvars, ref conj) in disj {
          let suff = if qvars.is_empty() { "" } else {
            write!(fmt, "(exists (") ? ;
            for (var, typ) in qvars {
              write!(fmt, " ({} {})", var.default_str(), typ) ?
            }
            write!(fmt, " )") ? ;
            " )"
          } ;
          write!(fmt, " (and") ? ;
          for tterm in conj {
            write!(fmt, " ") ? ;
            tterm.fmt(fmt) ?
          }
          write!(fmt, "){}", suff) ?
        }
        write!(fmt, ")")
      },
    }
  }
}

impl<'a, 'b> ::rsmt2::to_smt::Expr2Smt<
  & 'b (& 'a PrdSet, & 'a PrdSet, & 'a PrdMap< ::instance::info::PrdInfo >)
> for TTerms {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, info: & 'b (
      & 'a PrdSet, & 'a PrdSet, & 'a PrdMap<::instance::info::PrdInfo>
    )
  ) -> SmtRes<()> {
    let (true_preds, false_preds, pred_info) = * info ;
    self.write_smt2(
      w, |w, pred, args| {
        if true_preds.contains(& pred) {
          write!(w, "true")
        } else if false_preds.contains(& pred) {
          write!(w, "false")
        } else {
          write!(w, "({}", pred_info[pred]) ? ;
          for arg in args {
            write!(w, " ") ? ;
            arg.write(w, |w, var| var.default_write(w)) ?
          }
          write!(w, ")")
        }
      }
    ) ? ;
    Ok(())
  }
}









/// Operators.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Op {
  /// Addition.
  Add,
  /// Subtraction.
  Sub,
  /// Multiplication.
  Mul,
  /// Division.
  Div,
  /// Modulo.
  Mod,
  /// Greater than.
  Gt,
  /// Greater than or equal to.
  Ge,
  /// Less than or equal to.
  Le,
  /// Less than.
  Lt,
  /// Implication.
  Impl,
  /// Equal to.
  Eql,
  /// Negation.
  Not,
  /// Conjunction.
  And,
  /// Disjunction.
  Or,
  /// If-then-else.
  Ite,
}
impl Op {
  /// String representation.
  pub fn as_str(& self) -> & str {
    use self::Op::* ;
    match * self {
      Add => "+", Sub => "-", Mul => "*", Div => "div", Mod => "mod",
      Gt => ">", Ge => ">=", Le => "<=", Lt => "<", Eql => "=",
      Not => "not", And => "and", Or => "or", Impl => "=>", Ite => "ite"
    }
  }


  /// Evaluation.
  pub fn eval(& self, mut args: Vec<Val>) -> Res<Val> {
    use term::Op::* ;
    if args.is_empty() {
      bail!("evaluating operator on 0 elements")
    }
    match * self {
      Add => {
        let mut res ;
        for_first!{
          args.into_iter() => {
            |fst| res = try_val!(int fst),
            then |nxt| res = res + try_val!(int nxt),
            yild Ok( Val::I(res) )
          } else unreachable!()
        }
      },
      Sub => if args.len() == 1 {
        Ok(
          Val::I(
            - try_val!( int args.pop().unwrap() )
          )
        )
      } else {
        let mut res ;
        for_first!{
          args.into_iter() => {
            |fst| res = try_val!(int fst),
            then |nxt| res = res - try_val!(int nxt),
            yild Ok( Val::I(res) )
          } else unreachable!()
        }
      },
      Mul => {
        let mut unknown = false ;
        let mut res: Int = 1.into() ;
        for arg in args.into_iter() {
          if let Some(i) = arg.to_int() ? {
            if i.is_zero() {
              return Ok( 0.into() )
            } else {
              res = res * i
            }
          } else {
            unknown = true
          }
        }
        if unknown { Ok(Val::N) } else { Ok(Val::I(res)) }
      },
      Div => {
        if args.len() != 2 {
          bail!("unexpected division over {} numbers", args.len())
        }
        let den = try_val!( int args.pop().unwrap() ) ;
        let num = try_val!( int args.pop().unwrap() ) ;
        if den.is_zero() {
          bail!("denominator is zero...")
        }
        let mut res = & num / & den ;
        use num::Signed ;
        if num.is_positive() ^ den.is_positive() {
          if den * & res != num {
            res = res - 1
          }
        }
        Ok( Val::I(res) )
      },

      Mod => if args.len() != 2 {
        bail!(
          format!("evaluating `Div` with {} (!= 2) arguments", args.len())
        )
      } else {
        use num::Integer ;
        let b = try_val!( int args.pop().unwrap() ) ;
        if b == 1.into() {
          Ok( 0.into() )
        } else {
          let a = try_val!( int args.pop().unwrap() ) ;
          Ok( Val::I( a.mod_floor(& b) ) )
        }
      },

      // Bool operators.

      Gt => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last > nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },

      Ge => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last >= nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },

      Le => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last <= nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },

      Lt => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last < nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },

      Eql => {
        let mem ;
        let mut res = true ;
        for_first!{
          args.into_iter() => {
            |fst| mem = fst,
            then |nxt| {
              if ! mem.same_type( & nxt ) {
                return Ok(Val::N)
              }
              if mem != nxt {
                res = false
              }
            },
          } else unreachable!()
        }
        Ok( Val::B(res) )
      },

      Not => if args.len() != 1 {
        bail!(
          format!("evaluating `Not` with {} (!= 1) arguments", args.len())
        )
      } else {
        if let Some(b) = args.pop().unwrap().to_bool() ? {
          Ok( Val::B(! b) )
        } else {
          Ok(Val::N)
        }
      },

      And => {
        let mut unknown = false ;
        for arg in args {
          match arg.to_bool() ? {
            Some(false) => return Ok( Val::B(false) ),
            None => unknown = true,
            _ => ()
          }
        }
        if unknown {
          Ok( Val::N )
        } else {
          Ok( Val::B(true) )
        }
      },

      Or => {
        let mut unknown = false ;
        for arg in args {
          match arg.to_bool() ? {
            Some(true) => return Ok( Val::B(true) ),
            None => unknown = true,
            _ => ()
          }
        }
        if unknown {
          Ok( Val::N )
        } else {
          Ok( Val::B(false) )
        }
      },

      Impl => if args.len() != 2 {
        bail!(
          format!("evaluating `Impl` with {} (!= 2) arguments", args.len())
        )
      } else {
        // Safe because of the check above.
        let rhs = args.pop().unwrap() ;
        let lhs = args.pop().unwrap() ;
        match ( lhs.to_bool() ?, rhs.to_bool() ? ) {
          (_, Some(true)) | (Some(false), _) => Ok( Val::B(true) ),
          (Some(lhs), Some(rhs)) => Ok( Val::B(rhs || ! lhs) ),
          _ => Ok(Val::N),
        }
      },

      Ite => if args.len() != 3 {
        bail!(
          format!("evaluating `Ite` with {} (!= 3) arguments", args.len())
        )
      } else {
        let (els, thn, cnd) = (
          args.pop().unwrap(), args.pop().unwrap(), args.pop().unwrap()
        ) ;
        match cnd.to_bool() ? {
          Some(true) => Ok(thn),
          Some(false) => Ok(els),
          _ => Ok(Val::N),
        }
      }

    }
  }
}
impl_fmt!{
  Op(self, fmt) {
    fmt.write_str( self.as_str() )
  }
}



/// Existential or universal qualifier.
///
/// Always use the constructors to avoid falsifying the invariant.
///
/// # Invariant
///
/// The variable partial maps are never empty.
#[derive(Clone)]
pub enum Qualf {
  /// Exists.
  Exists( VarHMap<Typ> ),
  /// Forall.
  Forall( VarHMap<Typ> ),
}
impl Qualf {
  /// Creates an existential qualifier.
  pub fn exists(map: VarHMap<Typ>) -> Option<Self> {
    if map.is_empty() { None } else { Some( Qualf::Exists(map) ) }
  }
  /// Creates an existential qualifier.
  pub fn forall(map: VarHMap<Typ>) -> Option<Self> {
    if map.is_empty() { None } else { Some( Qualf::Forall(map) ) }
  }

  /// Number of quantified variables.
  pub fn len(& self) -> usize {
    let map = match * self {
      Qualf::Exists(ref map) => map,
      Qualf::Forall(ref map) => map,
    } ;
    debug_assert! { ! map.is_empty() }
    map.len()
  }

  /// Writes the opening part of the qualifier as a line.
  ///
  /// Basically `"{}(<quantified> ( <qvars> )\n", prefix`.
  pub fn write_pref<W, WVar>(
    & self, w: & mut W, pref: & str, write_var: WVar
  ) -> IoRes<()>
  where
  W: Write, WVar: Fn(& mut W, VarIdx) -> IoRes<()> {
    w.write( pref.as_bytes() ) ? ;
    let map = match * self {
      Qualf::Exists(ref map) => {
        write!(w, "(exists (") ? ;
        map
      },
      Qualf::Forall(ref map) => {
        write!(w, "(forall (") ? ;
        map
      },
    } ;
    for (var, typ) in map {
      write!(w, " (") ? ;
      write_var(w, * var) ? ;
      write!(w, " {})", typ) ?
    }
    writeln!(w, " )")
  }
}



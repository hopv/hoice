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
//!
//! # Examples
//!
//! ```rust
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
#[
  derive(
    Debug, Clone, Copy,
    PartialEq, Eq, Hash,
    PartialOrd, Ord
  )
]
pub enum Typ {
  /// Integers.
  Int,
  /// Reals.
  Real,
  /// Booleans.
  Bool,
}
impl Typ {
  /// Default value of a type.
  pub fn default_val(& self) -> Val {
    match * self {
      Typ::Int => Val::I( Int::zero() ),
      Typ::Real => Val::R(
        Rat::new( Int::zero(), Int::one() )
      ),
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
      Typ::Real => fmt.write_str("Real"),
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
  /// A real (actually a rational).
  Real(Rat),
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
  /// Returns the kids of conjunctions.
  pub fn conj_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::And, ref args } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of disjunctions.
  pub fn disj_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Or, ref args } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of equalities.
  pub fn eq_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Eql, ref args } => Some(args),
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
    // ^^^^^^^^^|  ^^| ^^~~~ termination string (written once vector's empty)
    //          |    |~~~~~~ prefix string      (written before next element)
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
            int_to_smt!(w, i) ?
          },
          Real(ref r) => {
            write!(w, "{}", sep) ? ;
            rat_to_smt!(w, r) ?
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
  pub fn int_eval<E: Evaluator>(
    & self, model: & E
  ) -> Res< Option<Int> > {
    self.eval(model)?.to_int()
  }

  /// Term evaluation (bool).
  pub fn bool_eval<E: Evaluator>(
    & self, model: & E
  ) -> Res< Option<bool> > {
    self.eval(model)?.to_bool()
  }

  /// True if the term has no variables and evaluates to true.
  ///
  /// # Examples
  ///
  /// ```rust
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
    match self.bool_eval( & () ) {
      Ok(Some(b)) => b,
      _ => false,
    }
  }
  
  /// True if the term has no variables and evaluates to true.
  ///
  /// # Examples
  ///
  /// ```rust
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
    match self.bool_eval( & () ) {
      Ok(Some(b)) => ! b,
      _ => false,
    }
  }
  /// Boolean a constant boolean term evaluates to.
  pub fn bool(& self) -> Option<bool> {
    match self.bool_eval( & () ) {
      Ok(Some(b)) => Some(b),
      _ => None
    }
  }
  /// Integer a constant integer term evaluates to.
  pub fn int(& self) -> Option<Int> {
    match self.int_eval( & () ) {
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
  /// True if this term is known to have type bool.
  pub fn has_type_bool(
    & self, vars: & VarMap<::instance::info::VarInfo>
  ) -> bool {
    match * self {
      RTerm::App { op: Op::Eql, .. } |
      RTerm::App { op: Op::And, .. } |
      RTerm::App { op: Op::Or, .. } |
      RTerm::App { op: Op::Impl, .. } |
      RTerm::App { op: Op::Gt, .. } |
      RTerm::App { op: Op::Ge, .. } |
      RTerm::App { op: Op::Lt, .. } |
      RTerm::App { op: Op::Le, .. } => true,
      RTerm::App { op: Op::Not, ref args } => args[0].has_type_bool(vars),
      RTerm::App { op: Op::Ite, ref args } => args[1].has_type_bool(vars),
      RTerm::Var(idx) => vars[idx].typ == Typ::Bool,
      RTerm::Bool(_) => true,
      _ => false,
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
  pub fn eval<E: Evaluator>(& self, model: & E) -> Res<Val> {
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
          model.get(v).clone()
        } else {
          bail!("model is too short")
        },
        Int(ref i) => Val::I( i.clone() ),
        Real(ref r) => Val::R( r.clone() ),
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

  /// If the term's an integer constant, returns the value.
  pub fn int_val(& self) -> Option<& Int> {
    if let RTerm::Int(ref i) = * self { Some( i ) } else { None }
  }
  /// If the term's a rational constant, returns the value.
  pub fn rat_val(& self) -> Option<& Rat> {
    if let RTerm::Real(ref r) = * self { Some( r ) } else { None }
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
        RTerm::Int(_) |
        RTerm::Real(_) |
        RTerm::Bool(_) => (),
        RTerm::App{ ref args, .. } => for arg in args {
          to_do.push(arg)
        },
      }
    }
    max
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
          term
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
  /// # Examples
  ///
  /// ```rust
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
            Op::IDiv => (Op::Mul, false),
            Op::Mul => (Op::IDiv, true),
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
    args: TArgs,
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
  pub fn args(& self) -> Option<& TArgs> {
    match * self {
      TTerm::P { ref args, .. } => Some(args),
      _ => None,
    }
  }

  /// Applies some treatment if the top term is a predicate application.
  pub fn pred_app_fold<T, F>(& mut self, init: T, f: F) -> T
  where F: Fn(T, PrdIdx, & mut TArgs) -> T {
    if let TTerm::P { pred, ref mut args } = * self {
      f(init, pred, args)
    } else {
      init
    }
  }

  /// Variables appearing in a top term.
  pub fn vars(& self) -> VarSet {
    match * self {
      TTerm::P { ref args, .. } => {
        let mut vars = VarSet::with_capacity(17) ;
        for term in args {
          vars.extend( term::vars(term) )
        }
        vars
      },
      TTerm::T(ref term) => term::vars(term),
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
  WritePrd: Fn(& mut W, PrdIdx, & TArgs) -> IoRes<()> {
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
  WritePrd: Fn(& mut W, PrdIdx, & TArgs) -> IoRes<()> {
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


/// A *set* of top terms.
///
/// Actually contains a set of `Term`s and a map from predicates to their
/// arguments.
#[derive(Clone, PartialEq, Eq)]
pub struct TTermSet {
  /// Set of terms.
  terms: HConSet<Term>,
  /// Predicate applications.
  preds: PrdHMap< HashSet<TArgs> >,
}
impl TTermSet {
  /// Creates a new top term set with some capacity
  #[inline]
  pub fn with_capacity(capa: usize) -> Self {
    TTermSet {
      terms: HConSet::with_capacity(capa),
      preds: PrdHMap::with_capacity(capa),
    }
  }
  /// Creates a new top term set with some capacities
  #[inline]
  pub fn with_capacities(term_capa: usize, pred_capa: usize) -> Self {
    TTermSet {
      terms: HConSet::with_capacity(term_capa),
      preds: PrdHMap::with_capacity(pred_capa),
    }
  }

  /// Reserves some space.
  #[inline]
  pub fn reserve(& mut self, terms: usize, preds: usize) {
    self.terms.reserve(terms) ;
    self.preds.reserve(preds)
  }

  /// Creates an empty top term set.
  #[inline]
  pub fn new() -> Self { Self::with_capacity(5) }

  /// Creates a top term set from a set of terms.
  #[inline]
  pub fn of_terms(terms: HConSet<Term>, pred_capa: usize) -> Self {
    TTermSet {
      terms: terms,
      preds: PrdHMap::with_capacity(pred_capa),
    }
  }

  /// True iff the set is empty.
  #[inline]
  pub fn is_empty(& self) -> bool {
    self.terms.is_empty() && self.preds.is_empty()
  }

  /// Number of elements.
  #[inline]
  pub fn len(& self) -> usize {
    let mut len = self.terms.len() ;
    for (_, argss) in & self.preds {
      len += argss.len()
    }
    len
  }

  /// Terms.
  #[inline]
  pub fn terms(& self) -> & HConSet<Term> {
    & self.terms
  }
  /// Predicate applications.
  #[inline]
  pub fn preds(& self) -> & PrdHMap< TArgss > {
    & self.preds
  }

  /// Terms (mutable version).
  #[inline]
  pub fn terms_mut(& mut self) -> & mut HConSet<Term> {
    & mut self.terms
  }
  /// Predicate applications (mutable version).
  #[inline]
  pub fn preds_mut(& mut self) -> & mut PrdHMap< TArgss > {
    & mut self.preds
  }

  /// True if `self` is a subset of `that`.
  #[inline]
  pub fn is_subset_of(& self, that: & Self) -> bool {
    // `terms` subset?
    if ! self.terms.is_subset(& that.terms) { return false }
    // All predicates in `that` also appear in `self`?
    for (pred, _) in & that.preds {
      if ! self.preds.contains_key(pred) {
        return false
      }
    }
    // All applications in `self` also in `that`?
    for (pred, self_set) in & self.preds {
      if let Some(that_set) = that.preds.get(pred) {
        if ! self_set.is_subset(that_set) { return false }
      } else {
        return false
      }
    }
    true
  }

  /// Inserts a predicate application.
  #[inline]
  pub fn insert_pred_app(& mut self, pred: PrdIdx, args: TArgs) -> bool {
    self.preds.entry(pred).or_insert_with(
      || HashSet::new()
    ).insert(args)
  }
  /// Inserts some predicate applications.
  pub fn insert_pred_apps<Iter, TArgss>(
    & mut self, pred: PrdIdx, argss: TArgss
  )
  where
  Iter: Iterator<Item = TArgs> + ExactSizeIterator,
  TArgss: IntoIterator<Item = TArgs, IntoIter = Iter> {
    let argss = argss.into_iter() ;
    if argss.len() == 0 { return () }
    self.preds.entry(pred).or_insert_with(
      || HashSet::new()
    ).extend( argss )
  }

  /// Inserts a term.
  #[inline]
  pub fn insert_term(& mut self, term: Term) -> bool {
    self.terms.insert(term)
  }
  /// Inserts some terms.
  #[inline]
  pub fn insert_terms<Iter, Terms>(& mut self, terms: Terms)
  where
  Iter: Iterator<Item = Term> + ExactSizeIterator,
  Terms: IntoIterator<Item = Term, IntoIter = Iter> {
    let terms = terms.into_iter() ;
    self.terms.reserve( terms.len() ) ;
    for term in terms { self.terms.insert(term) ; () }
  }

  /// Inserts a top term.
  pub fn insert_tterm(& mut self, tterm: TTerm) -> bool {
    match tterm {
      TTerm::T(term) => self.insert_term(term),
      TTerm::P { pred, args } => self.insert_pred_app(pred, args)
    }
  }

  /// Constructor from some top terms.
  pub fn of_tterms<Iter, TTs>(tterms: TTs) -> Self
  where
  Iter: Iterator<Item = TTerm> + ExactSizeIterator,
  TTs: IntoIterator<Item = TTerm, IntoIter = Iter> {
    let tterms = tterms.into_iter() ;
    let mut slf = Self::with_capacity( tterms.len() ) ;
    for tterm in tterms {
      slf.insert_tterm(tterm) ; ()
    }
    slf
  }

  /// Constructor from a single term.
  pub fn of_term(term: Term) -> Self {
    let mut slf = Self::new() ;
    slf.insert_term(term) ;
    slf
  }

  /// Puts the variables appearing in the top terms in some set.
  pub fn vars(& self, set: & mut VarSet) {
    for term in & self.terms {
      set.extend( term::vars(term) )
    }
    for (_, argss) in & self.preds {
      for args in argss {
        for arg in args {
          set.extend( term::vars(arg) )
        }
      }
    }
  }

  /// Removes some arguments from the predicate applications.
  pub fn remove_vars(& mut self, to_keep: & PrdHMap<VarSet>) {
    remove_vars_from_pred_apps(
      & mut self.preds, to_keep
    )
  }


  /// Writes all top terms with some separator.
  pub fn write<W, WriteVar, WritePrd>(
    & self, w: & mut W, sep: & str, write_var: WriteVar, write_pred: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WriteVar: Fn(& mut W, VarIdx) -> IoRes<()>,
  WritePrd: Fn(& mut W, PrdIdx, & TArgs) -> IoRes<()> {
    // Don't print the separator the first time.
    let mut separate = false ;
    macro_rules! write_sep {
      () => (
        if separate {
          write!(w, "{}", sep) ?
        } else {
          separate = true
        }
      ) ;
    }

    for term in & self.terms {
      write_sep!() ;
      term.write(w, & write_var) ?
    }

    for (pred, argss) in & self.preds {
      for args in argss {
        write_sep!() ;
        write_pred(w, * pred, args) ?
      }
    }

    Ok(())
  }
}
impl ::std::cmp::PartialOrd for TTermSet {
  fn partial_cmp(& self, other: & Self) -> Option<::std::cmp::Ordering> {
    use ::std::cmp::Ordering::* ;
    let mut le = true ;
    let mut ge = true ;
    macro_rules! check_none {
      () => ( if ! le && ! ge { return None } )
    }

    for term in & self.terms {
      if ! other.terms.contains(term) { le = false ; break }
    }
    for term in & other.terms {
      if ! self.terms.contains(term) { ge = false ; break }
    }
    check_none! {}

    // Part of what happens in this loop is explained below.
    for (pred, argss) in & self.preds {
      check_none! {}
      if let Some(ass) = other.preds.get(pred) {
        if ! argss.is_subset(ass) {
          le = false
        }
        if ! ass.is_subset(argss) {
          ge = false
        }
      } else {
        le = false
      }
    }

    // At this point we checked all predicate applications in `self`. We won't
    // touch `le` anymore.
    //
    // The only way `ge` can change is if it is true and `other` has some
    // predicates that don't appear in `self`. That's because in the previous
    // loop, whenever a predicate from `self` also appears in `other`, we
    // checked whether the other set of arguments is a subset of the self set
    // of arguments and set `ge` to false if it's not the case.

    if ge {
      for pred in other.preds.keys() {
        if ! self.preds.contains_key(pred) {
          ge = false ;
          break
        }
      }
    }

    match (le, ge) {
      (true, true) => Some(Equal),
      (true, false) => Some(Less),
      (false, true) => Some(Greater),
      (false, false) => None,
    }
  }
}

/// Removes some arguments from some predicate applications.
fn remove_vars_from_pred_apps(
  apps: & mut PrdHMap< TArgss >, to_keep: & PrdHMap<VarSet>
) {
  for (pred, argss) in apps.iter_mut() {
    let vars_to_keep = if let Some(vars) = to_keep.get(pred) {
      vars
    } else {
      continue
    } ;
    let mut old_argss = HashSet::with_capacity( argss.len() ) ;
    ::std::mem::swap( & mut old_argss, argss ) ;
    for mut args in old_argss {
      args.remove( vars_to_keep ) ;
      argss.insert(args) ;
    }
  }
}


/// A formula composed of top terms.
#[derive(Clone)]
pub enum TTerms {
  /// True.
  True,
  /// False.
  False,
  /// Conjunction.
  Conj {
    quant: Option<Quant>, tterms: TTermSet
  },
  /// Disjunction.
  Disj {
    quant: Option<Quant>,
    tterms: TTermSet,
    neg_preds: PrdHMap< TArgss >
  },
  /// Almost a DNF: a disjunction of conjunctions of `TTerm`s.
  Dnf {
    disj: Vec< (Option<Quant>, TTermSet) >
  },
}
impl TTerms {
  // pub fn inspect(& self) {
  //   match * self {
  //     TTerms::True => println!("true"),
  //     TTerms::False => println!("false"),
  //     TTerms::Conj { ref quant, ref tterms } => println!(
  //       "conj, {} ({})", tterms.len(),
  //       if let Some(q) = quant.as_ref() {
  //         format!("{}", q.len())
  //       } else { "none".into() }
  //     ),
  //     TTerms::Disj { ref quant, ref tterms, ref neg_preds } => println!(
  //       "conj, {}, {}, {}", tterms.len(), neg_preds.len(),
  //       if let Some(q) = quant.as_ref() {
  //         format!("{}", q.len())
  //       } else { "none".into() }
  //     ),
  //     TTerms::Dnf { ref disj } => println!(
  //       "dnf, {}", disj.len()
  //     ),
  //   }
  // }

  /// True.
  #[inline]
  pub fn tru() -> Self { TTerms::True }
  /// False.
  #[inline]
  pub fn fls() -> Self { TTerms::False }
  /// Constructor from a boolean.
  #[inline]
  pub fn of_bool(b: bool) -> Self {
    if b { Self::tru() } else { Self::fls() }
  }

  /// Boolean value of some top terms.
  #[inline]
  pub fn bool(& self) -> Option<bool> {
    match * self {
      TTerms::True => Some(true),
      TTerms::False => Some(false),
      _ => None,
    }
  }

  /// Removes some arguments from the predicate applications.
  pub fn remove_vars(& mut self, to_keep: & PrdHMap< VarSet >) {
    match * self {
      TTerms::True | TTerms::False => (),
      TTerms::Conj { ref mut tterms, .. } => tterms.remove_vars(to_keep),
      TTerms::Disj {
        ref mut tterms, ref mut neg_preds, ..
      } => {
        tterms.remove_vars(to_keep) ;
        remove_vars_from_pred_apps(neg_preds, to_keep)
      },
      TTerms::Dnf { ref mut disj } => for & mut (_, ref mut tterms) in disj {
        tterms.remove_vars(to_keep)
      },
    }
  }

  /// Constructor for a single term.
  pub fn of_term(quant: Option<Quant>, term: Term) -> Self {
    Self::conj( quant, TTermSet::of_term(term) )
  }

  /// Constructs a conjuction.
  pub fn conj(quant: Option<Quant>, tterms: TTermSet) -> Self {
    TTerms::Conj{ quant, tterms }.simplify()
  }

  /// Constructs a disjuction.
  pub fn disj(
    quant: Option<Quant>, tterms: TTermSet, neg_preds: PrdHMap<TArgss>
  ) -> Self {
    TTerms::Disj{ quant, tterms, neg_preds }.simplify()
  }
  /// Constructs a disjunction from a positive application and some negated top
  /// terms.
  ///
  /// This special format is exactly the one used by preprocessing.
  pub fn disj_of_pos_neg(
    quant: Option<Quant>, pos: Option<(PrdIdx, TArgs)>, neg: TTermSet
  ) -> Self {
    let TTermSet { terms, preds: neg_preds } = neg ;
    let mut tterms = TTermSet::with_capacities(terms.len(), 1) ;
    for term in terms {
      tterms.insert_term( not(term) ) ;
    }
    if let Some((pred, args)) = pos {
      tterms.insert_pred_app(pred, args) ;
    }
    TTerms::Disj {
      quant, tterms, neg_preds
    }
  }

  /// Constructs a DNF.
  pub fn dnf(disj: Vec< (Option<Quant>, TTermSet) >) -> Self {
    TTerms::Dnf{ disj }.simplify()
  }

  /// Predicates appearing in the top terms.
  pub fn preds(& self) -> PrdSet {
    let mut res = PrdSet::new() ;
    match * self {
      TTerms::True | TTerms::False => (),

      TTerms::Conj { ref tterms, .. } => for pred in tterms.preds.keys() {
        res.insert(* pred) ;
      },
      TTerms::Disj { ref tterms, ref neg_preds, .. } => {
        for pred in tterms.preds.keys() {
          res.insert(* pred) ;
        }
        for pred in neg_preds.keys() {
          res.insert(* pred) ;
        }
      },

      TTerms::Dnf { ref disj } => for & (_, ref tterms) in disj {
        for pred in tterms.preds.keys() {
          res.insert(* pred) ;
        }
      },
    }

    res
  }

  /// Constructs the disjunction of `self` and `conj` (a conjunction).
  ///
  /// Does not call `simplify` if it creates a dnf.
  ///
  /// # Error if
  ///
  /// - called on a `Disj`
  pub fn or(self, conj: (Option<Quant>, TTermSet)) -> Res<Self> {
    match self {
      TTerms::True => Ok(self),
      TTerms::False => Ok(
        TTerms::conj(conj.0, conj.1).simplify()
      ),
      TTerms::Conj { quant, tterms } => {
        // conj => self?
        if tterms.is_subset_of(& conj.1) {
          Ok( TTerms::Conj { quant, tterms } )
        } else
        // self => conj?
        if conj.1.is_subset_of(& tterms) {
          Ok(
            TTerms::Conj{ quant: conj.0, tterms: conj.1 }.simplify()
          )
        } else {
          Ok(
            TTerms::dnf(
              vec![ (quant, tterms), conj ]
            )
          )
        }
      },
      TTerms::Disj { .. } => bail!(
        "TTerms: trying to call `or` on a disjunction"
      ),
      TTerms::Dnf { disj } => {
        let mut nu_disj = Vec::with_capacity( disj.len() ) ;
        let mut ignore_conj = false ;
        for (quant, tterms) in disj {
          use std::cmp::Ordering::* ;
          match tterms.partial_cmp( & conj.1 ) {
            // conj => tterms
            // don't need `conj`
            Some(Less) => ignore_conj = true,
            // tterms => conj
            // skip `tterms`
            Some(Greater) => continue,
            // tterms = conj
            // skip `conj`
            Some(Equal) => ignore_conj = true,

            None => (),
          }
          nu_disj.push( (quant, tterms) )
        }

        if ! ignore_conj { nu_disj.push(conj) }

        // Note that if we ignored a `tterms_1` because `tterms_1 => conj`, and
        // then we saw a `tterms_2` s.t. `conj => tterms_2` so we ignored
        // `conj` as well, there is no problem because implication is
        // transitive.

        Ok( TTerms::Dnf { disj: nu_disj } )
      },
    }
  }

  /// Simplifies a formula of top terms.
  ///
  /// # TODO
  ///
  /// - factor code inside this function, `Conj` and `Disj` are almost the
  ///   same, DRY
  ///
  /// # Warning
  ///
  /// This function recurses on a `Conj` in the `Dnf` case. At the time of
  /// writing, this recursive call is guaranteed not to cause more recursive
  /// calls.
  ///
  /// Be careful to maintain, or (ideally) improve, this invariant.
  pub fn simplify(self) -> Self {

    match self {

      TTerms::True | TTerms::False => return self,

      TTerms::Conj { quant, mut tterms } => {
        tterms.preds.retain(
          |_, argss| ! argss.is_empty()
        ) ;

        let mut old_terms = HConSet::with_capacity( tterms.terms.len() ) ;
        // Used to inline conjunctions.
        let mut swap = HConSet::new() ;
        ::std::mem::swap( & mut old_terms, & mut tterms.terms ) ;

        'inline_conjs: loop {

          'inspect_conj_terms: for term in old_terms.drain() {

            // Is the term a conjunction?
            if let Some(kids) = term.conj_inspect() {
              for kid in kids {
                swap.insert( kid.clone() ) ;
                ()
              }
              continue 'inspect_conj_terms
            }

            // Term trivial?
            match term.bool() {
              Some(true) => continue 'inspect_conj_terms,
              Some(false) => return TTerms::fls(),
              None => (),
            }

            // Do we also have its negation?
            if tterms.terms.contains( & not( term.clone() ) ) {
              return TTerms::fls()
            }

            // Okay, move on.
            tterms.terms.insert(term) ;
            ()
          }

          // Keep going if `swap` is not empty.
          if ! swap.is_empty() {
            ::std::mem::swap( & mut old_terms, & mut swap ) ;
            continue 'inline_conjs
          } else {
            break 'inline_conjs
          }

        }

        // Only keep active quantified variables.
        let quant = quant.and_then(
          |quant| {
            let mut active = VarSet::with_capacity(
              quant.vars().len() * 2
            ) ;
            tterms.vars(& mut active) ;
            quant.filter(|var| active.contains(var))
          }
        ) ;

        if tterms.is_empty() {
          TTerms::tru()
        } else {
          TTerms::Conj { quant, tterms }
        }
      },

      TTerms::Disj {
        quant, mut tterms, mut neg_preds
      } => {
        tterms.preds.retain(
          |_, argss| ! argss.is_empty()
        ) ;
        neg_preds.retain(
          |_, argss| ! argss.is_empty()
        ) ;

        // Do we have a predicate application and its negation?
        for (pred, argss) in & tterms.preds {
          if let Some(neg_argss) = neg_preds.get(pred) {
            for args in argss {
              if neg_argss.contains(args) { return TTerms::tru() }
            }
          }
        }

        let mut old_terms = HConSet::with_capacity( tterms.terms.len() ) ;
        // Used to inline disjunctions.
        let mut swap = HConSet::new() ;
        ::std::mem::swap( & mut old_terms, & mut tterms.terms ) ;

        'inline_disj: loop {

          'inspect_disj_terms: for term in old_terms.drain() {

            // Is the term a disjunction?
            if let Some(kids) = term.disj_inspect() {
              for kid in kids {
                swap.insert( kid.clone() ) ;
                ()
              }
              continue 'inspect_disj_terms
            }

            // Term trivial?
            match term.bool() {
              Some(true) => return TTerms::tru(),
              Some(false) => continue 'inspect_disj_terms,
              None => (),
            }

            // Do we also have its negation?
            if tterms.terms.contains( & not( term.clone() ) ) {
              return TTerms::tru()
            }

            // Okay, move on.
            tterms.terms.insert(term) ;
            ()
          }

          // Keep going if `swap` is not empty.
          if ! swap.is_empty() {
            ::std::mem::swap( & mut old_terms, & mut swap ) ;
            continue 'inline_disj
          } else {
            break 'inline_disj
          }

        }

        // Only keep active quantified variables.
        let quant = quant.and_then(
          |quant| {
            let mut active = VarSet::with_capacity(
              quant.vars().len() * 2
            ) ;
            tterms.vars(& mut active) ;
            for (_, argss) in & neg_preds {
              for args in argss {
                for arg in args {
                  active.extend( term::vars(arg) )
                }
              }
            }
            quant.filter(|var| active.contains(var))
          }
        ) ;

        if tterms.is_empty() && neg_preds.is_empty() {
          TTerms::fls()
        } else {
          TTerms::Disj { quant, tterms, neg_preds }
        }
      },

      TTerms::Dnf { disj } => {
        // We're cheating a bit here. Simplifying the disjuncts is done by
        // constructing the corresponding `TTerms::Conj` and simplifying them.
        // While this causes a recursive call, it's fine because it is
        // guaranteed to be the only one.
        //
        // Unless something changes later in `Conj`'s simplification...
        let mut nu_disj: Vec<(_, TTermSet)> = Vec::with_capacity(
          disj.len()
        ) ;
        'simplify_disjuncts: for (quant, tterms) in disj {
          match ( TTerms::Conj { quant, tterms } ).simplify() {
            TTerms::True => return TTerms::True,
            TTerms::False => (),
            TTerms::Conj { quant, tterms } => {
              // Check with other disjuncts.
              let mut cnt = 0 ;
              while cnt < nu_disj.len() {
                use std::cmp::Ordering::* ;
                match tterms.partial_cmp(& nu_disj[cnt].1) {
                  None => cnt += 1,
                  // other disjunct => this disjunct
                  Some(Less) => { nu_disj.swap_remove(cnt) ; () },
                  // other disjunct = this disjunct
                  Some(Equal) => continue 'simplify_disjuncts,
                  // this disjunct => other disjunct
                  Some(Greater) => continue 'simplify_disjuncts,
                }
              }
              nu_disj.push( (quant, tterms) )
            },
            TTerms::Disj { .. } => panic!(
              "simplification of a conjunct in a TTerms DNF \
              yielded a disjunction, unreachable"
            ),
            TTerms::Dnf { .. } => panic!(
              "simplification of a conjunct in a TTerms DNF \
              yielded a DNF, unreachable"
            ),
          }
        }
        match nu_disj.len() {
          0 => TTerms::fls(),
          1 => if let Some((quant, tterms)) = nu_disj.pop() {
            TTerms::Conj { quant, tterms }
          } else {
            unreachable!()
          },
          _ => TTerms::Dnf { disj: nu_disj }
        }
      },
    }
  }


  /// Simplifies some top terms given some definitions for the predicates.
  pub fn simplify_pred_apps(self, model: & Model) -> Self {
    macro_rules! if_defined {
      ($pred:ident then |$def:ident| $stuff:expr) => (
        for & (ref idx, ref $def) in model {
          if idx == $pred { $stuff }
        }
      )
    }

    match self {
      TTerms::True => TTerms::True,
      TTerms::False => TTerms::False,

      TTerms::Conj { quant, mut tterms } => {
        let mut to_rm = PrdSet::new() ;

        for pred in tterms.preds.keys() {
          if_defined! {
            pred then |def| match def.bool() {
              Some(true) => { to_rm.insert(* pred) ; () },
              Some(false) => return TTerms::fls(),
              None => (),
            }
          }
        }

        for pred in to_rm {
          let value = tterms.preds.remove(& pred) ;
          debug_assert!( value.is_some() )
        }

        TTerms::Conj { quant, tterms }.simplify()
      },

      TTerms::Disj { quant, mut tterms, mut neg_preds } => {
        let mut to_rm = PrdSet::new() ;

        for pred in tterms.preds.keys() {
          if_defined! {
            pred then |def| match def.bool() {
              Some(false) => { to_rm.insert(* pred) ; () },
              Some(true) => return TTerms::tru(),
              None => (),
            }
          }
        }

        for pred in to_rm.drain() {
          let value = tterms.preds.remove(& pred) ;
          debug_assert!( value.is_some() )
        }

        for pred in neg_preds.keys() {
          if_defined! {
            pred then |def| match def.bool() {
              Some(true) => { to_rm.insert(* pred) ; () },
              Some(false) => return TTerms::tru(),
              None => (),
            }
          }
        }

        for pred in to_rm.drain() {
          let value = neg_preds.remove(& pred) ;
          debug_assert!( value.is_some() )
        }

        TTerms::Disj { quant, tterms, neg_preds }.simplify()
      },

      TTerms::Dnf { disj } => {
        let mut nu_disj = Vec::with_capacity( disj.len() ) ;

        for (quant, tterms) in disj {
          match (
            TTerms::Conj { quant, tterms }
          ).simplify_pred_apps(model) {
            TTerms::True => return TTerms::tru(),
            TTerms::False => (),

            TTerms::Conj { quant, tterms } => nu_disj.push(
              (quant, tterms)
            ),

            TTerms::Disj { .. } => panic!(
              "simplification of a conjunct in a TTerms DNF \
              yielded a disjunction, unreachable"
            ),
            TTerms::Dnf { .. } => panic!(
              "simplification of a conjunct in a TTerms DNF \
              yielded a DNF, unreachable"
            ),
          }
        }

        TTerms::Dnf{ disj: nu_disj }.simplify()
      },
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
  WritePrd: Fn(& mut W, PrdIdx, & TArgs) -> IoRes<()> {

    macro_rules! write_conj {
      ($quant:expr, $tterms:expr) => ({
        let close_quant = if let Some(quant) = $quant.as_ref() {
          write!(w, "(") ? ;
          quant.write(w, & write_var) ? ;
          write!(w, " ") ? ;
          true
        } else { false } ;

        let close_and = if $tterms.len() > 1 {
          write!(w, "(and ") ? ;
          true
        } else { false } ;

        $tterms.write(w, " ", & write_var, & write_prd) ? ;

        if close_and { write!(w, ")") ? }

        if close_quant { write!(w, ")") } else { Ok(()) }
      }) ;
    }

    match * self {
      TTerms::True => return write!(w, "true"),
      TTerms::False => return write!(w, "false"),

      TTerms::Conj { ref quant, ref tterms } => write_conj!(quant, tterms),

      TTerms::Disj { ref quant, ref tterms, ref neg_preds } => {
        let close_quant = if let Some(quant) = quant.as_ref() {
          write!(w, "(") ? ;
          quant.write(w, & write_var) ? ;
          write!(w, " ") ? ;
          true
        } else { false } ;

        let close_or = if tterms.len() + neg_preds.len() > 1 {
          write!(w, "(or ") ? ;
          true
        } else { false } ;

        tterms.write(w, " ", & write_var, & write_prd) ? ;

        let mut sep = ! tterms.is_empty() && ! neg_preds.is_empty() ;

        for (pred, argss) in neg_preds {
          for args in argss {
            if sep {
              write!(w, " ") ?
            } else {
              sep = true
            }
            write!(w, "(not ") ? ;
            write_prd(w, * pred, args) ? ;
            write!(w, ")") ?
          }
        }

        if close_or { write!(w, ")") ? }

        if close_quant { write!(w, ")") } else { Ok(()) }
      },

      TTerms::Dnf { ref disj } => {
        let close_or = if disj.len() > 1 {
          write!(w, "(or") ? ;
          true
        } else { false } ;

        for & (ref quant, ref tterms) in disj {
          write!(w, " ") ? ;
          write_conj!(quant, tterms) ?
        }

        if close_or { write!(w, ")") } else { Ok(()) }
      },
    }
  }

  /// Writes some top terms smt2 style using a special function for writing
  /// predicates.
  ///
  /// Equivalent to `write` with variable default printing.
  pub fn write_smt2<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WritePrd: Fn(& mut W, PrdIdx, & TArgs) -> IoRes<()> {
    self.write(
      w, |w, var| var.default_write(w), write_prd
    )
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
        } else if args.is_empty() {
          write!(w, "{}", pred_info[pred])
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
  /// Integer division.
  IDiv,
  /// Division.
  Div,
  /// Remainder.
  Rem,
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
  /// Conversion from `Int` to `Real`.
  ToInt,
  /// Conversion from `Real` to `Int`.
  ToReal,
}
impl Op {
  /// String representation.
  pub fn as_str(& self) -> & str {
    use self::Op::* ;
    use keywords::op::* ;
    match * self {
      Add => add_,
      Sub => sub_,
      Mul => mul_,
      IDiv => idiv_,
      Div => div_,
      Rem => rem_,
      Mod => mod_,
      Gt => gt_,
      Ge => ge_,
      Le => le_,
      Lt => lt_,
      Eql => eq_,
      Not => not_,
      And => and_,
      Or => or_,
      Impl => impl_,
      Ite => ite_,
      ToInt => to_int_,
      ToReal => to_real_,
    }
  }


  /// Evaluation.
  pub fn eval(& self, mut args: Vec<Val>) -> Res<Val> {
    use term::Op::* ;
    if args.is_empty() {
      bail!("evaluating operator on 0 elements")
    }

    macro_rules! arith_app {
      (relation $op:tt $str:tt => $args:expr) => ({
        let mut args = $args.into_iter() ;
        if let (
          Some(fst), Some(mut pre)
        ) = (args.next(), args.next()) {
          let mut res = fst.$op(& pre) ? ;
          for arg in args {
            res = res.and( & pre.$op(& arg) ? ) ? ;
            pre = arg
          }
          Ok(res)
        } else {
          bail!("`{}` applied to 0 or 1 argument(s)")
        }
      }) ;
      ($op:tt $str:tt => $args:expr) => ({
        let mut args = $args.into_iter() ;
        if let Some(mut acc) = args.next() {
          for arg in args {
            acc = acc.$op(& arg) ?
          }
          Ok(acc)
        } else {
          bail!("`{}` applied to zero arguments", $str)
        }
      }) ;
    }

    match * self {
      Add => arith_app!(add "+" => args),

      Sub => if args.len() == 1 {
        args.pop().unwrap().minus()
      } else {
        arith_app!(sub "-" => args)
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

      Div => bail!("evaluation of divisions is not implemented"),

      IDiv => {
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

      Rem => if args.len() != 2 {
        bail!(
          format!("evaluating `{}` with {} (!= 2) arguments", self, args.len())
        )
      } else {
        use num::Integer ;
        let b = try_val!( int args.pop().unwrap() ) ;
        if b == 1.into() {
          Ok( 0.into() )
        } else {
          let a = try_val!( int args.pop().unwrap() ) ;
          Ok( Val::I( a.div_rem(& b).1 ) )
        }
      },

      Mod => if args.len() != 2 {
        bail!(
          format!("evaluating `{}` with {} (!= 2) arguments", self, args.len())
        )
      } else {
        use num::{ Integer, Signed } ;
        let b = try_val!( int args.pop().unwrap() ) ;
        if b == 1.into() {
          Ok( 0.into() )
        } else {
          let a = try_val!( int args.pop().unwrap() ) ;
          let res = a.mod_floor(& b) ;
          let res = if res.is_negative() {
            b.abs() - res.abs()
          } else {
            res
          } ;
          Ok( Val::I( res ) )
        }
      },

      // Bool operators.

      Gt => arith_app! {
        relation gt ">" => args
      },

      Ge => arith_app! {
        relation ge ">=" => args
      },

      Le => arith_app! {
        relation le "<=" => args
      },

      Lt => arith_app! {
        relation lt "<" => args
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

      ToInt => if let Some(val) = args.pop() {
        if ! args.is_empty() {
          bail!(
            "expected two arguments for `{}`, found {}", ToInt, args.len() + 1
          )
        }
        if let Some(rat) = val.to_real() ? {
          let res = rat.denom() / rat.denom() ;
          if rat.denom().is_negative() ^ rat.denom().is_negative() {
            Ok( Val::I(- res) )
          } else {
            Ok( Val::I(res) )
          }
        } else {
          Ok(Val::N)
        }
      } else {
        bail!("expected one argument for `{}`, found none", ToInt)
      },

      ToReal => if let Some(val) = args.pop() {
        if ! args.is_empty() {
          bail!(
            "expected two arguments for `{}`, found {}", ToReal, args.len() + 1
          )
        }
        if let Some(i) = val.to_int() ? {
          Ok( Val::R( Rat::new(i.clone(), 1.into()) ) )
        } else {
          Ok(Val::N)
        }
      } else {
        bail!("expected one argument for `{}`, found none", ToReal)
      },

    }
  }
}
impl_fmt!{
  Op(self, fmt) {
    fmt.write_str( self.as_str() )
  }
}



/// Existential or universal quantifier.
///
/// Always use the constructors to avoid falsifying the invariant.
///
/// # Invariant
///
/// The variable partial maps are never empty.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Quant {
  /// Exists.
  Exists( VarHMap<Typ> ),
  /// Forall.
  Forall( VarHMap<Typ> ),
}
impl Quant {
  /// Creates an existential qualifier.
  pub fn exists(map: VarHMap<Typ>) -> Option<Self> {
    if map.is_empty() { None } else { Some( Quant::Exists(map) ) }
  }
  /// Creates an existential qualifier.
  pub fn forall(map: VarHMap<Typ>) -> Option<Self> {
    if map.is_empty() { None } else { Some( Quant::Forall(map) ) }
  }

  /// Quantified variables.
  pub fn vars(& self) -> & VarHMap<Typ> {
    match * self {
      Quant::Exists(ref vars) => vars,
      Quant::Forall(ref vars) => vars,
    }
  }

  /// Quantified variables (mutable version).
  pub fn vars_mut(& mut self) -> & mut VarHMap<Typ> {
    match * self {
      Quant::Exists(ref mut vars) => vars,
      Quant::Forall(ref mut vars) => vars,
    }
  }

  /// Number of quantified variables.
  pub fn len(& self) -> usize {
    let map = match * self {
      Quant::Exists(ref map) => map,
      Quant::Forall(ref map) => map,
    } ;
    debug_assert! { ! map.is_empty() }
    map.len()
  }

  /// Filters some quantified variables.
  ///
  /// Keeps all quantified variables such that `f(var)`.
  ///
  /// Returns `None` if the mapping ends up being empty.
  pub fn filter<F>(mut self, f: F) -> Option<Self>
  where F: Fn(& VarIdx) -> bool {
    self.vars_mut().retain( |var, _| f(var) ) ;
    if self.vars().is_empty() { None } else { Some(self) }
  }

  /// Writes the quantier and its quantified variables.
  pub fn write<W, WVar>(
    & self, w: & mut W, write_var: WVar
  ) -> IoRes<()>
  where W: Write, WVar: Fn(& mut W, VarIdx) -> IoRes<()> {
    debug_assert!( ! self.vars().is_empty() ) ;

    let qvars = match * self {
      Quant::Exists(ref qvars) => {
        write!(w, "exists ") ? ;
        qvars
      },
      Quant::Forall(ref qvars) => {
        write!(w, "forall ") ? ;
        qvars
      },
    } ;

    write!(w, "(") ? ;
    for (var, typ) in qvars {
      write!(w, " (") ? ;
      write_var(w, * var) ? ;
      write!(w, " {})", typ) ? ;
    }
    write!(w, " )")
  }

  /// Writes the opening part of the quantifier as a line.
  ///
  /// Basically `"{}(<quantified> ( <qvars> )\n", prefix`.
  pub fn write_pref<W, WVar>(
    & self, w: & mut W, pref: & str, write_var: WVar
  ) -> IoRes<()>
  where
  W: Write, WVar: Fn(& mut W, VarIdx) -> IoRes<()> {
    w.write( pref.as_bytes() ) ? ;
    let map = match * self {
      Quant::Exists(ref map) => {
        write!(w, "(exists (") ? ;
        map
      },
      Quant::Forall(ref map) => {
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



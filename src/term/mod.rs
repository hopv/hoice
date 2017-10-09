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
//! See [`simplify`](fn.simplify.html) for more details.
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


/// Either true, false, a conjunction or a DNF of top terms.
#[derive(Clone, PartialEq, Eq)]
pub enum TTerms {
  /// True.
  True,
  /// False.
  False,
  /// Conjunction.
  And( Vec<TTerm> ),
  /// Disjunction.
  Or( Vec<TTerm> ),
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

  /// True if the top terms contain an application of `pred`.
  pub fn mention_pred(& self, pred: PrdIdx) -> bool {
    match * self {
      TTerms::And(ref tterms) => for tterm in tterms {
        if let Some(p) = tterm.pred() {
          if p == pred { return true }
        }
      },
      TTerms::Or(ref tterms) => for tterm in tterms {
        if let Some(p) = tterm.pred() {
          if p == pred { return true }
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
  /// Constructor for a DNF.
  #[inline]
  pub fn disj(mut tterms: Vec<TTerm>) -> Self {
    let mut cnt = 0 ;
    while cnt < tterms.len() {
      match tterms[cnt].bool() {
        Some(true) => return TTerms::tru(),
        Some(false) => { tterms.swap_remove(cnt) ; },
        None => cnt += 1,
      }
    }
    if tterms.len() == 0 {
      TTerms::fls()
    } else if tterms.len() == 1 {
      TTerms::And(tterms)
    } else {
      TTerms::Or(tterms)
    }
  }

  /// The predicates appearing in some top terms.
  pub fn preds(& self) -> PrdSet {
    let mut set = PrdSet::new() ;
    match * self {
      TTerms::And(ref tterms) => for tterm in tterms {
        if let Some(pred) = tterm.pred() { set.insert(pred) ; }
      },
      TTerms::Or(ref tterms) => for tterm in tterms {
        if let Some(pred) = tterm.pred() { set.insert(pred) ; }
      },
      _ => (),
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
      TTerms::Or(ref tterms) => {
        let mut nu_tterms = Vec::with_capacity( tterms.len() ) ;
        for tterm in tterms {
          let tterm = tterm.subst_total(map) ? ;
          if let Some(b) = tterm.bool() {
            if b { return Ok( Self::tru() ) }
          } else {
            nu_tterms.push( tterm )
          }
        }
        if nu_tterms.len() == 0 {
          Ok( TTerms::fls() )
        } else if nu_tterms.len() == 1 {
          Ok( TTerms::And(nu_tterms) )
        } else {
          Ok( TTerms::Or(nu_tterms) )
        }
      },
      _ => Ok( self.clone() ),
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
      TTerms::And(ref tterms) => {
        write!(w, "(and") ? ;
        for tterm in tterms {
          write!(w, " ") ? ;
          tterm.write(w, & write_var, & write_prd) ?
        }
        write!(w, ")")
      },
      TTerms::Or(ref tterms) => {
        write!(w, "(or") ? ;
        for tterm in tterms {
          write!(w, " ") ? ;
          tterm.write(w, & write_var, & write_prd) ?
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
      TTerms::Or(ref tterms) => {
        write!(fmt, "(or") ? ;
        for tterm in tterms {
          write!(fmt, " ") ? ;
          tterm.fmt(fmt) ?
        }
        write!(fmt, ")")
      },
    }
  }
}

impl<'a> ::rsmt2::to_smt::Expr2Smt<
  (& 'a PrdSet, & 'a PrdSet, & 'a PrdMap< ::instance::info::PrdInfo >)
> for TTerms {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, info: & (
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
}
impl Op {
  /// String representation.
  pub fn as_str(& self) -> & str {
    use self::Op::* ;
    match * self {
      Add => "+", Sub => "-", Mul => "*", Div => "div", Mod => "mod",
      Gt => ">", Ge => ">=", Le => "<=", Lt => "<", Eql => "=",
      Not => "not", And => "and", Or => "or", Impl => "=>",
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
        let mut res ;
        for_first!{
          args.into_iter() => {
            |fst| res = try_val!(int fst),
            then |nxt| res = res * try_val!(int nxt),
            yild Ok( Val::I(res) )
          } else unreachable!()
        }
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
        let a = try_val!( int args.pop().unwrap() ) ;
        debug_assert!( args.is_empty() ) ;
        Ok(
          Val::I( a.mod_floor(& b) )
        )
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
        for_first!{
          args.into_iter() => {
            |fst| mem = fst,
            then |nxt| {
              if mem != nxt {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },
      Not => if args.len() != 1 {
        bail!(
          format!("evaluating `Not` with {} (!= 1) arguments", args.len())
        )
      } else {
        let b = try_val!( bool args.pop().unwrap() ) ;
        Ok( Val::B(! b) )
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
    }
  }
}
impl_fmt!{
  Op(self, fmt) {
    fmt.write_str( self.as_str() )
  }
}

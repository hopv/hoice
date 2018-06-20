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
//! # use hoice::term::{ Op, RTerm, typ } ;
//! let some_term = term::eq(
//!   term::int(11), term::app(
//!     Op::Mul, vec![ term::int_var(5), term::int(2) ]
//!   )
//! ) ;
//! # println!("{}", some_term) ;
//! 
//! // A `Term` dereferences to an `RTerm`:
//! match * some_term {
//!   RTerm::App { ref typ, op: Op::Eql, ref args } => {
//!     assert_eq!( typ, & typ::bool() ) ;
//!     assert_eq!( args.len(), 2 ) ;
//!     assert_eq!( format!("{}", some_term), "(= (+ (* (- 2) v_5) 11) 0)" )
//!   },
//!   _ => panic!("not an equality"),
//! }
//! ```

use hashconsing::* ;

use common::* ;
use var_to::terms::VarTermsSet ;

#[macro_use]
mod op ;
pub use self::op::* ;
mod factory ;

pub mod simplify ;
pub mod typ ;
#[cfg(test)]
mod test ;

pub use self::factory::* ;
pub use self::typ::Typ ;


/// A real term.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum RTerm {
  /// A clause variable.
  Var(Typ, VarIdx),
  /// An integer.
  Int(Int),
  /// A real (actually a rational).
  Real(Rat),
  /// A boolean.
  Bool(bool),
  /// A **constant** array.
  ///
  /// The type is the type of **the indices** of the arrays.
  CArray { typ: Typ, term: Box<Term> },
  /// An operator application.
  App {
    /// Type of the application.
    typ: Typ,
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
      RTerm::App { op, ref args, .. } => Some((op, args)),
      _ => None,
    }
  }

  /// Returns the kids of an ite.
  pub fn ite_inspect(& self) -> Option<(& Term, & Term, & Term)> {
    match * self {
      RTerm::App { op: Op::Ite, ref args, .. } => {
        debug_assert_eq! { args.len(), 3 }
        Some( (& args[0], & args[1], & args[2]) )
      },
      _ => None,
    }
  }

  /// Returns the kid of a negation.
  pub fn neg_inspect(& self) -> Option<& Term> {
    match * self {
      RTerm::App { op: Op::Not, ref args, .. } => {
        debug_assert_eq! { args.len(), 1 }
        Some(& args[0])
      },
      _ => None,
    }
  }

  /// Returns the kids of conjunctions.
  pub fn conj_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::And, ref args, .. } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of disjunctions.
  pub fn disj_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Or, ref args, .. } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of equalities.
  pub fn eq_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Eql, ref args, .. } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of additions.
  pub fn add_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Add, ref args, .. } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of subtractions.
  pub fn sub_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Sub, ref args, .. } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of multiplications.
  pub fn mul_inspect(& self) -> Option<& Vec<Term>> {
    match * self {
      RTerm::App { op: Op::Mul, ref args, .. } => Some(args),
      _ => None,
    }
  }
  /// Returns the kids of a constant multiplication.
  pub fn cmul_inspect(& self) -> Option<(Val, & Term)> {
    match * self {
      RTerm::App { op: Op::CMul, ref args, .. } => {
        if args.len() == 2 {
          if let Some(val) = args[0].val() {
            return Some((val, & args[1]))
          }
        }
        panic!("illegal c_mul application: {}", self)
      },
      _ => None,
    }
  }

  /// Iterates over the subterms of a term.
  pub fn iter<F: FnMut(& RTerm)>(& self, mut f: F) {
    let mut stack = vec![self] ;

    while let Some(term) = stack.pop() {
      f(term) ;
      match * term {
        RTerm::App { ref args, .. } => for term in args {
          stack.push(term)
        },
        RTerm::CArray { ref term, .. } => stack.push(& * term),
        RTerm::Var(_, _) |
        RTerm::Int(_) |
        RTerm::Real(_) |
        RTerm::Bool(_) => (),
      }
    }
  }

  /// Type of the term.
  pub fn typ(& self) -> Typ {
    match * self {
      RTerm::Var(ref typ, _) => typ.clone(),
      RTerm::Int(_) => typ::int(),
      RTerm::Real(_) => typ::real(),
      RTerm::Bool(_) => typ::bool(),
      RTerm::CArray { ref typ, ref term } => typ::array(
        typ.clone(), term.typ()
      ),
      RTerm::App { ref typ, .. } => typ.clone(),
    }
  }

  /// True if the term is zero (integer or real).
  pub fn is_zero(& self) -> bool {
    match ( self.int(), self.real() ) {
      (Some(i), _) => i.is_zero(),
      (_, Some(r)) => r.is_zero(),
      _ => false,
    }
  }

  /// True if the term is one (integer or real).
  pub fn is_one(& self) -> bool {
    use num::One ;
    match ( self.int(), self.real() ) {
      (Some(i), _) => i == Int::one(),
      (_, Some(r)) => r == Rat::one(),
      _ => false,
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
      if let Some(this_term) = to_do.pop() {
        stack.push( (to_do, sep, end) ) ;
        match * this_term {
          Var(_, v) => {
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
          CArray { ref term, .. } => {
            write!(w, "{}((as const {})", sep, this_term.typ()) ? ;
            stack.push( (vec![term], " ", ")") )
          },
          App { op, ref args, .. } => {
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

  /// True if atom `self` implies atom `other` syntactically.
  ///
  /// Returns
  ///
  /// - `None` if no conclusion was reached,
  /// - `Some(Greater)` if `lhs => rhs`,
  /// - `Some(Less)` if `lhs <= rhs`,
  /// - `Some(Equal)` if `lhs` and `rhs` are equivalent.
  ///
  /// So *greater* really means *more generic*.
  ///
  /// See [the module's function][atom implies] for more details and examples.
  ///
  /// [atom implies]: fn.atom_implies.html (atom_implies module-level function)
  pub fn conj_simpl(& self, other: & Self) -> simplify::SimplRes {
    simplify::conj_simpl(& self, & other)
  }

  /// Term evaluation (int).
  pub fn int_eval<E: Evaluator>(
    & self, model: & E
  ) -> Res< Option<Int> > {
    self.eval(model)?.to_int()
  }

  /// Term evaluation (real).
  pub fn real_eval<E: Evaluator>(
    & self, model: & E
  ) -> Res< Option<Rat> > {
    self.eval(model)?.to_real()
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
  ///   term::int(7), term::int_var(1)
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
  ///   term::int(7), term::int_var(1)
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

  /// Evaluates a term with an empty model.
  pub fn as_val(& self) -> Val {
    if let Ok(res) = self.eval(& ()) { res } else {
      val::none(self.typ().clone())
    }
  }

  /// Integer a constant integer term evaluates to.
  pub fn int(& self) -> Option<Int> {
    if self.typ() != typ::int() { return None }
    match self.int_eval( & () ) {
      Ok(Some(i)) => Some(i),
      _ => None
    }
  }
  /// Integer a constant integer term evaluates to.
  pub fn real(& self) -> Option<Rat> {
    match self.real_eval( & () ) {
      Ok(Some(r)) => Some(r),
      _ => None
    }
  }

  /// Turns a constant term in a `Val`.
  pub fn val(& self) -> Option<Val> {
    match * self {
      RTerm::Int(ref i) => Some( val::int(i.clone()) ),
      RTerm::Real(ref r) => Some( val::real(r.clone()) ),
      RTerm::Bool(b) => Some( val::bool(b) ),
      _ => None,
    }
  }

  /// Returns a constant arithmetic version of the term if any.
  pub fn arith(& self) -> Option<Term> {
    if let Some(i) = self.int() {
      Some( term::int(i) )
    } else if let Some(r) = self.real() {
      Some( term::real(r) )
    } else {
      None
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
      RTerm::App { op: Op::Not, ref args, .. } => args[0].is_relation(),
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
  ///
  /// # TODO
  ///
  /// - remove recursive call for constant arrays
  pub fn eval<E: Evaluator>(& self, model: & E) -> Res<Val> {
    use self::RTerm::* ;
    let mut current = self ;
    let mut stack = vec![] ;

    'eval: loop {
      // Go down applications.
      let mut evaled = match * current {
        App { op, ref args, .. } => {
          current = & args[0] ;
          stack.push( (op, & args[1..], vec![]) ) ;
          continue 'eval
        },
        // Rest are leaves, going up.
        Var(_, v) => if v < model.len() {
          model.get(v).clone()
        } else {
          bail!("model is too short ({})", model.len())
        },
        Int(ref i) => val::int( i.clone() ),
        Real(ref r) => val::real( r.clone() ),
        Bool(b) => val::bool(b),
        CArray { ref typ, ref term } => {
          let default = term.eval(model) ? ;
          val::array(typ.clone(), default)
        },
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
  pub fn real_val(& self) -> Option<& Rat> {
    if let RTerm::Real(ref r) = * self { Some( r ) } else { None }
  }

  /// The highest variable index appearing in the term.
  pub fn highest_var(& self) -> Option<VarIdx> {
    let mut to_do = vec![ self ] ;
    let mut max = None ;
    while let Some(term) = to_do.pop() {
      match * term {
        RTerm::Var(_, i) => max = Some(
          ::std::cmp::max( i, max.unwrap_or(0.into()) )
        ),
        RTerm::Int(_) |
        RTerm::Real(_) |
        RTerm::Bool(_) => (),
        RTerm::CArray { ref term, .. } => to_do.push(& * term),
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
      RTerm::Var(_, i) => Some(i),
      _ => None,
    }
  }

  /// Return true if the term mentions at least one variable from `vars`.
  pub fn mentions_one_of(& self, vars: & VarSet) -> bool {
    let mut to_do = vec![ self ] ;
    while let Some(term) = to_do.pop() {
      match * term {
        RTerm::Var(_, var) => if vars.contains(& var) {
          return true
        },
        RTerm::Bool(_) |
        RTerm::Int(_) |
        RTerm::Real(_) |
        RTerm::CArray { .. } => (),
        RTerm::App { ref args, .. } => for arg in args {
          to_do.push(arg)
        },
      }
    }
    false
  }

  /// If the term is a negation, returns what's below the negation.
  pub fn rm_neg(& self) -> Option<Term> {
    match * self {
      RTerm::App { op: Op::Not, ref args, .. } => {
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
  ///
  /// # TODO
  ///
  /// - remove recursive call in the array case
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
        RTerm::Var(ref typ, var) => if let Some(term) = map.var_get(var) {
          debug_assert_eq! { typ, & term.typ() }
          subst_count += 1 ;
          term
        } else if total {
          return None
        } else {
          current.clone()
        },
        RTerm::App { op, ref args, .. } => {
          current = & args[0] ;
          stack.push(
            (op, & args[1..], Vec::with_capacity( args.len() ))
          ) ;
          continue 'go_down
        },
        RTerm::CArray { ref typ, ref term } => {
          if let Some((term, changed)) = term.subst_custom(map, total) {
            if changed {
              subst_count += 1 ;
            }
            cst_array(typ.clone(), term)
          } else {
            return None
          }

        },
        RTerm::Bool(_) |
        RTerm::Real(_) |
        RTerm::Int(_) => current.clone(),
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


  /// Tries to turn a term into a substitution.
  ///
  /// Works only on equalities.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use hoice::term ;
  ///
  /// let bv0 = term::bool_var(0) ;
  /// let bv1 = term::bool_var(1) ;
  /// let bv2 = term::bool_var(2) ;
  /// let rhs = term::or(vec![bv1, bv2]) ;
  /// let term = term::eq(bv0, rhs.clone()) ;
  /// debug_assert_eq! { term.as_subst(), Some((0.into(), rhs)) }
  /// ```
  pub fn as_subst(& self) -> Option<(VarIdx, Term)> {
    if let Some(kids) = self.eq_inspect() {
      debug_assert_eq! { kids.len(), 2 }
      let (lhs, rhs) = (& kids[0], & kids[1]) ;

      if let Some(var_idx) = lhs.var_idx() {
        return Some((var_idx, rhs.clone()))
      } else if let Some(var_idx) = rhs.var_idx() {
        return Some((var_idx, lhs.clone()))
      }

      if lhs.typ().is_arith() {
        debug_assert! { rhs.is_zero() }

        let lhs = if let Some((_, term)) = lhs.cmul_inspect() {
          term
        } else { lhs } ;

        let mut add = vec![] ;
        let mut var = None ;
        let mut negated = false ;

        if let Some(kids) = lhs.add_inspect() {
          for kid in kids {
            if var.is_some() {
              add.push(kid.clone()) ;
              continue
            }
            if let Some(var_index) = kid.var_idx() {
              debug_assert! { var.is_none() }
              var = Some(var_index) ;
              continue
            } else if let Some((val, term)) = kid.cmul_inspect() {
              if let Some(var_index) = term.var_idx() {
                if val.is_one() {
                  var = Some(var_index) ;
                  continue
                } else if val.is_minus_one() {
                  var = Some(var_index) ;
                  negated = true ;
                  continue
                }
              }
            }
            add.push(kid.clone())
          }

          if let Some(var) = var {
            let mut sum = term::add(add) ;
            if ! negated { sum = term::u_minus(sum) }
            Some((var, sum))
          } else {
            None
          }
        } else {
          None
        }
      } else {
        None
      }

    } else {
      None
    }
  }



  /// Attempts to invert a term from a variable.
  pub fn invert_var(& self, var: VarIdx, typ: Typ) -> Option<(VarIdx, Term)> {
    self.invert( term::var(var, typ) )
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
  /// let term = term::u_minus( term::int_var(0) ) ;
  /// println!("{}", term) ;
  /// assert_eq!{
  ///   term.invert( term::int_var(1) ),
  ///   Some( (0.into(), term::u_minus( term::int_var(1) ) ) )
  /// }
  /// let term = term::sub( vec![ term::int_var(0), term::int(7) ] ) ;
  /// println!("{}", term) ;
  /// assert_eq!{
  ///   term.invert( term::int_var(1) ),
  ///   Some( (0.into(), term::add( vec![ term::int_var(1), term::int(7) ] ) ) )
  /// }
  /// let term = term::add( vec![ term::int(7), term::int_var(0) ] ) ;
  /// println!("{}", term) ;
  /// assert_eq!{
  ///   term.invert( term::int_var(1) ),
  ///   Some(
  ///     (0.into(), term::sub( vec![ term::int_var(1), term::int(7) ] ) )
  ///   )
  /// }
  /// ```
  pub fn invert(& self, term: Term) -> Option<(VarIdx, Term)> {
    let mut solution = term ;
    let mut term = self ;

    loop {
      // println!("inverting {}", term) ;
      match * term {
        RTerm::App { op, ref args, .. } => {
          let (po, symmetric) = match op {
            Op::Add => (Op::Sub, true),
            Op::Sub => {
              if args.len() == 1 {
                solution = term::u_minus( solution ) ;
                term = & args[0] ;
                continue
              } else if args.len() == 2 {
                if args[0].val().is_some() {
                  solution = term::sub(
                    vec![ args[0].clone(), solution ]
                  ) ;
                  term = & args[1] ;
                  continue
                } else if args[1].val().is_some() {
                  solution = term::add(
                    vec![ args[1].clone(), solution ]
                  ) ;
                  term = & args[0] ;
                  continue
                }
              }
              return None
            },
            Op::IDiv => return None,
            Op::CMul => {
              if args.len() == 2 {
                if let Some(val) = args[0].val() {
                  if val.minus().expect(
                    "illegal c_mul application found in `invert`"
                  ).is_one() {
                    solution = term::u_minus(solution) ;
                    term = & args[1] ;
                    continue
                  } else {
                    return None
                  }
                }
              }

              panic!("illegal c_mul application found in `invert`")
            },
            // Op::Div => (Op::Mul, false),
            // Op::Mul => (Op::Div, true),
            Op::ToReal => {
              solution = term::to_int(solution) ;
              term = & args[0] ;
              continue
            },
            Op::ToInt => {
              solution = term::to_real(solution) ;
              term = & args[0] ;
              continue
            },
            _ => return None,
          } ;
          if args.len() != 2 { return None }

          if let Some(arith) = args[0].arith() {
            if symmetric {
              solution = term::app( po, vec![ solution, arith ] )
            } else {
              solution = term::app( op, vec![ arith, solution ] )
            }
            term = & args[1]
          } else if let Some(arith) = args[1].arith() {
            solution = term::app( po, vec![ solution, arith ] ) ;
            term = & args[0]
          } else {
            return None
          }
        },
        RTerm::Var(_, v) => return Some((v, solution)),
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
    args: VarTerms,
  },
  /// Just a term.
  T(Term),
}
impl TTerm {
  /// The false top term.
  pub fn fls() -> Self {
    TTerm::T( term::fls() )
  }
  /// The true top term.
  pub fn tru() -> Self {
    TTerm::T( term::tru() )
  }

  /// Type of the top term.
  ///
  /// Should always be bool, except during parsing.
  pub fn typ(& self) -> Typ {
    match * self {
      TTerm::P { .. } => typ::bool(),
      TTerm::T(ref term) => term.typ(),
    }
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
  pub fn args(& self) -> Option<& VarTerms> {
    match * self {
      TTerm::P { ref args, .. } => Some(args),
      _ => None,
    }
  }

  /// Applies some treatment if the top term is a predicate application.
  pub fn pred_app_fold<T, F>(& mut self, init: T, f: F) -> T
  where F: Fn(T, PrdIdx, & mut VarTerms) -> T {
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
        for term in args.iter() {
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
        let mut nu_args = VarMap::with_capacity( args.len() ) ;
        for arg in args.iter() {
          let (t, b) = arg.subst(map) ;
          nu_args.push(t) ;
          changed = changed || b
        }
        * args = nu_args.into() ;
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
        for term in args.iter() {
          if let Some((term, _)) = term.subst_total(map) {
            new_args.push(term)
          } else {
            bail!("total substitution failed (predicate)")
          }
        }
        Ok( TTerm::P { pred, args: new_args.into() } )
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
  WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
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
  WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
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
        for arg in args.iter() {
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
  preds: PrdHMap< VarTermsSet >,
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

  /// Destroys the set.
  #[inline]
  pub fn destroy(self) -> (HConSet<Term>, PrdHMap<VarTermsSet>) {
    (self.terms, self.preds)
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
  pub fn preds(& self) -> & PrdHMap< VarTermsSet > {
    & self.preds
  }

  /// Terms (mutable version).
  #[inline]
  pub fn terms_mut(& mut self) -> & mut HConSet<Term> {
    & mut self.terms
  }
  /// Predicate applications (mutable version).
  #[inline]
  pub fn preds_mut(& mut self) -> & mut PrdHMap< VarTermsSet > {
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

  /// Variable substitution.
  pub fn subst<Map: VarIndexed<Term>>(& self, map: & Map) -> Self {
    let mut terms = HConSet::<Term>::with_capacity(self.terms.len()) ;
    for term in self.terms() {
      let (term, _) = term.subst(map) ;
      terms.insert(term) ;
    }

    let mut preds = PrdHMap::with_capacity( self.preds.len() ) ;
    for (pred, argss) in self.preds.iter() {
      let mut nu_argss = VarTermsSet::with_capacity( argss.len() ) ;
      for args in argss {
        let args = var_to::terms::new( args.subst(map) ) ;
        nu_argss.insert(args) ;
      }
      preds.insert(* pred, nu_argss) ;
    }

    TTermSet { terms, preds }
  }

  /// Inserts a predicate application.
  #[inline]
  pub fn insert_pred_app(& mut self, pred: PrdIdx, args: VarTerms) -> bool {
    self.preds.entry(pred).or_insert_with(
      || VarTermsSet::new()
    ).insert(args)
  }
  /// Inserts some predicate applications.
  pub fn insert_pred_apps<Iter, TArgss>(
    & mut self, pred: PrdIdx, argss: TArgss
  )
  where
  Iter: Iterator<Item = VarTerms> + ExactSizeIterator,
  TArgss: IntoIterator<Item = VarTerms, IntoIter = Iter> {
    let argss = argss.into_iter() ;
    if argss.len() == 0 { return () }
    self.preds.entry(pred).or_insert_with(
      || VarTermsSet::new()
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
        for arg in args.iter() {
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
  WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
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
  apps: & mut PrdHMap< VarTermsSet >, to_keep: & PrdHMap<VarSet>
) {
  for (pred, argss) in apps.iter_mut() {
    let vars_to_keep = if let Some(vars) = to_keep.get(pred) {
      vars
    } else {
      continue
    } ;
    let mut old_argss = VarTermsSet::with_capacity( argss.len() ) ;
    ::std::mem::swap( & mut old_argss, argss ) ;
    for args in old_argss {
      argss.insert( args.remove( vars_to_keep ) ) ;
    }
  }
}


/// A formula composed of top terms.
#[derive(Clone, PartialEq, Eq)]
pub enum TTerms {
  /// True.
  True,
  /// False.
  False,
  /// Conjunction.
  Conj {
    quant: Option<Quant>,
    tterms: TTermSet,
  },
  /// Disjunction.
  Disj {
    quant: Option<Quant>,
    tterms: TTermSet,
    neg_preds: PrdHMap< VarTermsSet >,
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

  /// Attempts to transform some terms in a term.
  pub fn to_term(& self) -> Option<Term> {
    match * self {
      TTerms::True => Some( term::tru() ),
      TTerms::False => Some( term::fls() ),

      TTerms::Conj { ref quant, .. } if quant.is_some() => None,
      TTerms::Conj { ref tterms, .. } if ! tterms.preds.is_empty() => None,
      TTerms::Conj { ref tterms, .. } => Some(
        term::and(
          tterms.terms().iter().map(|term| term.clone()).collect()
        )
      ),

      TTerms::Disj { ref quant, .. } if quant.is_some() => None,
      TTerms::Disj {
        ref tterms, ref neg_preds, ..
      } if ! tterms.preds.is_empty() || ! neg_preds.is_empty() => None,
      TTerms::Disj { ref tterms, .. } => Some(
        term::or(
          tterms.terms().iter().map(|term| term.clone()).collect()
        )
      ),

      TTerms::Dnf { ref disj } => {
        let mut disj_terms = Vec::with_capacity( disj.len() ) ;
        for & (ref quant, ref conj) in disj {
          if quant.is_some()
          || ! conj.preds.is_empty() { return None }
          disj_terms.push(
            term::and(
              conj.terms().iter().map(|term| term.clone()).collect()
            )
          )
        }
        Some( term::or(disj_terms) )
      },
    }
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

  /// Variable substitution.
  pub fn subst<Map: VarIndexed<Term>>(& self, map: & Map) -> Self {
    match * self {
      TTerms::True => TTerms::True,
      TTerms::False => TTerms::False,

      TTerms::Conj { ref quant, ref tterms } => {
        debug_assert! {
          if let Some(quant) = quant.as_ref() {
            quant.vars().keys().all(
              |v| map.var_get(* v).is_none()
            )
          } else {
            true
          }
        }
        TTerms::Conj { quant: quant.clone(), tterms: tterms.subst(map) }
      },

      TTerms::Disj { ref quant, ref tterms, ref neg_preds } => {
        debug_assert! {
          if let Some(quant) = quant.as_ref() {
            quant.vars().keys().all(
              |v| map.var_get(* v).is_none()
            )
          } else {
            true
          }
        }

        let mut preds = PrdHMap::with_capacity( neg_preds.len() ) ;
        for (pred, argss) in neg_preds.iter() {
          let mut nu_argss = VarTermsSet::with_capacity( argss.len() ) ;
          for args in argss {
            let args = var_to::terms::new( args.subst(map) ) ;
            nu_argss.insert(args) ;
          }
          preds.insert(* pred, nu_argss) ;
        }

        TTerms::Disj {
          quant: quant.clone(),
          tterms: tterms.subst(map),
          neg_preds: preds,
        }
      },

      TTerms::Dnf { ref disj } => {
        let mut nu_disj = Vec::with_capacity( disj.len() ) ;
        for & (ref quant, ref tterms) in disj {
          debug_assert! {
            if let Some(quant) = quant.as_ref() {
              quant.vars().keys().all(
                |v| map.var_get(* v).is_none()
              )
            } else {
              true
            }
          }
          nu_disj.push(
            (quant.clone(), tterms.subst(map))
          )
        }
        TTerms::Dnf { disj: nu_disj }
      },
    }
  }

  /// Constructor for a single term.
  pub fn of_term(quant: Option<Quant>, term: Term) -> Self {
    Self::conj( quant, TTermSet::of_term(term) )
  }

  /// Constructs a conjuction.
  pub fn conj(quant: Option<Quant>, tterms: TTermSet) -> Self {
    TTerms::Conj { quant, tterms }.simplify()
  }

  /// Constructs a disjuction.
  pub fn disj(
    quant: Option<Quant>, tterms: TTermSet, neg_preds: PrdHMap<VarTermsSet>
  ) -> Self {
    TTerms::Disj { quant, tterms, neg_preds }.simplify()
  }
  /// Constructs a disjunction from a positive application and some negated top
  /// terms.
  ///
  /// This special format is exactly the one used by preprocessing.
  pub fn disj_of_pos_neg(
    quant: Option<Quant>, pos: Option<(PrdIdx, VarTerms)>, neg: TTermSet
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
                for arg in args.iter()   {
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
  pub fn simplify_pred_apps(
    self, model: & Model, pred_terms: & PrdMap< Option<TTerms> >
  ) -> Self {
    macro_rules! if_defined {
      ($pred:ident then |$def:ident| $stuff:expr) => (
        if let Some($def) = pred_terms[* $pred].as_ref() {
          $stuff
        } else {
          for & (ref idx, ref $def) in model {
            if idx == $pred { $stuff }
          }
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
          ).simplify_pred_apps(model, pred_terms) {
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
  WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {

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
  WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
    self.write(
      w, |w, var| var.default_write(w), write_prd
    )
  }
}

impl<'a, 'b> ::rsmt2::print::Expr2Smt<
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
          for arg in args.iter() {
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



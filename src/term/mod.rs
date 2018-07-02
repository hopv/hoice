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

#[macro_use]
mod op ;
mod factory ;
mod tterms ;
pub mod simplify ;
pub mod typ ;
mod zip ;

pub use self::op::* ;
pub use self::factory::* ;
pub use self::tterms::* ;
pub use self::typ::Typ ;

#[cfg(test)]
mod test ;



/// Hash consed term.
pub type Term = HConsed<RTerm> ;



/// A real term.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum RTerm {
  /// A clause variable.
  Var(Typ, VarIdx),
  /// A constant.
  Cst(Val),

  /// A **constant** array.
  ///
  /// The type is the type of **the indices** of the arrays.
  CArray {
    /// Type of **the indices** (not the array).
    typ: Typ,
    /// Default term of the array.
    term: Box<Term>
  },

  /// An operator application.
  App {
    /// Type of the application.
    typ: Typ,
    /// The operator.
    op: Op,
    /// The arguments.
    args: Vec<Term>,
  },

  /// A datatype constructor application.
  DTypNew {
    /// Type of the application.
    typ: Typ,
    /// Name of the constructor.
    name: String,
    /// Arguments of the constructor.
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
        RTerm::DTypNew { ref args, .. } => for term in args {
          stack.push(term)
        },
        RTerm::Var(_, _) |
        RTerm::Cst(_) => (),
      }
    }
  }

  /// Type of the term.
  pub fn typ(& self) -> Typ {
    match self {
      RTerm::Var(typ, _) => typ.clone(),
      RTerm::Cst(val) => val.typ(),
      RTerm::CArray { typ, term } => typ::array(
        typ.clone(), term.typ()
      ),
      RTerm::DTypNew { typ, .. } => typ.clone(),
      RTerm::App { typ, .. } => typ.clone(),
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

        match this_term {
          Var(_, v) => {
            write!(w, "{}", sep) ? ;
            write_var(w, * v) ?
          },
          Cst(val) => write!(w, "{}{}", sep, val) ?,

          CArray { term, .. } => {
            write!(w, "{}((as const {})", sep, this_term.typ()) ? ;
            stack.push( (vec![term], " ", ")") )
          },

          App { op, args, .. } => {
            write!(w, "{}({}", sep, op) ? ;
            stack.push(
              (args.iter().rev().map(|t| t.get()).collect(), " ", ")")
            )
          },

          DTypNew { name, args, .. } => if args.is_empty() {
            write!(w, "{}", name) ?
          } else {
            write!(w, "({}", name) ? ;
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
      RTerm::Cst(ref val) => Some( val.clone() ),
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
        // Leaves, going up.
        Var(_, v) => if v < model.len() {
          model.get(v).clone()
        } else {
          bail!("model is too short ({})", model.len())
        },
        Cst(ref val) => val.clone(),

        // Recursive cases.

        App { op, ref args, .. } => {
          current = & args[0] ;
          stack.push( (op, & args[1..], vec![]) ) ;
          continue 'eval
        },

        CArray { ref typ, ref term } => {
          let default = term.eval(model) ? ;
          val::array(typ.clone(), default)
        },

        DTypNew { .. } => bail!(
          "datatype constructor evaluation is not implemented"
        ),
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
    if let RTerm::Cst(val) = self {
      if let val::RVal::I(i) = val.get() {
        return Some( i )
      }
    }
    None
  }
  /// If the term's a rational constant, returns the value.
  pub fn real_val(& self) -> Option<& Rat> {
    if let RTerm::Cst(val) = self {
      if let val::RVal::R(r) = val.get() {
        return Some( r )
      }
    }
    None
  }

  /// The highest variable index appearing in the term.
  pub fn highest_var(& self) -> Option<VarIdx> {
    let mut to_do = vec![ self ] ;
    let mut max = None ;
    while let Some(term) = to_do.pop() {
      match * term {
        RTerm::Var(_, i) => max = Some(
          ::std::cmp::max( i, max.unwrap_or_else(|| 0.into()) )
        ),
        RTerm::Cst(_) => (),

        RTerm::CArray { ref term, .. } => to_do.push(& * term),

        RTerm::App{ ref args, .. } => for arg in args {
          to_do.push(arg)
        },

        RTerm::DTypNew { ref args, .. } => for arg in args {
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
        RTerm::Cst(_) => (),

        RTerm::CArray { ref term, .. } => to_do.push(term),

        RTerm::App { ref args, .. } => for arg in args {
          to_do.push(arg)
        },

        RTerm::DTypNew { ref args, .. } => for arg in args {
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
        RTerm::DTypNew { .. } => panic!(
          "substitution in datatype constructors is not implemented"
        ),

        RTerm::Cst(_) => current.clone(),
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

        RTerm::CArray { .. } |
        RTerm::DTypNew { .. } => return None,

        RTerm::Cst(_) => return None,
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

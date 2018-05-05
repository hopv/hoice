//! Term simplification.

pub use std::cmp::Ordering ;
use std::ops::Deref ;

use common::* ;



lazy_static! {
  static ref simpl_solver: RwLock<
    Option<::rsmt2::Solver<()>>
  > = RwLock::new(
    if conf.check_simpl {
      Some(
        conf.solver.spawn("check_simpl", (), & Instance::new()).unwrap()
      )
    } else {
      None
    }
  ) ;
}



/// Result of a simplification check between two terms.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum SimplRes {
  /// Nothing.
  None,
  /// The two terms are directly related.
  Cmp(Ordering),
  /// The two terms are equivalent to another term.
  Yields(Term),
}
impl SimplRes {
  /// Inverts the result.
  pub fn invert(self) -> Self {
    use self::SimplRes::* ;
    match self {
      None => None,
      Cmp(ord) => Cmp( ord.reverse() ),
      Yields(term) => Yields(term),
    }
  }
  /// True if `self` is not `None`.
  #[inline]
  pub fn is_some(& self) -> bool {
    self != & SimplRes::None
  }
  /// True if `self` is `None`.
  #[inline]
  pub fn is_none(& self) -> bool {
    ! self.is_some()
  }
}



/// Simplifies a conjunction.
pub fn conj_vec_simpl(mut terms: Vec<Term>) -> Vec<Term> {
  let mut res = Vec::with_capacity( terms.len() ) ;

  'add_terms: while let Some(term) = terms.pop() {

    let mut cnt = 0 ;

    'check_current: while cnt < res.len() {
      use self::SimplRes::* ;
      use std::cmp::Ordering::* ;

      match conj_simpl(& term, & res[cnt]) {
        None => cnt += 1,

        Cmp(Less) |
        Cmp(Equal) => continue 'add_terms,

        Cmp(Greater) => {
          res.swap_remove(cnt) ;
        },

        Yields(term) => {
          res.swap_remove(cnt) ;
          terms.push(term) ;
          continue 'add_terms
        },
      }
    }

    res.push(term)

  }

  res.shrink_to_fit() ;

  res
}




/// Checks the conjunction of two terms for simplification.
///
/// Returns
///
/// - `None` if no conclusion was reached,
/// - `Cmp(Greater)` if `lhs => rhs`,
/// - `Cmp(Less)` if `lhs <= rhs`,
/// - `Cmp(Equal)` if `lhs` and `rhs` are equivalent.
/// - `Yields(term)` if `lhs and rhs` is equivalent to `term`.
///
/// So *greater* really means *stronger*.
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering::* ;
/// use hoice::term::simplify::SimplRes::* ;
/// use hoice::term::simplify::conj_simpl ;
/// use hoice::term ;
///
/// let lhs = term::not(
///   term::lt(
///     term::int(0),
///     term::sub( vec![ term::int(3), term::int_var(0) ] )
///   )
/// ) ;
/// # println!("   {}", lhs) ;
/// let rhs = term::ge( term::int_var(0), term::int(3) ) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Equal) }
///
/// # println!("   {}", lhs) ;
/// let rhs = term::ge( term::int_var(0), term::int(7) ) ;
/// # println!("<= {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Less) }
///
/// # println!("   {}", rhs) ;
/// # println!("=> {}\n\n", lhs) ;
/// debug_assert_eq! { conj_simpl(& rhs, & lhs), Cmp(Greater) }
///
/// let lhs = term::gt( term::int_var(0), term::int(7) ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Greater) }
///
// / let lhs = term::le( term::int_var(0), term::int(7) ) ;
// / # println!("   {}", lhs) ;
// / # println!("=> {}\n\n", rhs) ;
// / let expected = term::eq( term::int_var(0), term::int(7) ) ;
// / debug_assert_eq! { conj_simpl(& lhs, & rhs), Yields(expected) }
///
/// let lhs = term::le( term::int_var(1), term::int(7) ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), None }
///
/// let lhs = term::le( term::int_var(1), term::int(7) ) ;
/// let rhs = term::or(
///   vec![ lhs.clone(), term::eq( term::int_var(3), term::int(7) ) ]
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Greater) }
///
/// # println!("   {}", rhs) ;
/// # println!("=> {}\n\n", lhs) ;
/// debug_assert_eq! { conj_simpl(& rhs, & lhs), Cmp(Less) }
/// ```
pub fn conj_simpl<T1, T2>(lhs: & T1, rhs: & T2) -> SimplRes
where T1: Deref<Target=RTerm>, T2: Deref<Target=RTerm> {

  if conf.term_simpl == 0 {
    return SimplRes::None
  }

  let res = conj_simpl_2(lhs, rhs) ;

  if res.is_some() {
    if let Some(solver) = simpl_solver.write().unwrap().as_mut() {
      solver.push(1).unwrap() ;
      let mut vars = VarSet::new() ;
      lhs.iter(
        |term| if let Some(idx) = term.var_idx() {
          let is_new = vars.insert(idx) ;
          if is_new {
            solver.declare_const(
              & format!("{}", term), term.typ().get()
            ).unwrap()
          }
        }
      ) ;
      rhs.iter(
        |term| if let Some(idx) = term.var_idx() {
          let is_new = vars.insert(idx) ;
          if is_new {
            solver.declare_const(
              & format!("{}", term), term.typ().get()
            ).unwrap()
          }
        }
      ) ;
      use std::cmp::Ordering::* ;
      let check = match res {
        SimplRes::Cmp(Equal) => format!(
          "(= {} {})", lhs.deref(), rhs.deref()
        ),
        SimplRes::Cmp(Less) => format!(
          "(=> {} {})", rhs.deref(), lhs.deref()
        ),
        SimplRes::Cmp(Greater) => format!(
          "(=> {} {})", lhs.deref(), rhs.deref()
        ),
        SimplRes::Yields(ref term) => format!(
          "(= (and {} {}) {})", lhs.deref(), rhs.deref(), term
        ),
        SimplRes::None => unreachable!(),
      } ;

      solver.assert(& format!("(not {})", check)).unwrap() ;

      if solver.check_sat().unwrap() {
        log! { @0
          " " ;
          "{}", lhs.deref() ;
          "{}", rhs.deref() ;
          "{:?}", res ;
          " "
        }
        panic! { "simplification failure" }
      }

      solver.pop(1).unwrap()
    }
  }

  match res {
    SimplRes::Yields(_) if conf.term_simpl <= 1 => SimplRes::None,
    res => res,
  }
}
pub fn conj_simpl_2<T1, T2>(lhs: & T1, rhs: & T2) -> SimplRes
where T1: Deref<Target=RTerm>, T2: Deref<Target=RTerm> {
  use std::cmp::Ordering::* ;

  if let Some(args) = lhs.disj_inspect() {
    for lhs in args {
      let mut greater_count = 0 ;
      let mut yields = vec![] ;
      match int_conj_simpl(lhs, rhs, true) {
        SimplRes::Cmp(Equal) |
        SimplRes::Cmp(Less) => return SimplRes::Cmp(Less),
        SimplRes::Cmp(Greater) => greater_count += 1,

        SimplRes::Yields(term) => yields.push(term),
        SimplRes::None => break,
      }
      if yields.len() == args.len() {
        return SimplRes::Yields( term::or(yields) )
      } else if greater_count == args.len() {
        return SimplRes::Cmp(Greater)
      }
    }
  } else if let Some(args) = rhs.disj_inspect() {
    for rhs in args {
      let mut less_count = 0 ;
      let mut yields = vec![] ;
      match int_conj_simpl(lhs, rhs, true) {
        SimplRes::Cmp(Equal) |
        SimplRes::Cmp(Greater) => return SimplRes::Cmp(Greater),
        SimplRes::Cmp(Less) => less_count += 1,

        SimplRes::Yields(term) => yields.push(term),
        SimplRes::None => break,
      }
      if yields.len() == args.len() {
        return SimplRes::Yields( term::or(yields) )
      } else if less_count == args.len() {
        return SimplRes::Cmp(Greater)
      }
    }
  }

  let res = int_conj_simpl(lhs, rhs, true) ;
  // if res.is_some() {
  //   log! { @0
  //     "\n\n{}", lhs.deref() ;
  //     "{}", rhs.deref() ;
  //     "{:?}", res
  //   }
  // }

  res
}


fn int_conj_simpl<T1, T2>(lhs: & T1, rhs: & T2, conj: bool) -> SimplRes
where T1: Deref<Target=RTerm>, T2: Deref<Target=RTerm> {
  use std::cmp::Ordering::* ;
  // Input boolean is true (false) for `lhs` => `rhs` (reversed).
  macro_rules! ord_of_bool {
    ($b:expr) => (
      if $b {
        SimplRes::Cmp(Greater)
      } else {
        SimplRes::Cmp(Less)
      }
    ) ;
  }

  let (lhs, rhs) = ( lhs.deref(), rhs.deref() ) ;

  // A term implies itself.
  if lhs == rhs { return SimplRes::Cmp(Equal) }

  match ( lhs.bool(), rhs.bool() ) {
    // True can only imply true.
    (Some(true), rhs) => return ord_of_bool!(
      rhs.unwrap_or(false)
    ),
    // False implies anything.
    (Some(false), _) => return ord_of_bool!(true),
    // False can only be implied by false.
    (lhs, Some(false)) => return ord_of_bool!(
      ! lhs.unwrap_or(true)
    ),
    // True is implied by anything.
    (_, Some(true)) => return ord_of_bool!(true),
    // Otherwise we don't know (yet).
    (None, None) => (),
  }

  // Only legal atoms are `vars >= cst` and `vars > cst`.
  let (
    lhs_op, lhs_vars, lhs_cst
  ) = if let Some((op, args)) = lhs.app_inspect() {
    if ! args[0].typ().is_arith() {
      return SimplRes::None
    }
    (op, & args[0], args[1].val().unwrap())
  } else {
    return SimplRes::None
  } ;
  let (
    rhs_op, rhs_vars, rhs_cst
  ) = if let Some((op, args)) = rhs.app_inspect() {
    if ! args[0].typ().is_arith() {
      return SimplRes::None
    }
    (op, & args[0], args[1].val().unwrap())
  } else {
    return SimplRes::None
  } ;

  if lhs_vars == rhs_vars {

    match (lhs_op, rhs_op) {
      (Op::Gt, Op::Gt) |
      (Op::Ge, Op::Ge) => return SimplRes::Cmp(
        lhs_cst.cmp(& rhs_cst).unwrap()
      ),

      (Op::Gt, Op::Ge) |
      (Op::Ge, Op::Gt) => if lhs_cst == rhs_cst {
        if lhs_op == Op::Gt {
          return SimplRes::Cmp(Less)
        } else {
          return SimplRes::Cmp(Greater)
        }
      } else {
        return SimplRes::Cmp(
          lhs_cst.cmp(& rhs_cst).unwrap().reverse()
        )
      },

      (Op::Eql, Op::Ge) |
      (Op::Eql, Op::Gt) => match lhs_cst.cmp(& rhs_cst) {
        Some(Less) => return SimplRes::Yields( term::fls() ),
        Some(Equal) if rhs_op == Op::Gt => if conj {
          return SimplRes::Yields( term::fls() )
        } else {
        },
        Some(Equal) |
        Some(Greater) => return SimplRes::Cmp(Greater),
        None => unreachable!(),
      },

      (Op::Ge, Op::Eql) |
      (Op::Gt, Op::Eql) => match rhs_cst.cmp(& lhs_cst) {
        Some(Less) => return SimplRes::Yields( term::fls() ),
        Some(Equal) if rhs_op == Op::Gt => return SimplRes::Yields(
          term::fls()
        ),
        Some(Equal) |
        Some(Greater) => return SimplRes::Cmp(Less),
        None => unreachable!(),
      },

      (Op::Eql, Op::Eql) => if rhs_cst == lhs_cst {
        return SimplRes::Cmp(Greater)
      } else {
        return SimplRes::Yields( term::fls() )
      },

      _ => unreachable!(),
    }

  } else

  if lhs_op == Op::Ge && rhs_op == Op::Ge
  && lhs_cst == rhs_cst.minus().unwrap()
  && rhs_vars == & term::u_minus( lhs_vars.clone() ) {

    if conj {
      return SimplRes::Yields(
        term::eq(lhs_vars.clone(), lhs_cst.to_term().unwrap())
      )
    } else {
      return SimplRes::Yields(
        term::tru()
      )
    }
  }

  SimplRes::None
}


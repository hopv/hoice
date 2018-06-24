//! Term simplification.

pub use std::cmp::Ordering ;
use std::ops::Deref ;

use term::factory::NormRes;

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


/// Adds a term to a set understood as a conjunction.
///
/// Returns `true` if the resulting set is false.
pub fn conj_term_insert(
  term: Term, set: & mut TermSet
) -> bool {

  let mut next_term = Some(term) ;
  let mut fls = false ;
  let mut add_term ;

  macro_rules! helper {
    (add term) => (
      next_term.is_none() && add_term
    ) ;

    (is false) => (fls) ;
    (term dropped) => (next_term.is_none() && ! add_term) ;
    (is true) => (! fls && helper!(term dropped)) ;

    (drop term) => ({
      next_term = None ;
      add_term = false
    }) ;

    (set false) => ({
      fls = true ;
      helper!(drop term)
    }) ;

    (set true) => ({
      debug_assert! { ! fls }
      helper!(drop term)
    }) ;

    (update $old_term:expr, to $term:expr) => ({
      $old_term = $term.clone() ;
      next_term = Some($term) ;
    }) ;
  }

  while let Some(mut term) = ::std::mem::replace(
    & mut next_term, None
  ) {
    add_term = true ;


    set.retain(
      |set_term| {
        if helper!(is false) {
          return false
        }
        if helper!(is true) {
          return true
        }

        use std::cmp::Ordering::* ;
        match conj_simpl(& term, set_term) {
          SimplRes::None => true,

          SimplRes::Cmp(Less) |
          SimplRes::Cmp(Equal) => {
            helper!(drop term) ;
            true
          },

          SimplRes::Cmp(Greater) => {
            false
          },

          SimplRes::Yields(nu_term) => match nu_term.bool() {
            Some(true) => {
              helper!(set true) ;
              false
            },
            Some(false) => {
              helper!(set false) ;
              false
            },
            None => {
              helper!(update term, to nu_term) ;
              false
            },
          },
        }
      }
    ) ;

    if helper!(add term) {
      let is_new = set.insert(term) ;
      debug_assert! { is_new }
    }
  }

  if fls {
    set.clear() ;
    set.insert( term::fls() ) ;
  }
  fls
}



/// Simplifies a conjunction.
pub fn conj_vec_simpl(terms: & mut Vec<Term>) {
  let mut res = Vec::with_capacity( terms.len() ) ;

  'add_terms: while let Some(term) = terms.pop() {

    let mut cnt = 0 ;

    while cnt < res.len() {
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
  res.sort_unstable() ;
  res.dedup() ;

  ::std::mem::swap(terms, & mut res)
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
/// ```rust
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
///
/// let lhs = term::gt( term::real_var(1), term::real_zero() ) ;
/// let rhs = term::ge(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Greater) }
///
/// # println!("   {}", rhs) ;
/// # println!("=> {}\n\n", lhs) ;
/// debug_assert_eq! { conj_simpl(& rhs, & lhs), Cmp(Less) }
///
/// let lhs = term::or(
///   vec![
///     term::bool_var(0), term::gt( term::real_var(1), term::real_zero() )
///   ]
/// ) ;
/// let rhs = term::ge(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), None }
///
/// let lhs = term::or(
///   vec![
///     term::bool_var(0), term::gt( term::real_var(1), term::real_zero() )
///   ]
/// ) ;
/// let rhs = term::eq(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), None }
///
/// let rhs = term::or(
///   vec![
///     term::bool_var(0), term::gt( term::real_var(1), term::real_zero() )
///   ]
/// ) ;
/// let lhs = term::eq(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// debug_assert_eq! { conj_simpl(& lhs, & rhs), None }
/// ```
pub fn conj_simpl<T1, T2>(lhs: & T1, rhs: & T2) -> SimplRes
where T1: Deref<Target=RTerm>, T2: Deref<Target=RTerm> {

  if conf.term_simpl == 0 {
    return SimplRes::None
  }

  let res = conj_simpl_2(lhs, rhs) ;

  if res.is_some() {

    if let Some(solver) = simpl_solver.write().expect(
      "could not retrieve term simplification solver"
    ).as_mut() {
      solver.push(1).expect(
        "error on `push` during term simplification"
      ) ;
      let mut vars = VarSet::new() ;
      lhs.iter(
        |term| if let Some(idx) = term.var_idx() {
          let is_new = vars.insert(idx) ;
          if is_new {
            solver.declare_const(
              & format!("{}", term), term.typ().get()
            ).expect(
              "error on `declare_const` during term simplification (lhs)"
            )
          }
        }
      ) ;
      rhs.iter(
        |term| if let Some(idx) = term.var_idx() {
          let is_new = vars.insert(idx) ;
          if is_new {
            solver.declare_const(
              & format!("{}", term), term.typ().get()
            ).expect(
              "error on `declare_const` during term simplification (rhs)"
            )
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

      solver.assert(& format!("(not {})", check)).expect(
        "error on `assert` during term simplification"
      ) ;

      if solver.check_sat().expect(
        "could not retrieve check-sat result in conjunction simplification"
      ) {
        log! { @0
          " " ;
          "{}", lhs.deref() ;
          "{}", rhs.deref() ;
          "{:?}", res ;
          " "
        }
        panic! { "simplification failure" }
      }

      solver.pop(1).expect(
        "error on `pop` during term simplification"
      )
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
    let mut greater_count = 0 ;
    let mut yields = vec![] ;
    for lhs in args {
      match int_conj_simpl(lhs, rhs, true) {
        SimplRes::Cmp(Equal) |
        SimplRes::Cmp(Less) => return SimplRes::Cmp(Less),
        SimplRes::Cmp(Greater) => greater_count += 1,

        SimplRes::Yields(term) => yields.push(term),
        SimplRes::None => (),
      }
    }
    if yields.len() == args.len() {
      return SimplRes::Yields( term::or(yields) )
    } else if greater_count == args.len() {
      return SimplRes::Cmp(Greater)
    }
  } else if let Some(args) = rhs.disj_inspect() {
    let mut less_count = 0 ;
    let mut yields = vec![] ;
    for rhs in args {
      match int_conj_simpl(lhs, rhs, true) {
        SimplRes::Cmp(Equal) |
        SimplRes::Cmp(Greater) => return SimplRes::Cmp(Greater),
        SimplRes::Cmp(Less) => less_count += 1,

        SimplRes::Yields(term) => yields.push(term),
        SimplRes::None => (),
      }
    }
    if yields.len() == args.len() {
      return SimplRes::Yields( term::or(yields) )
    } else if less_count == args.len() {
      return SimplRes::Cmp(Greater)
    }
  }

  int_conj_simpl(lhs, rhs, true)
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
  if lhs == rhs {
    return SimplRes::Cmp(Equal)
  }

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
    (
      op,
      & args[0],
      args[1].val().expect(
        "error during value unwrapping in term simplification (lhs)"
      ),
    )
  } else {
    return SimplRes::None
  } ;
  let (
    rhs_op, rhs_vars, rhs_cst
  ) = if let Some((op, args)) = rhs.app_inspect() {
    if ! args[0].typ().is_arith() {
      return SimplRes::None
    }
    (
      op,
      & args[0],
      args[1].val().expect(
        "error during value unwrapping in term simplification (rhs)"
      ),
    )
  } else {
    return SimplRes::None
  } ;

  if lhs_vars == rhs_vars {

    match (lhs_op, rhs_op) {
      (Op::Gt, Op::Gt) |
      (Op::Ge, Op::Ge) => return SimplRes::Cmp(
        lhs_cst.get().compare(& rhs_cst).expect(
          "error during comparison unwrapping in term simplification (same op)"
        )
      ),

      (Op::Gt, Op::Ge) |
      (Op::Ge, Op::Gt) => if lhs_cst == rhs_cst {
        if lhs_op == Op::Gt {
          return SimplRes::Cmp(Greater)
        } else {
          return SimplRes::Cmp(Less)
        }
      } else {
        return SimplRes::Cmp(
          lhs_cst.get().compare(& rhs_cst).expect(
          "error during comparison unwrapping in term simplification (diff op)"
        )
        )
      },

      (Op::Eql, Op::Ge) |
      (Op::Eql, Op::Gt) => match lhs_cst.get().compare(& rhs_cst) {
        Some(Less) => return SimplRes::Yields( term::fls() ),
        Some(Equal) if rhs_op == Op::Gt => if conj {
          return SimplRes::Yields( term::fls() )
        },
        Some(Equal) |
        Some(Greater) => return SimplRes::Cmp(Greater),
        None => unreachable!(),
      },

      (Op::Ge, Op::Eql) |
      (Op::Gt, Op::Eql) => match rhs_cst.get().compare(& lhs_cst) {
        Some(Less) => return SimplRes::Yields( term::fls() ),
        Some(Equal) if lhs_op == Op::Gt => return SimplRes::Yields(
          term::fls()
        ),
        Some(Equal) |
        Some(Greater) => return SimplRes::Cmp(Less),
        None => unreachable!(),
      },

      (Op::Eql, Op::Eql) => if rhs_cst.equal(& lhs_cst) {
        return SimplRes::Cmp(Greater)
      } else {
        return SimplRes::Yields( term::fls() )
      },

      _ => (),
    }

  } else if lhs_op == Op::Ge && rhs_op == Op::Ge
  && lhs_cst == rhs_cst.minus().expect(
    "error during rhs inversion in term simplification"
  )
  && rhs_vars == & term::u_minus( lhs_vars.clone() ) {

    if conj {
      return SimplRes::Yields(
        term::eq(
          lhs_vars.clone(), lhs_cst.to_term().expect(
            "error during lhs cst to term conversion in term simplification"
          )
        )
      )
    } else {
      return SimplRes::Yields(
        term::tru()
      )
    }
  }

  SimplRes::None
}




/// Fails if the number of arguments is wrong.
macro_rules! arity {
  ($op:expr => $args:expr, $len:expr) => (
    if $args.len() != $len {
      panic!(
        "illegal application of `{}` to {} arguments", $op, $args.len()
      )
    }
  ) ;
}
macro_rules! simpl_fun {
  ( $(fn $name:ident($args:pat) $body:expr);* $(;)* ) => (
    $(
      pub fn $name($args: & mut Vec<Term>) -> Option<NormRes> {
        $body
      }
    )*
  ) ;
}


// Polymorphic operations.

simpl_fun! {
  // Equal.
  fn eql(args) {
    if args.len() == 2 {

      if args[0] == args[1] {
        return Some(
          NormRes::Term( term::tru() )
      )

      } else if let Some(b) = args[0].bool() {

        return Some(
          NormRes::Term(
            if b {
              args[1].clone()
            } else {
              term::not( args[1].clone() )
            }
          )
        )

      } else if let Some(b) = args[1].bool() {

        return Some(
          NormRes::Term(
            if b {
              args[0].clone()
            } else {
              term::not( args[0].clone() )
            }
          )
        )

      } else if let (Some(r_1), Some(r_2)) = (
        args[0].real(), args[1].real()
      ) {

        return Some(
          NormRes::Term( term::bool( r_1 == r_2 ) )
        )

      } else if let (Some(i_1), Some(i_2)) = (
        args[0].int(), args[1].int()
      ) {

        return Some(
          NormRes::Term( term::bool( i_1 == i_2 ) )
        )

      } else if args[0].typ().is_arith() {

        // println!("  (= {} {})", args[0], args[1]) ;
        if ! args[1].is_zero() {
          let (rhs, lhs) = (args.pop().unwrap(), args.pop().unwrap()) ;
          let typ = rhs.typ() ;
          let lhs = if lhs.is_zero() { NormRes::Term(rhs) } else {
            NormRes::App(
              typ.clone(), Op::Sub, vec![
                NormRes::Term(lhs), NormRes::Term(rhs)
              ]
            )
          } ;
          return Some(
            NormRes::App(
              typ::bool(), Op::Eql, vec![
                lhs, NormRes::Term( typ.default_val().to_term().unwrap() )
              ]
            )
          )
        } else {
          // Rhs is zero, now normalize lhs. This is a bit ugly...
          let mut u_minus_lhs = term::u_minus(args[0].clone()) ;
          if u_minus_lhs.uid() < args[0].uid() {
            ::std::mem::swap(& mut args[0], & mut u_minus_lhs)
          }
        }

      }

    } else {

      args.sort_unstable() ;
      let len = args.len() ;
      let mut args = args.drain(0..) ;
      let mut conj = vec![] ;
      if let Some(first) = args.next() {
        for arg in args {
          conj.push(
            NormRes::App(
              typ::bool(), Op::Eql, vec![
                NormRes::Term( first.clone() ),
                NormRes::Term(arg)
              ]
            )
          )
        }
        if ! conj.is_empty() {
          return Some(
            NormRes::App(typ::bool(), Op::And, conj)
          )
        }
      }
      panic!(
        "illegal application of `=` to {} (< 2) argument", len
      )
    }

    None
  } ;

  // If-then-else.
  fn ite(args) {
    arity!("ite" => args, 3) ;
    if let Some(b) = args[0].bool() {
      return Some(
        NormRes::Term(
          if b { args[1].clone() } else { args[2].clone() }
        )
      )
    }
    if args[1] == args[2] {
      return Some(
        NormRes::Term( args[1].clone() )
      )
    }
    None
  } ;

  // Distinct.
  fn distinct(args) {
    if args.len() == 2 {
      return Some(
        NormRes::App(
          typ::bool(), Op::Not, vec![
            NormRes::App(
              typ::bool(), Op::Eql, args.drain(0..).map(
                NormRes::Term
              ).collect()
            ),
          ]
        )
      )
    } else {
      args.sort_unstable() ;
      None
    }
  }
}


// Boolean operations.

simpl_fun! {
  fn and(args) {
    args.sort_unstable() ;
    args.dedup() ;

    let mut cnt = 0 ;
    
    while cnt < args.len() {
      if let Some(b) = args[cnt].bool() {
        if b {
          args.swap_remove(cnt) ;
          ()
        } else {
          return Some(
            NormRes::Term( term::fls() )
          )
        }
      } else if let Some(conj) = args[cnt].conj_inspect().cloned() {
        for term in conj {
          args.push(term)
        }
        args.swap_remove(cnt) ;
        args.sort_unstable() ;
        args.dedup() ;
        cnt = 0
      } else {
        cnt += 1
      }
    }

    // if conf.term_simpl >= 3 {
      conj_vec_simpl(args) ;
    // }

    if args.is_empty() {
      return Some(
        NormRes::Term( term::tru() )
      )
    } else if args.len() == 1 {
      return Some(
        NormRes::Term( args.pop().unwrap() )
      )
    }

    None
  }
}



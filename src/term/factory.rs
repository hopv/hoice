//! Term creation functions.

use hashconsing::{ HashConsign, HConser } ;

use common::* ;
use term::{ RTerm, Term, Op } ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<RTerm> > ;

lazy_static! {
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa )
  ) ;
}

lazy_static! {
  /// Cache for terms' variables.
  static ref var_cache: RwLock< HConMap<Term, VarSet> > = RwLock::new(
    HConMap::with_capacity( conf.instance.term_capa )
  ) ;
}


/// Scans a term to extract the variables that appear in it.
fn scan_vars(t: & Term) -> VarSet {
  let mut to_do = vec![ t ] ;
  let mut set = VarSet::with_capacity(11) ;
  while let Some(term) = to_do.pop() {
    match ** term {
      RTerm::Var(i) => {
        let _ = set.insert(i) ; ()
      },
      RTerm::Int(_) => (),
      RTerm::Real(_) => (),
      RTerm::Bool(_) => (),
      RTerm::App{ ref args, .. } => for arg in args {
        to_do.push(arg)
      },
    }
  }
  set.shrink_to_fit() ;
  set
}

/// Variables appearing in a term (cached).
#[inline]
pub fn vars(t: & Term) -> VarSet {
  if let Some(vars) = var_cache.read().expect(
    "variable cache is corrupted..."
  ).get(t) {
    return vars.clone()
  }
  var_cache.write().expect(
    "variable cache is corrupted..."
  ).entry( t.clone() ).or_insert_with(
    || scan_vars(t)
  ).clone()
}

/// Creates a term.
#[inline(always)]
pub fn term(t: RTerm) -> Term {
  factory.mk(t)
}

/// Creates a variable.
#[inline(always)]
pub fn var<V: Into<VarIdx>>(v: V) -> Term {
  factory.mk( RTerm::Var(v.into()) )
}

/// Creates an integer constant.
#[inline(always)]
pub fn int<I: Into<Int>>(i: I) -> Term {
  factory.mk(
    RTerm::Int( i.into() )
  )
}
/// Creates a real constant.
#[inline(always)]
pub fn real<R: Into<Rat>>(r: R) -> Term {
  let r = r.into() ;
  let r = if r.numer().is_negative() == r.denom().is_negative() {
    r
  } else {
    - r.abs()
  } ;
  factory.mk( RTerm::Real(r) )
}
/// Creates the constant `0`.
#[inline(always)]
pub fn zero() -> Term {
  int( Int::zero() )
}
/// Creates the constant `1`.
#[inline(always)]
pub fn one() -> Term {
  int( Int::one() )
}

/// Creates a boolean.
#[inline(always)]
pub fn bool(b: bool) -> Term {
  factory.mk( RTerm::Bool(b) )
}
/// Creates the constant `true`.
#[inline(always)]
pub fn tru() -> Term {
  bool(true)
}
/// Creates the constant `false`.
#[inline(always)]
pub fn fls() -> Term {
  bool(false)
}

/// If-then-else.
#[inline(always)]
pub fn ite(c: Term, t: Term, e: Term) -> Term {
  app(Op::Ite, vec![c, t, e])
}

/// Implication.
#[inline(always)]
pub fn implies(lhs: Term, rhs: Term) -> Term {
  app(Op::Impl, vec![lhs, rhs])
}

/// Negates a term.
#[inline(always)]
pub fn not(term: Term) -> Term {
  app(Op::Not, vec![term])
}
/// Disjunction.
#[inline(always)]
pub fn or(terms: Vec<Term>) -> Term {
  app(Op::Or, terms)
}
/// Conjunction.
#[inline(always)]
pub fn and(terms: Vec<Term>) -> Term {
  app(Op::And, terms)
}

/// Creates an operator application.
///
/// Runs [`normalize`](fn.normalize.html) and returns its result.
#[inline(always)]
pub fn app(op: Op, args: Vec<Term>) -> Term {
  normalize(op, args)
}

/// Creates a less than or equal to.
#[inline(always)]
pub fn le(lhs: Term, rhs: Term) -> Term {
  app(Op::Le, vec![lhs, rhs])
}
/// Creates a less than.
#[inline(always)]
pub fn lt(lhs: Term, rhs: Term) -> Term {
  app(Op::Lt, vec![lhs, rhs])
}
/// Creates a greater than.
#[inline(always)]
pub fn gt(lhs: Term, rhs: Term) -> Term {
  app(Op::Gt, vec![lhs, rhs])
}
/// Creates a greater than or equal to.
#[inline(always)]
pub fn ge(lhs: Term, rhs: Term) -> Term {
  app(Op::Ge, vec![lhs, rhs])
}

/// Creates an equality.
#[inline(always)]
pub fn eq(lhs: Term, rhs: Term) -> Term {
  app(Op::Eql, vec![lhs, rhs])
}

/// Creates a sum.
#[inline(always)]
pub fn add(kids: Vec<Term>) -> Term {
  app(Op::Add, kids)
}
/// Creates a subtraction.
#[inline(always)]
pub fn sub(kids: Vec<Term>) -> Term {
  app(Op::Sub, kids)
}
/// Creates a unary minus.
#[inline(always)]
pub fn u_minus(kid: Term) -> Term {
  app(Op::Sub, vec![kid])
}
/// Creates a multiplication.
#[inline(always)]
pub fn mul(kids: Vec<Term>) -> Term {
  app(Op::Mul, kids)
}
/// Creates a division.
#[inline(always)]
pub fn div(kids: Vec<Term>) -> Term {
  app(Op::IDiv, kids)
}
/// Creates a modulo application.
#[inline(always)]
pub fn modulo(a: Term, b: Term) -> Term {
  app(Op::Mod, vec![a, b])
}

/// Creates a conversion from `Int` to `Real`.
#[inline(always)]
pub fn to_real(int: Term) -> Term {
  app(Op::ToReal, vec![int])
}
/// Creates a conversion from `Real` to `Int`.
#[inline(always)]
pub fn to_int(real: Term) -> Term {
  app(Op::ToInt, vec![real])
}







/// Simplifies operator applications.
///
/// This function is currently not strongly-normalizing.
///
/// # Examples
///
/// ```rust
/// use hoice::term ;
///
/// let tru = term::tru() ;
/// let fls = term::fls() ;
/// 
/// let var_1 = term::var(7) ;
/// let n_var_1 = term::not( var_1.clone() ) ;
/// let var_2 = term::var(2) ;
/// let n_var_2 = term::not( var_2.clone() ) ;
///
/// let int_1 = term::int(3) ;
/// let int_2 = term::int(42) ;
///
///
/// // |===| `And` and `Or`.
///
/// // Nullary.
/// assert_eq!( tru, term::and( vec![] ) ) ;
/// assert_eq!( fls, term::or( vec![] ) ) ;
///
/// // Unary.
/// assert_eq!( var_2, term::and( vec![ var_2.clone() ] ) ) ;
/// assert_eq!( var_1, term::or( vec![ var_1.clone() ] ) ) ;
///
/// // Trivial.
/// assert_eq!(
///   fls, term::and( vec![ var_1.clone(), fls.clone(), var_2.clone() ] )
/// ) ;
/// assert_eq!(
///   tru, term::or( vec![ var_1.clone(), tru.clone(), var_2.clone() ] )
/// ) ;
///
///
/// // |===| `Ite`.
///
/// // Trivial.
/// assert_eq!(
///   var_1, term::ite( tru.clone(), var_1.clone(), var_2.clone() )
/// ) ;
/// assert_eq!(
///   var_2, term::ite( fls.clone(), var_1.clone(), var_2.clone() )
/// ) ;
/// assert_eq!( // Same `then` and `else`.
///   var_1, term::ite( var_2.clone(), var_1.clone(), var_1.clone() )
/// ) ;
///
///
/// // |===| `Not`.
///
/// // Double negation.
/// assert_eq!( var_1, term::not( n_var_1.clone() ) ) ;
/// assert_eq!( n_var_1, term::not( var_1.clone() ) ) ;
///
/// // `And` and `Or` propagation.
/// let and = term::and( vec![ var_1.clone(), var_2.clone() ] ) ;
/// let or = term::or( vec![ var_1.clone(), var_2.clone() ] ) ;
/// let n_and = term::not( and.clone() ) ;
/// let n_or = term::not( or.clone() ) ;
/// let and_n = term::and( vec![ n_var_1.clone(), n_var_2.clone() ] ) ;
/// let or_n = term::or( vec![ n_var_1.clone(), n_var_2.clone() ] ) ;
/// assert_eq!( n_and, or_n ) ;
/// assert_eq!( n_or, and_n ) ;
/// assert_eq!( and, term::not( or_n ) ) ;
/// assert_eq!( and, term::not( n_and ) ) ;
/// assert_eq!( or, term::not( and_n ) ) ;
/// assert_eq!( or, term::not( n_or ) ) ;
///
///
/// // |===| `Eql`.
///
/// // `t_1 = t_1`.
/// assert_eq!( tru, term::eq(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( tru, term::eq(int_1.clone(), int_1.clone()) ) ;
/// // `n != m` with `n` and `m` integers.
/// assert_eq!( fls, term::eq(int_1.clone(), int_2.clone()) ) ;
/// // `true = t`.
/// assert_eq!( var_1, term::eq(tru.clone(), var_1.clone()) ) ;
/// // `false = t`.
/// assert_eq!( n_var_1, term::eq(fls.clone(), var_1.clone()) ) ;
///
///
/// // |===| `Ge`, `Le`, `Lt` and `Gt`.
///
/// assert_eq!( tru, term::ge(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( tru, term::le(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( fls, term::gt(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( fls, term::lt(var_1.clone(), var_1.clone()) ) ;
///
/// assert_eq!( fls, term::ge(int_1.clone(), int_2.clone()) ) ;
/// assert_eq!( tru, term::le(int_1.clone(), int_2.clone()) ) ;
/// assert_eq!( fls, term::gt(int_1.clone(), int_2.clone()) ) ;
/// assert_eq!( tru, term::lt(int_1.clone(), int_2.clone()) ) ;
/// ```
pub fn normalize(
  op: Op, args: Vec<Term>
) -> Term {

  // Contains stack frames composed of
  //
  // - the operator `op` to apply,
  // - a vector of operators to apply to some arguments before applying `op`
  // - the arguments to apply `op`, basically storing the results of the
  //   applications from the second element
  //
  // It is important that the second, `to_do`, element of the frames is in
  // **reverse order**. This is because its elements will be `pop`ped and
  // `push`ed on the third element.
  //
  // (It actually doesn't matter that much right now as `normalize_app` only
  // works on symmetric operators, but still.)
  let mut stack = vec![ (op, vec![], args) ] ;

  while let Some((op, mut to_do, args)) = stack.pop() {

    if let Some( (nu_op, nu_args) ) = to_do.pop() {

      stack.push( (op, to_do, args) ) ;
      stack.push( (nu_op, vec![], nu_args) )

    } else {

      match normalize_app(op, args) {
        // Going down...
        Either::Right((op, mut to_do)) => {
          let args = Vec::with_capacity( to_do.len() ) ;
          to_do.reverse() ;
          stack.push( (op, to_do, args) )
        },
        // Going up...
        Either::Left(term) => if let Some(
          & mut ( _, _, ref mut args )
        ) = stack.last_mut() {
          args.push( term )
        } else {
          return term
        },
      }

    }
  }

  unreachable!()
}


/// Normalizes an operation application.
fn normalize_app(
  op: Op, mut args: Vec<Term>
) -> Either<Term, (Op, Vec<(Op, Vec<Term>)>)> {
  use num::Zero ;

  let (op, args) = match op {

    Op::Ite => if args.len() == 3 {
      if let Some(b) = args[0].bool() {
        return Either::Left(
          if b { args[1].clone() } else { args[2].clone() }
        )
      }
      if args[1] == args[2] {
        return Either::Left( args[1].clone() )
      }
      (op, args)
    } else {
      panic!("trying to apply ite operator to {} (!= 3) arguments", args.len())
    },

    Op::And => {
      let mut cnt = 0 ;
      while cnt < args.len() {
        if let Some(b) = args[cnt].bool() {
          if b {
            args.swap_remove(cnt) ;
          } else {
            return Either::Left( fls() )
          }
        } else {
          cnt += 1
        }
      }
      if args.is_empty() {
        return Either::Left( term::tru() )
      } else if args.len() == 1 {
        return Either::Left( args.pop().unwrap() )
      } else {
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::Or => {
      let mut cnt = 0 ;
      while cnt < args.len() {
        if let Some(b) = args[cnt].bool() {
          if ! b {
            args.swap_remove(cnt) ;
          } else {
            return Either::Left( tru() )
          }
        } else {
          cnt += 1
        }
      }
      if args.is_empty() {
        return Either::Left( term::fls() )
      } else if args.len() == 1 {
        return Either::Left( args.pop().unwrap() )
      } else {
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::Not => {
      assert!( args.len() == 1 ) ;
      if let Some(b) = args[0].bool() {
        return Either::Left( bool(! b) )
      }
      match * args[0] {
        RTerm::App { op: Op::Not, ref args } => {
          return Either::Left( args[0].clone() )
        },
        RTerm::App { op: Op::And, ref args } => {
          return Either::Right((
            Op::Or, args.iter().map(
              |arg| (Op::Not, vec![arg.clone()])
            ).collect()
          ))
        },
        RTerm::App { op: Op::Or, ref args } => {
          return Either::Right((
            Op::And, args.iter().map(
              |arg| (Op::Not, vec![arg.clone()])
            ).collect()
          ))
        },
        _ => (),
      }
      (op, args)
    },

    Op::Eql => {
      if args.len() == 2 {
        if args[0] == args[1] {
          return Either::Left( tru() )
        } else if let Some(b) = args[0].bool() {
          return Either::Left(
            if b {
              args[1].clone()
            } else {
              not( args[1].clone() )
            }
          )
        } else if let Some(b) = args[1].bool() {
          return Either::Left(
            if b {
              args[0].clone()
            } else {
              not( args[0].clone() )
            }
          )
        // } else if args[0].is_relation() {
        //   return Either::Right((
        //     Op::Or, vec![
        //       ( Op::And, args.clone() ),
        //       (
        //         Op::And, args.iter().map(
        //           |arg| ( not(arg.clone()) )
        //           //      ^^^^^^^^^^^^^^^^
        //           // This is essentially a recursive call... it sucks :(
        //         ).collect()
        //       )
        //     ]
        //   ))
        } else if let (Some(i_1), Some(i_2)) = (args[0].int(), args[1].int()) {
          return Either::Left( term::bool( i_1 == i_2 ) )
        }
      }
      args.sort_unstable() ;
      (op, args)
    },

    Op::Sub => {
      if args.len() == 1 {
        if let Some(i) = args[0].int_val() {
          return Either::Left( int(- i) )
        } else if let Some(r) = args[0].rat_val() {
          return Either::Left( real( -r ) )
        }
      }
      (op, args)
    },

    Op::Add => {
      let mut cnt = 0 ;
      if args.is_empty() {
        panic!("trying to construct an empty sum")
      }
      let mut sum: Int = 0.into() ;
      while cnt < args.len() {
        if let Some(i) = args[cnt].int_val().map( |v| v.clone() ) {
          args.swap_remove(cnt) ;
          sum = sum + i
        } else {
          cnt += 1
        }
      }
      if args.len() == 0 {
        return Either::Left( int(sum) )
      } else if args.len() == 1 && sum.is_zero() {
        return Either::Left( args.pop().unwrap() )
      } else {
        if ! sum.is_zero() {
          args.push( int(sum) )
        }
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::Mul => {
      let mut cnt = 0 ;
      if args.is_empty() {
        panic!("trying to construct an empty mul")
      }
      let mut mul: Int = 1.into() ;
      while cnt < args.len() {
        if let Some(i) = args[cnt].int_val().map( |v| v.clone() ) {
          if i.is_zero() {
            return Either::Left( int( i.clone() ) )
          }
          args.swap_remove(cnt) ;
          mul = mul * i
        } else {
          cnt += 1
        }
      }
      if args.len() == 0 || mul.is_zero() {
        return Either::Left( int(mul) )
      } else if args.len() == 1 && mul == 1.into() {
        return Either::Left( args.pop().unwrap() )
      } else {
        if mul != 1.into() {
          args.push( int(mul) )
        }
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::IDiv => {
      if args.len() == 2 {
        if let Some(i) = args[0].int() {
          if i.is_zero() {
            return Either::Left( int(i) )
          }
        }
        if let Some(i) = args[1].int() {
          use num::FromPrimitive ;
          if Some(i) == Int::from_usize(1) {
            return Either::Left( args[0].clone() )
          }
        }
      }
      (op, args)
    },

    Op::Ge => if args.len() == 2 {
      if args[0] == args[1] {
        return Either::Left( tru() )
      } else if let (Some(lhs), Some(rhs)) = (args[0].int(), args[1].int()) {
        return Either::Left( bool(lhs >= rhs) )
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::Gt => if args.len() == 2 {
      if args[0] == args[1] {
        return Either::Left( fls() )
      } else if let (Some(lhs), Some(rhs)) = (args[0].int(), args[1].int()) {
        return Either::Left( bool(lhs > rhs) )
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::Le => if args.len() == 2 {
      if args[0] == args[1] {
        return Either::Left( tru() )
      } else if let (Some(lhs), Some(rhs)) = (args[0].int(), args[1].int()) {
        return Either::Left( bool(lhs <= rhs) )
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::Lt => if args.len() == 2 {
      if args[0] == args[1] {
        return Either::Left( fls() )
      } else if let (Some(lhs), Some(rhs)) = (args[0].int(), args[1].int()) {
        return Either::Left( bool(lhs < rhs) )
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::Mod => if args.len() == 2 {
      if let Some(i) = args[1].int() {
        if i == 1.into() {
          return Either::Left( term::int(0) )
        } else {
          (op, args)
        }
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    // Not implemented.
    Op::Div => panic!("simplification of division is not implemented"),

    Op::Rem |
    Op::ToInt |
    Op::ToReal |
    Op::Impl => (op, args),

  } ;

  Either::Left( factory.mk( RTerm::App { op, args } ) )
}

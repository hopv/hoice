//! Term creation functions.

use hashconsing::{ HashConsign, HConser } ;

use common::* ;
use term::{ RTerm, Term, Op } ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<RTerm> > ;

lazy_static!{
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa )
  ) ;
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
/// Creates a multiplication.
#[inline(always)]
pub fn mul(kids: Vec<Term>) -> Term {
  app(Op::Mul, kids)
}








#[doc = r#"Tries to normalize an operator application.

# Nullary / unary applications of `And` and `Or`

```
use hoice::term ;
use hoice::term::Op::* ;

let tru = term::bool(true) ;
let fls = term::bool(false) ;
let var_1 = term::var(7) ;
let var_2 = term::var(2) ;

assert_eq!( tru, term::normalize(And, vec![]) ) ;
assert_eq!( fls, term::normalize(Or, vec![]) ) ;
assert_eq!( var_2, term::normalize(And, vec![ var_2.clone() ]) ) ;
assert_eq!( var_1, term::normalize(Or, vec![ var_1.clone() ]) ) ;

let and = term::app(And, vec![ var_2.clone(), var_1.clone() ]) ;
assert_eq!(
  and, term::normalize(And, vec![ var_2.clone(), var_1.clone() ])
) ;
let or = term::app(Or, vec![ var_2.clone(), var_1.clone() ]) ;
assert_eq!(
  or, term::normalize(Or, vec![ var_2.clone(), var_1.clone() ])
) ;
```

# Double negations

```
use hoice::term ;
use hoice::term::Op::* ;

let var_1 = term::var(7) ;
let n_var_1 = term::app( Not, vec![ var_1.clone() ] ) ;
assert_eq!( var_1, term::normalize(Not, vec![ n_var_1 ]) ) ;

let var_1 = term::var(7) ;
let n_var_1 = term::app( Not, vec![ var_1.clone() ] ) ;
assert_eq!( n_var_1, term::normalize(Not, vec![ var_1 ]) ) ;
```
"#]
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
      (op, args)
    },

    Op::Add => {
      let mut cnt = 0 ;
      if args.is_empty() {
        panic!("trying to construct an empty sum")
      }
      let mut sum: Int = 0.into() ;
      while cnt < args.len() {
        if let Some(i) = args[cnt].int_val() {
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
        args.push( int(sum) ) ;
        (op, args)
      }
    },

    Op::Mul => {
      let mut cnt = 0 ;
      if args.is_empty() {
        panic!("trying to construct an empty sum")
      }
      let mut mul: Int = 1.into() ;
      while cnt < args.len() {
        if let Some(i) = args[cnt].int_val() {
          if i.is_zero() {
            return Either::Left( int(i) )
          }
          args.swap_remove(cnt) ;
          mul = mul * i
        } else {
          cnt += 1
        }
      }
      if args.len() == 0 {
        return Either::Left( int(mul) )
      } else if args.len() == 1 && mul.is_zero() {
        return Either::Left( args.pop().unwrap() )
      } else {
        args.push( int(mul) ) ;
        (op, args)
      }
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
    

    _ => (op, args),

  } ;

  Either::Left( factory.mk( RTerm::App { op, args } ) )
}

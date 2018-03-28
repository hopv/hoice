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
      RTerm::Var(_, i) => {
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

/// Map over the variables appearing in a term (cached).
#[inline]
pub fn map_vars<F>(t: & Term, mut f: F)
where F: FnMut(VarIdx) {
  if let Some(vars) = var_cache.read().expect(
    "variable cache is corrupted..."
  ).get(t) {
    for var in vars {
      f(* var)
    }
    return ()
  }

  let vars = scan_vars(t) ;
  for var in & vars {
    f(* var)
  }
  var_cache.write().expect(
    "variable cache is corrupted..."
  ).entry( t.clone() ).or_insert_with(
    || vars
  ) ;
  ()
}

/// Creates a term.
#[inline(always)]
pub fn term(t: RTerm) -> Term {
  factory.mk(t)
}

/// Creates a variable.
#[inline(always)]
pub fn var<V: Into<VarIdx>>(v: V, typ: Typ) -> Term {
  factory.mk( RTerm::Var(typ, v.into()) )
}

/// Creates an integer variable.
#[inline(always)]
pub fn int_var<V: Into<VarIdx>>(v: V) -> Term {
  factory.mk( RTerm::Var(Typ::Int, v.into()) )
}

/// Creates a real variable.
#[inline(always)]
pub fn real_var<V: Into<VarIdx>>(v: V) -> Term {
  factory.mk( RTerm::Var(Typ::Real, v.into()) )
}

/// Creates a boolean variable.
#[inline(always)]
pub fn bool_var<V: Into<VarIdx>>(v: V) -> Term {
  factory.mk( RTerm::Var(Typ::Bool, v.into()) )
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
  if r.denom().is_zero() {
    panic!("division by zero while constructing real term")
  }
  let r = if r.numer().is_negative() == r.denom().is_negative() {
    r
  } else {
    - r.abs()
  } ;
  factory.mk( RTerm::Real(r) )
}
/// Creates the constant `0`.
#[inline(always)]
pub fn int_zero() -> Term {
  int( Int::zero() )
}
/// Creates the constant `1`.
#[inline(always)]
pub fn int_one() -> Term {
  int( Int::one() )
}
/// Creates the constant `0`.
#[inline(always)]
pub fn real_zero() -> Term {
  real( Rat::zero() )
}
/// Creates the constant `1`.
#[inline(always)]
pub fn real_one() -> Term {
  real( Rat::one() )
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
/// Assumes the application is well-typed, modulo int to real casting.
///
/// Runs [`normalize`](fn.normalize.html) and returns its result.
#[inline(always)]
pub fn app(op: Op, args: Vec<Term>) -> Term {
  let typ = expect!(
    op.type_check(& args) => |e|
      let res: Res<()> = Err(
        "Fatal internal type checking error, \
        please notify the developer(s)".into()
      ) ;
      match e {
        Either::Left((exp, (found, index))) => res.chain_err(
          || format!(
            "expected an expression of sort {}, found {} ({})",
            exp.map(|t| format!("{}", t)).unwrap_or("?".into()),
            args[index], found
          )
        ).chain_err(
          || "in this operator application"
        ).chain_err(
          || {
            use std::io::Write ;
            let buff = & mut Vec::new() ;
            write!(buff, "({}", op).unwrap() ;
            for arg in args {
              write!(buff, " {}[{}]", arg, arg.typ()).unwrap()
            }
            write!(buff, ")").unwrap() ;
            String::from_utf8_lossy(buff).into_owned()
          }
        ),
        Either::Right(blah) => res.chain_err(|| blah)
      }.unwrap_err()
  ) ;
  let term = normalize(op, args, typ) ;
  // println!("{}: {}", term, typ) ;
  term
}

/// Creates an operator application.
///
/// Error if the application is ill-typed (int will be cast to real
/// automatically).
///
/// Runs [`normalize`](fn.normalize.html) and returns its result.
#[inline(always)]
pub fn try_app(op: Op, args: Vec<Term>) -> Result<
  Term, Either< (Option<Typ>, (Typ, usize)), String >
> {
  let typ = op.type_check(& args) ? ;
  Ok( normalize(op, args, typ) )
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
/// Creates an integer division.
#[inline(always)]
pub fn idiv(kids: Vec<Term>) -> Term {
  app(Op::IDiv, kids)
}
/// Creates a division.
#[inline(always)]
pub fn div(kids: Vec<Term>) -> Term {
  app(Op::Div, kids)
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
/// let var_1 = term::bool_var(7) ;
/// let n_var_1 = term::not( var_1.clone() ) ;
/// let var_2 = term::bool_var(2) ;
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
/// let var_1 = term::int_var(7) ;
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
fn normalize(
  op: Op, args: Vec<Term>, typ: Typ
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
  let mut stack = vec![ (typ, op, vec![], args) ] ;

  'go_down: while let Some((typ, op, mut to_do, mut args)) = stack.pop() {

    'do_stuff: loop {

      match to_do.pop() {
        Some( NormRes::Term(term) ) => {
          args.push(term) ;
          continue 'do_stuff
        },

        Some( NormRes::App(nu_typ, nu_op, mut nu_to_do) ) => {
          stack.push( (typ, op, to_do, args) ) ;
          let nu_args = Vec::with_capacity( nu_to_do.len() ) ;
          nu_to_do.reverse() ;
          stack.push( (nu_typ, nu_op, nu_to_do, nu_args) ) ;
          continue 'go_down
        },

        None => match normalize_app(op, args, typ) {
          // Going down...
          NormRes::App(typ, op, mut to_do) => {
            let args = Vec::with_capacity( to_do.len() ) ;
            to_do.reverse() ;
            stack.push( (typ, op, to_do, args) ) ;
            continue 'go_down
          },
          // Going up...
          NormRes::Term(term) => if let Some(
            & mut ( _, _, _, ref mut args )
          ) = stack.last_mut() {
            args.push( term ) ;
            continue 'go_down
          } else {
            return term
          },
        },
      }

    }

  }

  unreachable!()
}



/// Normalization result.
enum NormRes {
  /// Just a term.
  Term(Term),
  /// More stuff to do.
  App(Typ, Op, Vec<NormRes>),
}



/// Normalizes an operation application.
fn normalize_app(mut op: Op, mut args: Vec<Term>, typ: Typ) -> NormRes {
  use num::Zero ;

  // println!("{} ({})", op, typ) ;
  // for arg in & args {
  //   println!("  {}", arg)
  // }

  let (op, args) = match op {

    Op::Ite => if args.len() == 3 {
      if let Some(b) = args[0].bool() {
        return NormRes::Term(
          if b { args[1].clone() } else { args[2].clone() }
        )
      }
      if args[1] == args[2] {
        return NormRes::Term( args[1].clone() )
      }
      (op, args)
    } else {
      panic!(
        "trying to apply `Ite` operator to {} (!= 3) arguments", args.len()
      )
    },

    Op::Impl => match (args.pop(), args.pop()) {
      (Some(rgt), Some(lft)) => {
        debug_assert! { args.pop().is_none() }
        return NormRes::App(
          Typ::Bool, Op::Or, vec![
            NormRes::App(Typ::Bool, Op::Not, vec![ NormRes::Term(lft) ]),
            NormRes::Term(rgt)
          ]
        )
      },
      _ => panic!("illegal application of `Impl` to less than 2 arguments")
    },

    Op::And => {
      let mut set = HConSet::<Term>::new() ;
      let mut cnt = 0 ;
      
      while cnt < args.len() {
        let is_new = set.insert( args[cnt].clone() ) ;

        if ! is_new {
          args.swap_remove(cnt) ;
          ()
        } else if let Some(b) = args[cnt].bool() {
          if b {
            args.swap_remove(cnt) ;
            ()
          } else {
            return NormRes::Term( fls() )
          }
        } else if let Some(conj) = args[cnt].conj_inspect().map(
          |conj| conj.clone()
        ) {
          for term in conj {
            args.push(term)
          }
          args.swap_remove(cnt) ;
        } else {
          cnt += 1
        }
      }

      if conf.term_simpl >= 4 {
        args = term::simplify::conj_vec_simpl(args)
      }

      if args.is_empty() {
        return NormRes::Term( term::tru() )
      } else if args.len() == 1 {
        return NormRes::Term( args.pop().unwrap() )
      } else {
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::Or => {
      let mut set = HConSet::<Term>::new() ;
      let mut cnt = 0 ;
      
      while cnt < args.len() {
        let is_new = set.insert( args[cnt].clone() ) ;

        if ! is_new {
          args.swap_remove(cnt) ;
          ()
        } else if let Some(b) = args[cnt].bool() {
          if ! b {
            args.swap_remove(cnt) ;
            ()
          } else {
            return NormRes::Term( tru() )
          }
        } else if let Some(disj) = args[cnt].disj_inspect().map(
          |disj| disj.clone()
        ) {
          for term in disj {
            args.push(term)
          }
          args.swap_remove(cnt) ;
        } else {
          cnt += 1
        }
      }

      if args.is_empty() {
        return NormRes::Term( term::fls() )
      } else if args.len() == 1 {
        return NormRes::Term( args.pop().unwrap() )
      } else {
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::Not => {
      assert!( args.len() == 1 ) ;
      if let Some(b) = args[0].bool() {
        return NormRes::Term( bool(! b) )
      }

      match * args[0] {
        RTerm::App { op: Op::Not, ref args, .. } => {
          return NormRes::Term( args[0].clone() )
        },

        RTerm::App { op: Op::And, ref args, .. } => {
          return NormRes::App(
            Typ::Bool, Op::Or, args.iter().map(
              |arg| NormRes::App(
                Typ::Bool, Op::Not, vec![ NormRes::Term( arg.clone() ) ]
              )
            ).collect()
          )
        },
        RTerm::App { op: Op::Or, ref args, .. } => {
          return NormRes::App(
            Typ::Bool, Op::And, args.iter().map(
              |arg| NormRes::App(
                Typ::Bool, Op::Not, vec![ NormRes::Term( arg.clone() ) ]
              )
            ).collect()
          )
        },

        RTerm::App { op: Op::Gt, ref args, .. } => return NormRes::App(
          Typ::Bool, Op::Ge, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).rev().collect()
          //^^^~~~~ IMPORTANT.
        ),
        RTerm::App { op: Op::Ge, ref args, .. } => return NormRes::App(
          Typ::Bool, Op::Gt, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).rev().collect()
          //^^^~~~~ IMPORTANT.
        ),
        RTerm::App { op: Op::Lt, ref args, .. } => return NormRes::App(
          Typ::Bool, Op::Ge, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).collect()
        ),
        RTerm::App { op: Op::Le, ref args, .. } => return NormRes::App(
          Typ::Bool, Op::Gt, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).rev().collect()
          //^^^~~~~ IMPORTANT.
        ),
        _ => (),
      }

      (op, args)
    },

    Op::Eql => {
      // println!("(= {} {})", args[0], args[1]) ;
      if args.len() == 2 {
        if args[0] == args[1] {
          return NormRes::Term( tru() )
        } else

        if let Some(b) = args[0].bool() {
          return NormRes::Term(
            if b {
              args[1].clone()
            } else {
              not( args[1].clone() )
            }
          )
        } else

        if let Some(b) = args[1].bool() {
          return NormRes::Term(
            if b {
              args[0].clone()
            } else {
              not( args[0].clone() )
            }
          )
        } else

        if let (Some(r_1), Some(r_2)) = (
          args[0].real(), args[1].real()
        ) {
          return NormRes::Term( term::bool( r_1 == r_2 ) )
        } else

        if let (Some(i_1), Some(i_2)) = (
          args[0].int(), args[1].int()
        ) {
          return NormRes::Term( term::bool( i_1 == i_2 ) )
        } else

        // if let Some((var, term)) = args[0].invert( args[1].clone() ) {
        //   args = vec![ term::var(var, term.typ()), term ]
        // } else

        // if let Some((var, term)) = args[1].invert( args[0].clone() ) {
        //   args = vec![ term::var(var, term.typ()), term ]
        // } else

        if args[0].typ().is_arith() {
          // println!("  (= {} {})", args[0], args[1]) ;
          if ! args[1].is_zero() {
            let (rhs, lhs) = (args.pop().unwrap(), args.pop().unwrap()) ;
            let typ = rhs.typ() ;
            let lhs = if lhs.is_zero() { NormRes::Term(rhs) } else {
              NormRes::App(
                typ, Op::Sub, vec![
                  NormRes::Term(lhs), NormRes::Term(rhs)
                ]
              )
            } ;
            return NormRes::App(
              Typ::Bool, Op::Eql, vec![
                lhs, NormRes::Term( typ.default_val().to_term().unwrap() )
              ]
            )
          } else {
            // Rhs is zero, now normalize lhs. This is a bit ugly...
            let mut u_minus_lhs = term::u_minus(args[0].clone()) ;
            if u_minus_lhs.uid() < args[0].uid() {
              ::std::mem::swap(& mut args[0], & mut u_minus_lhs)
            }
            (op, args)
          }
        } else {
          args.sort_unstable() ;
          (op, args)
        }
      } else {
        args.sort_unstable() ;
        let len = args.len() ;
        let mut args = args.into_iter() ;
        let mut conj = vec![] ;
        if let Some(first) = args.next() {
          for arg in args {
            conj.push(
              NormRes::App(
                Typ::Bool, Op::Eql, vec![
                  NormRes::Term( first.clone() ),
                  NormRes::Term(arg)
                ]
              )
            )
          }
          if ! conj.is_empty() {
            return NormRes::App(Typ::Bool, Op::And, conj)
          }
        }
        panic!(
          "illegal application of {} to {} (< 2) argument", op, len
        )
      }
    },

    Op::Sub => {

      let mut args = args.into_iter() ;
      if let Some(first) = args.next() {
        let minus_one = if first.typ() == Typ::Int {
          int(- Int::one())
        } else {
          real(- Rat::one())
        } ;

        if args.len() == 0 {
          if let Some(i) = first.int_val() {
            return NormRes::Term( int(- i) )
          } else if let Some(r) = first.real_val() {
            return NormRes::Term( real( -r ) )
          }

          return NormRes::App(
            typ, Op::CMul, vec![
              NormRes::Term(minus_one),
              NormRes::Term(first),
            ]
          )
        } else {
          let mut to_do = Vec::with_capacity( args.len() + 1 ) ;
          to_do.push( NormRes::Term(first) ) ;
          for arg in args {
            to_do.push(
              NormRes::App(
                typ, Op::CMul, vec![
                  NormRes::Term( minus_one.clone() ),
                  NormRes::Term(arg),
                ]
              )
            )
          }

          return NormRes::App(typ, Op::Add, to_do)
        }

      } else {
        panic!("illegal nullary application of `Sub`")
      }
    },

    Op::Add => if args.is_empty() {
      panic!("trying to construct an empty sum")
    } else {

      let mut sum: Val = if args[0].typ() == Typ::Int {
        0.into()
      } else {
        (0,1).into()
      } ;

      let mut c_args = HConMap::<Term, Val>::new() ;
      let mut changed = false ;

      while let Some(arg) = args.pop() {
        if let Some(kids) = arg.add_inspect().map(|kids| kids.clone()) {
          args.extend(kids)
        } else if let Some(v) = arg.val() {
          sum = sum.add(v).expect(
            "during add simplification"
          )
        } else {
          let (val, term) = if let Some((val, term)) = arg.cmul_inspect() {
            (val, term)
          } else {
            (1.into(), & arg)
          } ;

          if let Some(value) = c_args.get_mut(term) {
            * value = value.clone().add(val).expect(
              "during add simplification"
            ) ;
            changed = true ;
            continue
          }

          c_args.insert(term.clone(), val) ;
        }
      }

      if changed {
        let mut args = vec![
          NormRes::Term( sum.to_term().unwrap() )
        ] ;
        for (term, coef) in c_args {
          if coef.is_zero() {
            continue
          } else if coef.is_one() {
            args.push( NormRes::Term(term) )
          } else {
            args.push(
              NormRes::App(
                typ, Op::CMul, vec![
                  NormRes::Term( coef.to_term().unwrap() ),
                  NormRes::Term(term)
                ]
              )
            )
          }
        }

        return NormRes::App(typ, Op::Add, args)
      }

      let mut args = Vec::with_capacity( c_args.len() ) ;
      for (term, coef) in c_args {
        if coef.is_zero() {
          continue
        } else if coef.is_one() {
          args.push(term)
        } else {
          let coef = coef.to_term().unwrap() ;
          args.push(
            factory.mk(
              RTerm::App {
                typ,
                op: Op::CMul,
                args: vec![ coef, term ]
              }
            )
          )
        }
      }

      if args.len() == 0 {
        return NormRes::Term(
          sum.to_term().expect(
            "coefficient cannot be unknown"
          )
        )
      } else if sum.is_zero() {
        if args.len() == 1 {
          return NormRes::Term( args.pop().unwrap() )
        } else {
          args.sort_unstable() ;
          (op, args)
        }
      } else {
        let sum = sum.to_term().expect(
          "coefficient cannot be unknown"
        ) ;
        args.push(sum) ;
        args.sort_unstable() ;
        (op, args)
      }

    },

    Op::CMul => {
      let (cst, term) = if let Some(term) = args.pop() {
        if let Some(cst) = args.pop() {
          (cst, term)
        } else {
          panic!("trying to construct a c_mul with 1 != 2 arguments")
        }
      } else {
        panic!("trying to construct a c_mul with 0 != 2 arguments")
      } ;
      if args.pop().is_some() {
        panic!("trying to construct a c_mul with more than 2 arguments")
      }
      debug_assert! { cst.val().is_some() }

      if let Some(val) = term.val() {
        let cst_val = cst.val().expect(
          & format!("illegal c_mul application: {} {}", cst, term)
        ) ;
        let res = cst_val.mul(val).expect(
          & format!("illegal c_mul application: {} {}", cst, term)
        ).to_term().expect(
          "cannot be unknown"
        ) ;
        return NormRes::Term(res)
      }

      if cst.is_one() {
        return NormRes::Term(term)
      } else if cst.is_zero() {
        return NormRes::Term(cst)
      }

      if let Some((op, args)) = term.app_inspect() {
        match op {
          Op::Add | Op::Mul | Op::Sub => return NormRes::App(
            typ, op, args.iter().map(
              |arg| {
                NormRes::App(
                  typ, Op::CMul, vec![
                    NormRes::Term( cst.clone() ),
                    NormRes::Term( arg.clone() )
                  ]
                )
              }
            ).collect()
          ),

          Op::CMul => if args.len() != 2 {
            panic!("illegal c_mul application to {} != 2 terms", args.len())
          } else {
            let cst_2 = args[0].clone() ;
            let term = args[1].clone() ;
            return NormRes::App(
              typ, op, vec![
                NormRes::App(
                  typ, Op::Mul, vec![
                    NormRes::Term(cst),
                    NormRes::Term(cst_2),
                  ]
                ),
                NormRes::Term(term)
              ]
            )
          },

          Op::Ite => if args.len() != 3 {
            panic!("illegal ite application: {}", term)
          } else {
            let (c, t, e) = (
              args[0].clone(),
              args[1].clone(),
              args[2].clone(),
            ) ;
            return NormRes::App(
              typ, op, vec![
                NormRes::Term(c),
                NormRes::App(
                  typ, Op::CMul, vec![
                    NormRes::Term(cst.clone()),
                    NormRes::Term(t),
                  ]
                ),
                NormRes::App(
                  typ, Op::CMul, vec![
                    NormRes::Term(cst),
                    NormRes::Term(e),
                  ]
                )
              ]
            )
          },

          Op::IDiv | Op::Div | Op::Rem | Op::Mod |
          Op::ToInt | Op::ToReal => (),

          Op::Gt | Op::Ge | Op::Le | Op::Lt | Op::Eql |
          Op::Impl | Op::Not | Op::And | Op::Or => panic!(
            "illegal c_mul application {}", term
          ),
        }
      }

      (op, vec![ cst, term ])

    },

    Op::Mul => if args.is_empty() {
      panic!("trying to construct an empty multiplication")
    } else {

      let mut cnt = 0 ;
      let mut coef: Val = if args[0].typ() == Typ::Int {
        1.into()
      } else {
        (1,1).into()
      } ;

      while cnt < args.len() {
        if let Some(kids) = args[cnt].mul_inspect().map(|kids| kids.clone()) {
          args.swap_remove(cnt) ;
          args.extend(kids)
        } else if let Some(i) = args[cnt].int_val().map( |v| v.clone() ) {
          args.swap_remove(cnt) ;
          coef = coef.mul( i.into() ).expect(
            "during multiplication simplification"
          )
        } else if let Some(r) = args[cnt].real_val().map( |v| v.clone() ) {
          args.swap_remove(cnt) ;
          coef = coef.mul( r.into() ).expect(
            "during multiplication simplification"
          )
        } else {
          cnt += 1
        }
      }

      if args.len() == 0 {
        return NormRes::Term(
          coef.to_term().expect(
            "coefficient cannot be unknown"
          )
        )
      } else if coef.is_one() {
        if args.len() == 1 {
          return NormRes::Term( args.pop().expect("mul1") )
        } else {
          args.sort_unstable() ;
          (op, args)
        }
      } else {
        let coef = coef.to_term().expect(
          "coefficient cannot be unknown"
        ) ;
        if args.len() == 1 {
          return NormRes::App(
            typ, Op::CMul, vec![
              NormRes::Term(coef),
              NormRes::Term( args.pop().expect("mul2") )
            ]
          )
        } else {
          return NormRes::App(
            typ, Op::Mul, args.into_iter().map(
              |arg| NormRes::App(
                typ, Op::CMul, vec![
                  NormRes::Term( coef.clone() ),
                  NormRes::Term( arg )
                ]
              )
            ).collect()
          )
        }
      }

    },

    Op::IDiv => if args.len() == 2 {
      macro_rules! num_den {
        () => (
          if let ( Some(den), Some(num) ) = (
            args.pop(), args.pop()
          ) {
            (num, den)
          } else {
            panic!("logic error, pop failed after length check")
          }
        )
      }

      match ( args[0].as_val(), args[1].as_val() ) {
        ( Val::I(num), Val::I(den) ) => match Op::IDiv.eval(
          vec![ Val::I( num ), Val::I( den ) ]
        ) {
          Ok( Val::I(i) ) => return NormRes::Term( int(i) ),
          Ok(_) => panic!(
            "unexpected result while evaluating `({} {} {})`",
            op, args[0], args[1]
          ),
          Err(e) => panic!(
            "error while evaluating `({} {} {})`: {}",
            op, args[0], args[1], e.description()
          ),
        },

        ( Val::I(num), Val::N ) => if num.is_zero() {
          return NormRes::Term( int(0) )
        },

        ( Val::N, Val::I(den) ) => if den.abs() == Int::one() {
          let (num, _) = num_den!() ;
          if den.is_negative() {
            return NormRes::App( typ, Op::Sub, vec![ NormRes::Term(num) ] )
          } else {
            return NormRes::Term(num)
          }
        },

        ( Val::N, Val::N ) => (),

        // Anything else is type error.
        ( _, _ ) => panic!(
          "illegal application or `{}` to {} ({}) and {} ({})",
          op, args[0], args[0].typ(), args[1], args[1].typ()
        ),
      }

      (op, args)
    } else {
      panic!(
        "illegal application of `{}` to {} (!= 2) arguments", op, args.len()
      )
    },

    Op::Div => if args.len() != 2 {
      panic!(
        "illegal application of `{}` to {} (!= 2) arguments",
        op, args.len()
      )
    } else if let Some(den) = args[1].int() {
      if den.is_zero() {
        panic!("illegal division by zero")
      }

      let one = Int::one() ;

      if & den == & one {
        if let ( _, Some(num) ) = ( args.pop(), args.pop() ) {
          debug_assert! { args.pop().is_none() }
          return NormRes::Term(num)
        } else {
          panic!("logic error, pop failed after length check")
        }
      }

      if den == - & one {
        if let ( _, Some(num) ) = ( args.pop(), args.pop() ) {
          debug_assert! { args.pop().is_none() }
          return NormRes::App(
            Typ::Bool, Op::Mul, vec![
              NormRes::Term( term::int(-1) ),
              NormRes::Term(num),
            ]
          )
        } else {
          panic!("logic error, pop failed after length check")
        }
      }

      if let Some(num) = args[0].int() {
        if ( & num % & den ).is_zero() {
          return NormRes::Term(
            term::int( num / den )
          )
        }
      }

      (op, args)
    } else {
      (op, args)
    },

    Op::Ge | Op::Gt => if args.len() == 2 {

      if args[0] == args[1] {
        return NormRes::Term( bool( op == Op::Ge ) )
      } else

      // We want the rhs to be a constant.
      if let Some(rhs_val) = args[1].val() {
        // If lhs is also a constant, we done.
        if let Some(lhs_val) = args[0].val() {
          let res = if op == Op::Ge {
            lhs_val.ge(rhs_val)
          } else {
            lhs_val.gt(rhs_val)
          } ;
          return NormRes::Term(
            bool( res.unwrap().to_bool().unwrap().unwrap() )
          )
        }

        let (mut rhs, lhs) = ( args.pop().unwrap(), args.pop().unwrap() ) ;

        // Is lhs a sum with a constant in it?.
        let mut correction = None ;

        if let Some(kids) = lhs.add_inspect() {
          for kid in kids {
            if let Some(cst) = kid.val() { correction = Some(cst) }
          }
        }
        if let Some(correction) = correction {
          return NormRes::App(
            Typ::Bool, op, vec![
              NormRes::App(
                lhs.typ(), Op::Sub, vec![
                  NormRes::Term( lhs ),
                  NormRes::Term( correction.clone().to_term().unwrap() )
                ]
              ),
              NormRes::Term(
                rhs_val.sub(correction).unwrap().to_term().unwrap()
              )
            ]
          )
        } else {
          // Normalize gt to ge for integers.
          if op == Op::Gt {
            match rhs_val {
              Val::I(ref i) => {
                rhs = term::int(i + 1) ;
                op = Op::Ge
              },
              _ => (),
            }
          }

          // No correction, let's dodis.
          args.push(lhs) ;
          args.push(rhs)
        }

      } else {
        // Rhs is not a constant.
        let (rhs, lhs) = ( args.pop().unwrap(), args.pop().unwrap() ) ;
        let typ = rhs.typ() ;
        debug_assert_eq! { lhs.typ(), typ }
        return NormRes::App(
          Typ::Bool, op, vec![
            NormRes::App(
              typ, Op::Sub, vec![
                NormRes::Term( lhs ),
                NormRes::Term( rhs )
              ]
            ),
            NormRes::Term(
              if typ == Typ::Int {
                int_zero()
              } else {
                real_zero()
              }
            )
          ]
        )
      }

      (op, args)
    } else {
      panic!(
        "illegal `{}` application to {} != 2 argument(s)", op, args.len()
      )
    },

    Op::Le => {
      args.reverse() ;
      return NormRes::App(
        Typ::Bool, Op::Ge, args.into_iter().map(
          |arg| NormRes::Term(arg)
        ).collect()
      )
    },

    Op::Lt => {
      args.reverse() ;
      return NormRes::App(
        Typ::Bool, Op::Gt, args.into_iter().map(
          |arg| NormRes::Term(arg)
        ).collect()
      )
    },

    Op::Mod => if args.len() == 2 {
      if let Some(i) = args[1].int() {
        if i == 1.into() {
          return NormRes::Term( term::int(0) )
        } else {
          (op, args)
        }
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::ToInt => {
      if args.len() == 1 {
        if let Some(r) = args[0].real() {
          let mut i = r.to_integer() ;
          return NormRes::Term( term::int(i) )
        }
      }
      (op, args)
    },
    Op::ToReal => {
      if args.len() == 1 {
        if let Some(i) = args[0].int() {
          return NormRes::Term(
            term::real( Rat::new(i, 1.into()) )
          )
        }
      }
      (op, args)
    },

    Op::Rem => (op, args),

  } ;

  NormRes::Term( factory.mk( RTerm::App { typ, op, args } ) )
}

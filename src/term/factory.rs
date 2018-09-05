//! Term creation functions.

use hashconsing::HashConsign;

use common::*;
use term::{Op, RTerm, Term};

new_consign! {
  /// Term factory.
  let factory = consign(conf.instance.term_capa) for RTerm ;
}

lazy_static! {
  /// Cache for terms' variables.
  static ref var_cache: RwLock< TermMap<VarSet> > = RwLock::new(
    TermMap::with_capacity( conf.instance.term_capa )
  ) ;
}

/// Scans a term to extract the variables that appear in it.
fn scan_vars(t: &Term) -> VarSet {
    let mut to_do = vec![t];
    let mut set = VarSet::with_capacity(11);

    while let Some(term) = to_do.pop() {
        match term.get() {
            RTerm::Var(_, i) => {
                let _ = set.insert(*i);
                ()
            }
            RTerm::Cst(_) => (),

            RTerm::App { args, .. } | RTerm::Fun { args, .. } | RTerm::DTypNew { args, .. } => {
                for arg in args {
                    to_do.push(arg)
                }
            }

            RTerm::CArray { term, .. }
            | RTerm::DTypSlc { term, .. }
            | RTerm::DTypTst { term, .. } => to_do.push(term),
        }
    }
    set.shrink_to_fit();
    set
}

/// Variables appearing in a term (cached).
#[inline]
pub fn vars(t: &Term) -> VarSet {
    if let Some(vars) = var_cache
        .read()
        .expect("variable cache is corrupted...")
        .get(t)
    {
        return vars.clone();
    }
    var_cache
        .write()
        .expect("variable cache is corrupted...")
        .entry(t.clone())
        .or_insert_with(|| scan_vars(t))
        .clone()
}

/// Map over the variables appearing in a term (cached).
#[inline]
pub fn map_vars<F>(t: &Term, mut f: F)
where
    F: FnMut(VarIdx),
{
    if let Some(vars) = var_cache
        .read()
        .expect("variable cache is corrupted...")
        .get(t)
    {
        for var in vars {
            f(*var)
        }
        return ();
    }

    let vars = scan_vars(t);
    for var in &vars {
        f(*var)
    }
    var_cache
        .write()
        .expect("variable cache is corrupted...")
        .entry(t.clone())
        .or_insert_with(|| vars);
    ()
}

/// Creates a term.
#[inline]
pub fn term(t: RTerm) -> Term {
    factory.mk(t)
}

/// Creates a variable.
#[inline]
pub fn var<V: Into<VarIdx>>(v: V, typ: Typ) -> Term {
    factory.mk(RTerm::Var(typ, v.into()))
}

/// Creates an integer variable.
#[inline]
pub fn int_var<V: Into<VarIdx>>(v: V) -> Term {
    factory.mk(RTerm::Var(typ::int(), v.into()))
}

/// Creates a real variable.
#[inline]
pub fn real_var<V: Into<VarIdx>>(v: V) -> Term {
    factory.mk(RTerm::Var(typ::real(), v.into()))
}

/// Creates a boolean variable.
#[inline]
pub fn bool_var<V: Into<VarIdx>>(v: V) -> Term {
    factory.mk(RTerm::Var(typ::bool(), v.into()))
}

/// Creates a constant.
#[inline]
pub fn cst<V: Into<Val>>(val: V) -> Term {
    let val = val.into();
    if !val.is_known() {
        panic!(
            "trying to construct a constant term from a non-value {}",
            val
        )
    }
    factory.mk(RTerm::Cst(val))
}

/// Creates an integer constant.
#[inline]
pub fn int<I: Into<Int>>(i: I) -> Term {
    let i = i.into();
    factory.mk(RTerm::Cst(val::int(i)))
}
/// Creates a real constant.
#[inline]
pub fn real<R: Into<Rat>>(r: R) -> Term {
    let r = r.into();
    factory.mk(RTerm::Cst(val::real(r)))
}
/// Creates a real constant from a float.
#[inline]
pub fn real_of_float(f: f64) -> Term {
    real(rat_of_float(f))
}
/// Creates the constant `0`.
#[inline]
pub fn int_zero() -> Term {
    int(Int::zero())
}
/// Creates the constant `1`.
#[inline]
pub fn int_one() -> Term {
    int(Int::one())
}
/// Creates the constant `0`.
#[inline]
pub fn real_zero() -> Term {
    real(Rat::zero())
}
/// Creates the constant `1`.
#[inline]
pub fn real_one() -> Term {
    real(Rat::one())
}

/// Creates a boolean.
#[inline]
pub fn bool(b: bool) -> Term {
    factory.mk(RTerm::Cst(val::bool(b)))
}
/// Creates the constant `true`.
#[inline]
pub fn tru() -> Term {
    bool(true)
}
/// Creates the constant `false`.
#[inline]
pub fn fls() -> Term {
    bool(false)
}

/// If-then-else.
#[inline]
pub fn ite(c: Term, t: Term, e: Term) -> Term {
    app(Op::Ite, vec![c, t, e])
}

/// Implication.
#[inline]
pub fn implies(lhs: Term, rhs: Term) -> Term {
    app(Op::Impl, vec![lhs, rhs])
}

/// Negates a term.
#[inline]
pub fn not(term: Term) -> Term {
    app(Op::Not, vec![term])
}
/// Disjunction.
#[inline]
pub fn or(terms: Vec<Term>) -> Term {
    app(Op::Or, terms)
}
/// Conjunction.
#[inline]
pub fn and(terms: Vec<Term>) -> Term {
    app(Op::And, terms)
}

/// Constant array.
///
/// The type is the type of **the indices** of the array.
#[inline]
pub fn cst_array(typ: Typ, default: Term) -> Term {
    if let Some(val) = default.val() {
        factory.mk(RTerm::Cst(val::array(typ, val)))
    } else {
        factory.mk(RTerm::CArray { typ, term: default })
    }
}

/// Store operation in an array.
#[inline]
pub fn store(array: Term, idx: Term, val: Term) -> Term {
    app(Op::Store, vec![array, idx, val])
}
/// Select operation for an array.
#[inline]
pub fn select(array: Term, idx: Term) -> Term {
    app(Op::Select, vec![array, idx])
}

/// Function application.
///
/// # Panics
///
/// - if the function does not exist
/// - if the type does not make sense
/// - if the arguments are illegal
#[inline]
pub fn fun(typ: Typ, name: String, mut args: Vec<Term>) -> Term {
    if let Err(e) = fun::dec_do(&name, |fun| {
        debug_assert_eq! { typ, fun.typ }
        if args.len() != fun.sig.len() {
            panic!("illegal application of function {}", conf.bad(&name))
        }
        for (info, arg) in fun.sig.iter().zip(args.iter_mut()) {
            if let Some(nu_arg) = arg.force_dtyp(info.typ.clone()) {
                *arg = nu_arg
            }
        }
        Ok(())
    }) {
        print_err(&e);
        panic!("illegal function application")
    }

    factory.mk(RTerm::Fun { typ, name, args })
}

/// Creates an operator application.
///
/// Assumes the application is well-typed, modulo int to real casting.
///
/// Runs [`normalize`](fn.normalize.html) and returns its result.
#[inline]
pub fn app(op: Op, mut args: Vec<Term>) -> Term {
    let typ = expect!(
    op.type_check(& mut args) => |e|
      let res: Res<()> = Err(
        "Fatal internal type checking error, \
        please notify the developer(s)".into()
      ) ;
      match e {
        term::TypError::Typ {
          expected, obtained, index
        } => res.chain_err(
          || format!(
            "expected an expression of sort {}, found {} ({})",
            expected.map(|t| format!("{}", t)).unwrap_or_else(|| "?".into()),
            args[index], obtained
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
        term::TypError::Msg(blah) => res.chain_err(|| blah)
      }.unwrap_err()
  );

    normalize(op, args, typ.clone())
}

/// Creates a constant term.
pub fn val(val: Val) -> Term {
    factory.mk(RTerm::Cst(val))
}

/// Creates a datatype constructor.
pub fn dtyp_new(typ: Typ, name: String, args: Vec<Term>) -> Term {
    let rterm = term::simplify::dtyp_new(typ, name, args);
    factory.mk(rterm)
}

/// Creates a new datatype selector.
///
/// # TODO
///
/// - treat constants better
pub fn dtyp_slc(typ: Typ, name: String, term: Term) -> Term {
    match term::simplify::dtyp_slc(typ, name, term) {
        Either::Left(rterm) => factory.mk(rterm),
        Either::Right(term) => term,
    }
}

/// Creates a new datatype tester.
///
/// # TODO
///
/// - treat constants better
pub fn dtyp_tst(name: String, term: Term) -> Term {
    let (rterm, positive) = term::simplify::dtyp_tst(name, term);
    let res = factory.mk(rterm);
    if !positive {
        not(res)
    } else {
        res
    }
}

/// Creates an operator application.
///
/// Error if the application is ill-typed (int will be cast to real
/// automatically).
///
/// Runs [`normalize`](fn.normalize.html) and returns its result.
#[inline]
pub fn try_app(op: Op, mut args: Vec<Term>) -> Result<Term, term::TypError> {
    let typ = op.type_check(&mut args)?;
    Ok(normalize(op, args, typ))
}

/// Creates a less than or equal to.
#[inline]
pub fn le(lhs: Term, rhs: Term) -> Term {
    app(Op::Le, vec![lhs, rhs])
}
/// Creates a less than.
#[inline]
pub fn lt(lhs: Term, rhs: Term) -> Term {
    app(Op::Lt, vec![lhs, rhs])
}
/// Creates a greater than.
#[inline]
pub fn gt(lhs: Term, rhs: Term) -> Term {
    app(Op::Gt, vec![lhs, rhs])
}
/// Creates a greater than or equal to.
#[inline]
pub fn ge(lhs: Term, rhs: Term) -> Term {
    app(Op::Ge, vec![lhs, rhs])
}

/// Creates an equality.
#[inline]
pub fn eq(lhs: Term, rhs: Term) -> Term {
    app(Op::Eql, vec![lhs, rhs])
}

/// Creates a distinct application.
#[inline]
pub fn distinct(terms: Vec<Term>) -> Term {
    app(Op::Distinct, terms)
}

/// Creates a sum.
#[inline]
pub fn add(kids: Vec<Term>) -> Term {
    app(Op::Add, kids)
}
/// Creates a sum, binary version.
#[inline]
pub fn add2(kid_1: Term, kid_2: Term) -> Term {
    app(Op::Add, vec![kid_1, kid_2])
}

/// Creates a subtraction.
#[inline]
pub fn sub(kids: Vec<Term>) -> Term {
    app(Op::Sub, kids)
}
/// Creates a subtraction, binary version.
#[inline]
pub fn sub2(kid_1: Term, kid_2: Term) -> Term {
    app(Op::Sub, vec![kid_1, kid_2])
}

/// Creates a unary minus.
#[inline]
pub fn u_minus(kid: Term) -> Term {
    app(Op::Sub, vec![kid])
}
/// Creates a multiplication.
#[inline]
pub fn mul(kids: Vec<Term>) -> Term {
    app(Op::Mul, kids)
}
/// Creates a multiplication by a constant.
#[inline]
pub fn cmul<V>(cst: V, term: Term) -> Term
where
    V: Into<val::RVal>,
{
    app(
        Op::CMul,
        vec![
            cst.into()
                .to_term()
                .expect("illegal constant passed to CMul constructor"),
            term,
        ],
    )
}

/// Creates an integer division.
#[inline]
pub fn idiv(kids: Vec<Term>) -> Term {
    app(Op::IDiv, kids)
}
/// Creates a division.
#[inline]
pub fn div(kids: Vec<Term>) -> Term {
    app(Op::Div, kids)
}
/// Creates a modulo application.
#[inline]
pub fn modulo(a: Term, b: Term) -> Term {
    app(Op::Mod, vec![a, b])
}

/// Creates a conversion from `Int` to `Real`.
#[inline]
pub fn to_real(int: Term) -> Term {
    app(Op::ToReal, vec![int])
}
/// Creates a conversion from `Real` to `Int`.
#[inline]
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
fn normalize(op: Op, args: Vec<Term>, typ: Typ) -> Term {
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
    let mut stack = vec![(typ, op, vec![], args)];

    'go_down: while let Some((typ, op, mut to_do, mut args)) = stack.pop() {
        'do_stuff: loop {
            match to_do.pop() {
                Some(NormRes::Term(term)) => {
                    args.push(term);
                    continue 'do_stuff;
                }

                Some(NormRes::App(nu_typ, nu_op, mut nu_to_do)) => {
                    stack.push((typ, op, to_do, args));
                    let nu_args = Vec::with_capacity(nu_to_do.len());
                    nu_to_do.reverse();
                    stack.push((nu_typ, nu_op, nu_to_do, nu_args));
                    continue 'go_down;
                }

                None => match normalize_app(op, args, typ) {
                    // Going down...
                    NormRes::App(typ, op, mut to_do) => {
                        let args = Vec::with_capacity(to_do.len());
                        to_do.reverse();
                        stack.push((typ, op, to_do, args));
                        continue 'go_down;
                    }
                    // Going up...
                    NormRes::Term(term) => {
                        if let Some(&mut (_, _, _, ref mut args)) = stack.last_mut() {
                            args.push(term);
                            continue 'go_down;
                        } else {
                            return term;
                        }
                    }
                },
            }
        }
    }

    unreachable!()
}

/// Normalization result.
pub enum NormRes {
    /// Just a term.
    Term(Term),
    /// More stuff to do.
    App(Typ, Op, Vec<NormRes>),
}

/// Normalizes an operation application.
fn normalize_app(mut op: Op, mut args: Vec<Term>, typ: Typ) -> NormRes {
    use term::simplify;

    // println!() ;
    // print!("({}", op) ;
    // for arg in & args {
    //   print!(" {}", arg)
    // }
    // println!(")") ;

    let maybe_res = match op {
        // Polymorphic operators.
        Op::Eql => simplify::eql(&mut args),
        Op::Ite => simplify::ite(&mut args),
        Op::Distinct => simplify::distinct(&mut args),

        // Boolean operators.
        Op::And => simplify::and(&mut args),
        Op::Or => simplify::or(&mut args),
        Op::Not => simplify::not(&mut args),
        Op::Impl => simplify::implies(&mut args),

        // Relations over arithmetics.
        Op::Ge | Op::Gt => simplify::gt_ge(&mut op, &mut args),
        Op::Le | Op::Lt => simplify::lt_le(&mut op, &mut args),

        // Operations over arithmetics.
        Op::Div => simplify::div(&mut args),
        Op::Mod => simplify::modulo(&mut args),
        Op::Rem => simplify::rem(&mut args),
        Op::Sub => simplify::sub(&mut args),
        Op::Add => simplify::add(&mut args),
        Op::IDiv => simplify::idiv(&mut args),
        Op::CMul => simplify::cmul(&mut args),
        Op::Mul => simplify::mul(&mut args),

        // Casting operations.
        Op::ToInt => simplify::to_int(&mut args),
        Op::ToReal => simplify::to_real(&mut args),

        // Array operations.
        Op::Store => simplify::store(&mut args),
        Op::Select => simplify::select(&mut args),
    };

    // print!("... ") ;

    if let Some(result) = maybe_res {
        // println!("simplified") ;
        result
    } else {
        // print!("({}", op) ;
        // for arg in & args {
        //   print!(" {}", arg)
        // }
        // println!(")") ;
        NormRes::Term(factory.mk(RTerm::App { typ, op, args }))
    }
}

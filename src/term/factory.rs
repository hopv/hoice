//! Term creation functions.

use hashconsing::HashConsign;

use crate::{
    common::*,
    term::{Op, RTerm, Term},
};

hashconsing::consign! {
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
///
/// This function is not directly defined for `RTerm`s because it only makes sense on hashconsed
/// `Term`s.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let term = term::ge(
///     term::add(vec![
///         term::int_var(7),
///         term::cmul(7, term::int_var(3)),
///         term::mul( vec![term::int_var(2), term::int_var(5)] )
///     ]), term::int(0)
/// );
/// let expected: VarSet = vec![
///     7.into(), 3.into(), 2.into(), 5.into()
/// ].into_iter().collect();
/// assert_eq! { term::vars(&term), expected }
/// ```
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

/// Iterator over the variables appearing in a term (cached).
///
/// Each variable is visited only once.
///
/// Pretty much equivalent to `term::vars(t).into_iter().map(f)`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let term = term::ge(
///     term::add(vec![
///         term::int_var(7),
///         term::cmul(7, term::int_var(3)),
///         term::mul( vec![term::int_var(2), term::int_var(7), term::int_var(5)] )
///     ]), term::int(0)
/// );
/// let mut expected: VarSet = vec![
///     7.into(), 3.into(), 2.into(), 5.into()
/// ].into_iter().collect();
/// term::map_vars(
///     &term, |var| {
///         let was_there = expected.remove(&var);
///         assert! { was_there }
///     }
/// );
/// assert! { expected.is_empty() }
/// ```
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

/// Creates a term from a non-hconsed `RTerm`.
///
/// This function is not really meant to be used outside of the term module, although it cannot do
/// anything bad.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let kid_1 = term::add(vec![term::int_var(0), term::cmul(7, term::int_var(1))]);
/// let kid_2 = term::int(42);
/// let t = term::ge( kid_1, kid_2 );
///
/// let rterm = t.get().clone();
/// let other = term::term(rterm);
///
/// assert_eq! { other, t }
/// assert_eq! { other.uid(), t.uid() }
/// assert_eq! { other.get(), t.get() }
/// ```
#[inline]
pub fn term(t: RTerm) -> Term {
    factory.mk(t)
}

/// Creates a variable.
///
/// See also [`int_var`], [`real_var`] and [`bool_var`].
///
/// [`int_var`]: fn.int_var.html (int_var term creation function)
/// [`real_var`]: fn.real_var.html (real_var term creation function)
/// [`bool_var`]: fn.bool_var.html (bool_var term creation function)
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::var(3, typ::bool());
/// assert_eq! { t.var_idx(), Some(3.into()) }
/// assert_eq! { t.typ(), typ::bool() }
/// assert_eq! { t.get(), & RTerm::Var(typ::bool(), 3.into()) }
/// ```
#[inline]
pub fn var<V: Into<VarIdx>>(v: V, typ: Typ) -> Term {
    factory.mk(RTerm::Var(typ, v.into()))
}

/// Creates an integer variable.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::int_var(3);
/// assert_eq! { t.var_idx(), Some(3.into()) }
/// assert_eq! { t.typ(), typ::int() }
/// assert_eq! { t.get(), & RTerm::Var(typ::int(), 3.into()) }
/// ```
#[inline]
pub fn int_var<V: Into<VarIdx>>(v: V) -> Term {
    var(v, typ::int())
}

/// Creates a real variable.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::real_var(3);
/// assert_eq! { t.var_idx(), Some(3.into()) }
/// assert_eq! { t.typ(), typ::real() }
/// assert_eq! { t.get(), & RTerm::Var(typ::real(), 3.into()) }
/// ```
#[inline]
pub fn real_var<V: Into<VarIdx>>(v: V) -> Term {
    var(v, typ::real())
}

/// Creates a boolean variable.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::bool_var(3);
/// assert_eq! { t.var_idx(), Some(3.into()) }
/// assert_eq! { t.typ(), typ::bool() }
/// assert_eq! { t.get(), & RTerm::Var(typ::bool(), 3.into()) }
/// ```
#[inline]
pub fn bool_var<V: Into<VarIdx>>(v: V) -> Term {
    var(v, typ::bool())
}

/// Creates a constant.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let val = val::int(42);
/// let t = term::cst(val.clone());
/// assert_eq! { t.val(), Some(val.clone()) }
/// assert_eq! { t.typ(), typ::int() }
/// assert_eq! { t.get(), & RTerm::Cst(val) }
/// ```
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
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let val = val::int(42);
/// let t = term::int(42);
/// assert_eq! { t.val(), Some(val.clone()) }
/// assert_eq! { t.typ(), typ::int() }
/// assert_eq! { t.get(), & RTerm::Cst(val) }
/// ```
#[inline]
pub fn int<I: Into<Int>>(i: I) -> Term {
    cst(val::int(i))
}
/// Creates a real constant.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let val = val::real_of(42.);
/// let t = term::real(Rat::new(42.into(), 1.into()));
/// assert_eq! { t.val(), Some(val.clone()) }
/// assert_eq! { t.typ(), typ::real() }
/// assert_eq! { t.get(), & RTerm::Cst(val) }
/// ```
#[inline]
pub fn real<R: Into<Rat>>(r: R) -> Term {
    cst(val::real(r))
}
/// Creates a real constant from a float.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let val = val::real_of(42.);
/// let t = term::real_of(42.);
/// assert_eq! { t.val(), Some(val.clone()) }
/// assert_eq! { t.typ(), typ::real() }
/// assert_eq! { t.get(), & RTerm::Cst(val) }
/// ```
#[inline]
pub fn real_of(f: f64) -> Term {
    real(rat_of_float(f))
}

/// Creates the integer constant `0`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::int_zero();
/// assert_eq! { t.get(), & RTerm::Cst(val::int(0)) }
/// ```
#[inline]
pub fn int_zero() -> Term {
    int(Int::zero())
}
/// Creates the integer constant `1`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::int_one();
/// assert_eq! { t.get(), & RTerm::Cst(val::int(1)) }
/// ```
#[inline]
pub fn int_one() -> Term {
    int(Int::one())
}

/// Creates the real constant `0`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::real_zero();
/// assert_eq! { t.get(), & RTerm::Cst(val::real_of(0.)) }
/// ```
#[inline]
pub fn real_zero() -> Term {
    real(Rat::zero())
}
/// Creates the real constant `1`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::real_one();
/// assert_eq! { t.get(), & RTerm::Cst(val::real_of(1.)) }
/// ```
#[inline]
pub fn real_one() -> Term {
    real(Rat::one())
}

/// Creates a boolean.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::bool(true);
/// assert_eq! { t.typ(), typ::bool() }
/// assert_eq! { t.get(), & RTerm::Cst(val::bool(true)) }
/// ```
#[inline]
pub fn bool(b: bool) -> Term {
    cst(val::bool(b))
}
/// Creates the constant `true`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::tru();
/// assert_eq! { t.get(), & RTerm::Cst(val::bool(true)) }
/// ```
#[inline]
pub fn tru() -> Term {
    bool(true)
}
/// Creates the constant `false`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::fls();
/// assert_eq! { t.get(), & RTerm::Cst(val::bool(false)) }
/// ```
#[inline]
pub fn fls() -> Term {
    bool(false)
}

/// If-then-else.
///
/// # Examples
///
/// General case:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::ite(
///     term::bool_var(0),
///     term::int_var(7),
///     term::int(17),
/// );
/// assert_eq! {
///     &format!("{}", t), "(ite v_0 v_7 17)"
/// }
/// ```
///
/// ## Simplifications
///
/// Guard is trivial:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::ite(
///     term::fls(),
///     term::int_var(7),
///     term::int(17),
/// );
/// assert_eq! { &format!("{}", t), "17" }
/// ```
///
/// Both branches are equal:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::ite(
///     term::fls(),
///     term::int_var(7),
///     term::int_var(7),
/// );
/// assert_eq! { &format!("{}", t), "v_7" }
/// ```
#[inline]
pub fn ite(c: Term, t: Term, e: Term) -> Term {
    app(Op::Ite, vec![c, t, e])
}

/// Implication.
///
/// Implications `A => B` are rewritten as `(not A) or B`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::implies(
///     term::bool_var(0),
///     term::or( vec![term::bool_var(7), term::bool_var(3)] )
/// );
/// assert_eq! { &format!("{}", t), "(or v_7 v_3 (not v_0))" }
/// ```
#[inline]
pub fn implies(lhs: Term, rhs: Term) -> Term {
    app(Op::Impl, vec![lhs, rhs])
}

/// Negates a term.
///
/// Negations are pushed down as much as possible.
///
/// # Examples
///
/// General case:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::not(term::bool_var(0));
/// assert_eq! { &format!("{}", t), "(not v_0)" }
/// ```
///
/// ## Simplifications
///
/// Double negations:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::not(term::not(term::bool_var(0)));
/// assert_eq! { &format!("{}", t), "v_0" }
/// ```
///
/// Negations are pushed down:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::not(
///     term::or(vec![ term::bool_var(0), term::not(term::bool_var(1)) ])
/// );
/// assert_eq! { &format!("{}", t), "(and v_1 (not v_0))" }
/// let t = term::not(
///     term::and(vec![ term::bool_var(0), term::not(term::bool_var(1)) ])
/// );
/// assert_eq! { &format!("{}", t), "(or v_1 (not v_0))" }
/// ```
#[inline]
pub fn not(term: Term) -> Term {
    app(Op::Not, vec![term])
}

/// Disjunction.
///
/// # Examples
///
/// General case:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::or(vec![ term::bool_var(0), term::bool_var(1) ]);
/// assert_eq! { &format!("{}", t), "(or v_0 v_1)" }
/// ```
///
/// ## Simplifications
///
/// Nullary applications:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::or(vec![]);
/// assert_eq! { &format!("{}", t), "false" }
/// ```
///
/// Unary applications:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::or(vec![term::bool_var(0)]);
/// assert_eq! { &format!("{}", t), "v_0" }
/// ```
///
/// Trivial disjunctions:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::or(vec![
///     term::bool_var(1), term::bool_var(0), term::not(term::bool_var(1))
/// ]);
/// assert_eq! { &format!("{}", t), "true" }
/// ```
///
/// Arithmetic simplification:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::or(vec![
///     term::ge(term::int_var(0), term::int(7)), term::le(term::int_var(0), term::int(7)),
/// ]);
/// assert_eq! { &format!("{}", t), "true" }
/// let t = term::or(vec![
///     term::ge(term::int_var(0), term::int(7)), term::gt(term::int_var(0), term::int(7)),
/// ]);
/// assert_eq! { &format!("{}", t), "(>= v_0 7)" }
/// ```
#[inline]
pub fn or(terms: Vec<Term>) -> Term {
    app(Op::Or, terms)
}

/// Conjunction.
///
/// # Examples
///
/// General case:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::and(vec![ term::bool_var(0), term::bool_var(1) ]);
/// assert_eq! { &format!("{}", t), "(and v_0 v_1)" }
/// ```
///
/// ## Simplifications
///
/// Nullary applications:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::and(vec![]);
/// assert_eq! { &format!("{}", t), "true" }
/// ```
///
/// Unary applications:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::and(vec![term::bool_var(0)]);
/// assert_eq! { &format!("{}", t), "v_0" }
/// ```
///
/// Trivial conjunctions:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::and(vec![
///     term::bool_var(1), term::bool_var(0), term::not(term::bool_var(1))
/// ]);
/// assert_eq! { &format!("{}", t), "false" }
/// ```
///
/// Arithmetic simplification:
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::and(vec![
///     term::ge(term::int_var(0), term::int(7)), term::le(term::int_var(0), term::int(7)),
/// ]);
/// assert_eq! { &format!("{}", t), "(= (+ v_0 (- 7)) 0)" }
/// let t = term::and(vec![
///     term::ge(term::int_var(0), term::int(7)), term::gt(term::int_var(0), term::int(7)),
/// ]);
/// assert_eq! { &format!("{}", t), "(>= v_0 8)" }
/// let t = term::and(vec![
///     term::ge(term::int_var(0), term::int(7)), term::lt(term::int_var(0), term::int(7)),
/// ]);
/// assert_eq! { &format!("{}", t), "false" }
/// ```
#[inline]
pub fn and(terms: Vec<Term>) -> Term {
    app(Op::And, terms)
}

/// Constant array.
///
/// A constant array is not necessarily a value. It is an array which maps all indices to the same
/// (non-necessarily constant) term.
///
/// The type is the type of **the indices** of the array.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let arr = term::cst_array(typ::int(), term::int_var(3));
/// assert! { arr.val().is_none() }
/// assert_eq! { &format!("{}", arr), "((as const (Array Int Int)) v_3)" }
/// ```
#[inline]
pub fn cst_array(typ: Typ, default: Term) -> Term {
    if let Some(val) = default.val() {
        factory.mk(RTerm::Cst(val::array(typ, val)))
    } else {
        factory.mk(RTerm::new_carray(typ, default))
    }
}

/// Store operation in arrays.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let arr = term::cst_array(typ::int(), term::int_var(3));
/// let arr = term::store(arr, term::int(7), term::int(0));
/// assert_eq! { &format!("{}", arr), "(store ((as const (Array Int Int)) v_3) 7 0)" }
/// ```
#[inline]
pub fn store(array: Term, idx: Term, val: Term) -> Term {
    app(Op::Store, vec![array, idx, val])
}

/// Select operation for arrays.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let arr = term::cst_array(typ::int(), term::int_var(2));
/// let arr = term::store(arr, term::int(7), term::int(0));
/// let select_2 = term::select(arr.clone(), term::int(2));
/// assert_eq! {
///     &format!("{}", select_2), "(select (store ((as const (Array Int Int)) v_2) 7 0) 2)"
/// }
/// let select_7 = term::select(arr.clone(), term::int(7));
/// assert_eq! {
///     &format!("{}", select_7), "(select (store ((as const (Array Int Int)) v_2) 7 0) 7)"
/// }
/// let model: VarMap<_> = vec![ val::int(17), val::int(17), val::int(13) ].into();
/// assert_eq! { select_2.eval(&model).unwrap(), val::int(13) }
/// assert_eq! { select_7.eval(&model).unwrap(), val::int(0) }
/// ```
#[inline]
pub fn select(array: Term, idx: Term) -> Term {
    app(Op::Select, vec![array, idx])
}

/// Function application.
///
/// Panics when [`try_fun`] fails. See [`try_fun`] for examples.
///
/// [`try_fun`]: fn.try_fun.html (try_fun function)
#[inline]
pub fn fun<S>(name: S, args: Vec<Term>) -> Term
where
    S: Into<String>,
{
    match try_fun(name, args) {
        Ok(res) => res,
        Err(e) => panic!("{}", e),
    }
}

/// Function application.
///
/// # Examples
///
/// ```rust
/// use hoice::{ term, term::typ, dtyp, fun };
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let _ = term::try_fun(
///     fun::test::length_fun_name(),
///     vec![ term::dtyp_new(list.clone(), "nil", vec![]) ],
/// ).expect("during function call creation");
/// ```
///
/// Constant arguments:
///
/// ```rust
/// use hoice::{ term, term::typ, dtyp, fun, val };
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let cst = term::try_fun(
///     fun::test::length_fun_name(),
///     vec![term::dtyp_new(
///         list.clone(), "insert", vec![term::int(7), term::dtyp_new(list.clone(), "nil", vec![])]
///     )],
/// ).expect("during function call creation");
/// assert_eq! { cst.val().unwrap(), val::int(1) }
/// ```
///
/// Ill-typed application:
///
/// ```rust
/// use hoice::common::*;
/// fun::test::create_length_fun();
///
/// let err = term::try_fun(
///     fun::test::length_fun_name(), vec![ term::int(7) ],
/// ).unwrap_err();
/// assert_eq! {
///     format!("{}", err),
///     format!(
///         "ill-typed application of function {}, 7 does not have type (List Int)",
///         fun::test::length_fun_name()
///     )
/// }
/// ```
///
/// Function does not exist (panic):
///
/// ```rust
/// # use hoice::common::*;
/// let err = term::try_fun(
///     "unknown_function", vec![ term::int_var(0) ]
/// ).unwrap_err();
/// assert_eq! {
///     format!("{}", err),
///     "trying to retrieve signature for unknown function unknown_function\n\
///     no function signature present".to_string()
/// }
/// ```
#[inline]
pub fn try_fun<S>(name: S, mut args: Vec<Term>) -> Result<Term, TypError>
where
    S: Into<String>,
{
    let name = name.into();
    let mut all_args_constant = true;

    fun::sig_do(&name, |info| {
        if args.len() != info.sig.len() {
            return Err(TypError::Msg(format!(
                "illegal application of function {} to {} arguments, expected {}",
                conf.bad(&name),
                args.len(),
                info.sig.len(),
            )));
        }
        for (info, arg) in info.sig.iter().zip(args.iter_mut()) {
            if arg.val().is_none() {
                all_args_constant = false
            }
            if let Some(nu_arg) = arg.force_dtyp(info.typ.clone()) {
                *arg = nu_arg
            } else if info.typ != arg.typ() {
                return Err(TypError::Msg(format!(
                    "ill-typed application of function {}, {} does not have type {}",
                    conf.bad(&name),
                    arg,
                    info.typ
                )));
            }
        }
        Ok(info.typ.clone())
    })
    .map(|typ| {
        let term = factory.mk(RTerm::new_fun(typ, name, args));
        if all_args_constant {
            if let Ok(val) = term.eval(&()) {
                cst(val)
            } else {
                term
            }
        } else {
            term
        }
    })
}

/// Creates an operator application.
///
/// This is the function all operator application functions end up calling.
#[inline]
pub fn app(op: Op, mut args: Vec<Term>) -> Term {
    let typ = expect!(
        op.type_check(& mut args) => |e|
            let res: Res<()> = Err(
                "Fatal internal type checking error, \
                please notify the developer(s)".into()
            ) ;
            let res: Res<()> = res
                .chain_err(
                    || {
                        let mut res = format!("while type checking ({}", op);
                        for arg in &args {
                            res += &format!(" {}", arg)
                        }
                        res += ")";
                        res
                    }
                );
            match e {
                term::TypError::Typ { expected, obtained, index } => res.chain_err(
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
///
/// This function assumes the term created is legal. It will panic if the term is ill-typed.
///
/// # Examples
///
/// ```rust
/// use hoice::common::*;
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let t = term::dtyp_new(
///     list.clone(),
///     "insert",
///     vec![ term::int(7), term::var(0, list) ],
/// );
/// assert_eq! { &format!("{}", t), "(insert 7 v_0)" }
/// ```
///
/// Constant term:
///
/// ```rust
/// use hoice::common::*;
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let t = term::dtyp_new(
///     list.clone(),
///     "insert",
///     vec![ term::int(7), term::dtyp_new(list, "nil", vec![]) ],
/// ); // This term is actually a constant.
/// assert_eq! { &format!("{}", t.val().unwrap()), "(insert 7 (as nil (List Int)))" }
/// ```
pub fn dtyp_new<S>(typ: Typ, name: S, args: Vec<Term>) -> Term
where
    S: Into<String>,
{
    let rterm = term::simplify::dtyp_new(typ, name.into(), args);
    factory.mk(rterm)
}

/// Creates a new datatype selector.
///
/// This function assumes the term created is legal. It will panic if the term is ill-typed.
///
/// # Examples
///
/// ```rust
/// use hoice::common::*;
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let t = term::dtyp_new(
///     list.clone(),
///     "insert",
///     vec![ term::int(7), term::var(0, list) ],
/// );
/// assert_eq! { &format!("{}", t), "(insert 7 v_0)" }
/// ```
///
/// Constant term:
///
/// ```rust
/// use hoice::common::*;
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let t = term::dtyp_new(
///     list.clone(),
///     "insert",
///     vec![ term::int(7), term::dtyp_new(list, "nil", vec![]) ],
/// ); // This term is actually a constant.
/// assert_eq! { &format!("{}", t.val().unwrap()), "(insert 7 (as nil (List Int)))" }
/// let t = term::dtyp_slc( typ::int(), "head", t );
/// assert_eq! { t.val().unwrap(), val::int(7) }
/// ```
pub fn dtyp_slc<S>(typ: Typ, name: S, term: Term) -> Term
where
    S: Into<String>,
{
    match term::simplify::dtyp_slc(typ, name.into(), term) {
        Either::Left(rterm) => factory.mk(rterm),
        Either::Right(term) => term,
    }
}

/// Creates a new datatype tester.
///
/// This function assumes the term created is legal. It will panic if the term is ill-typed.
///
/// # Examples
///
/// ```rust
/// use hoice::common::*;
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let t = term::var(0, list);
/// let t = term::dtyp_tst("insert", t);
/// assert_eq! { &format!("{}", t), "(is-insert v_0)" }
/// ```
///
/// Evaluation on non-constant term:
///
/// ```rust
/// use hoice::common::*;
/// fun::test::create_length_fun();
/// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
///
/// let t = term::dtyp_new(
///     list.clone(),
///     "insert",
///     vec![ term::int(7), term::var(0, list) ],
/// );
/// let is_nil = term::dtyp_tst("nil", t.clone());
/// # println!("is_nil: {}", is_nil);
/// assert_eq! { is_nil.val().unwrap(), val::bool(false) }
/// let is_insert = term::dtyp_tst("insert", t);
/// # println!("is_insert: {}", is_insert);
/// assert_eq! { is_insert.val().unwrap(), val::bool(true) }
/// ```
pub fn dtyp_tst<S>(name: S, term: Term) -> Term
where
    S: Into<String>,
{
    let (rterm, positive) = term::simplify::dtyp_tst(name.into(), term);
    let res = factory.mk(rterm);
    if !positive {
        not(res)
    } else {
        res
    }
}

/// Creates an operator application.
///
/// Error if the application is ill-typed (int will be cast to real automatically).
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// use hoice::errors::TypError;
/// let bool_var = term::bool_var(0);
/// let int_term = term::add( vec![ term::int_var(1), term::int(7) ] );
/// let ill_typed = term::try_app( Op::And, vec![ bool_var, int_term ] );
/// # println!("{:?}", ill_typed);
///
/// assert! { ill_typed.is_err() }
/// match ill_typed.unwrap_err() {
///     TypError::Msg(blah) => panic!("unexpected error message `{}`", blah),
///     TypError::Typ { expected, obtained, index } => {
///         assert_eq! { expected, Some(typ::bool()) }
///         assert_eq! { obtained, typ::int()        }
///         assert_eq! {    index, 1                 }
///     }
/// }
/// ```
#[inline]
pub fn try_app(op: Op, mut args: Vec<Term>) -> Result<Term, term::TypError> {
    let typ = op.type_check(&mut args)?;
    Ok(normalize(op, args, typ))
}

/// Creates a less than or equal to.
///
/// Currently rewritten as a greater than or equal to.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::le( term::int_var(7), term::int(0) );
/// assert_eq! { &format!("{}", t), "(>= (* (- 1) v_7) 0)" }
/// ```
#[inline]
pub fn le(lhs: Term, rhs: Term) -> Term {
    app(Op::Le, vec![lhs, rhs])
}

/// Creates a less than.
///
/// Currently rewritten as a greater than (reals), or a greater than or equal to (integers).
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::lt( term::int_var(7), term::int(0) );
/// assert_eq! { &format!("{}", t), "(>= (* (- 1) v_7) 1)" }
/// let t = term::lt( term::real_var(7), term::real_of(0f64) );
/// assert_eq! { &format!("{}", t), "(> (* (- 1.0) v_7) 0.0)" }
/// ```
#[inline]
pub fn lt(lhs: Term, rhs: Term) -> Term {
    app(Op::Lt, vec![lhs, rhs])
}

/// Creates a greater than.
///
/// Currently rewritten as a greater than or equal to for integers.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::gt( term::int_var(7), term::int(0) );
/// assert_eq! { &format!("{}", t), "(>= v_7 1)" }
/// let t = term::gt( term::real_var(7), term::real_of(0f64) );
/// assert_eq! { &format!("{}", t), "(> v_7 0.0)" }
/// ```
#[inline]
pub fn gt(lhs: Term, rhs: Term) -> Term {
    app(Op::Gt, vec![lhs, rhs])
}

/// Creates a greater than or equal to.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::ge( term::int_var(7), term::int(0) );
/// assert_eq! { &format!("{}", t), "(>= v_7 0)" }
/// ```
#[inline]
pub fn ge(lhs: Term, rhs: Term) -> Term {
    app(Op::Ge, vec![lhs, rhs])
}

/// Creates an equality.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::eq( term::int_var(7), term::int(2) );
/// assert_eq! { &format!("{}", t), "(= (+ v_7 (- 2)) 0)" }
/// ```
#[inline]
pub fn eq(lhs: Term, rhs: Term) -> Term {
    app(Op::Eql, vec![lhs, rhs])
}

/// Creates a distinct application.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::distinct( vec![term::int_var(7), term::int(2)] );
/// assert_eq! { &format!("{}", t), "(not (= (+ v_7 (- 2)) 0))" }
/// let t = term::distinct( vec![term::int_var(7), term::int(2), term::int_var(3)] );
/// assert_eq! { &format!("{}", t), "(distinct v_7 2 v_3)" }
/// ```
#[inline]
pub fn distinct(terms: Vec<Term>) -> Term {
    app(Op::Distinct, terms)
}

/// Creates a sum.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::add( vec![term::int_var(7), term::int(2), term::int_var(7)] );
/// assert_eq! { &format!("{}", t), "(+ 2 (* 2 v_7))" }
/// let t = term::add( vec![term::int_var(7), term::int(2), term::int(40)] );
/// assert_eq! { &format!("{}", t), "(+ v_7 42)" }
/// let t = term::add( vec![term::int(7), term::int(2)] );
/// assert_eq! { &format!("{}", t), "9" }
/// ```
#[inline]
pub fn add(kids: Vec<Term>) -> Term {
    app(Op::Add, kids)
}

/// Creates a sum, binary version.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::add2(term::int_var(7), term::int(2));
/// assert_eq! { &format!("{}", t), "(+ v_7 2)" }
/// let t = term::add2(term::int_var(7), term::int_var(7));
/// assert_eq! { &format!("{}", t), "(* 2 v_7)" }
/// ```
#[inline]
pub fn add2(kid_1: Term, kid_2: Term) -> Term {
    app(Op::Add, vec![kid_1, kid_2])
}

/// Creates a subtraction.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::sub( vec![term::int_var(3), term::int(2), term::int_var(7)] );
/// assert_eq! { &format!("{}", t), "(+ v_3 (* (- 1) v_7) (- 2))" }
/// let t = term::sub( vec![term::int_var(7), term::int(2), term::int_var(7)] );
/// assert_eq! { &format!("{}", t), "(- 2)" }
/// let t = term::sub( vec![term::int_var(7), term::int(2), term::u_minus(term::int_var(7))] );
/// assert_eq! { &format!("{}", t), "(+ (- 2) (* 2 v_7))" }
/// let t = term::sub( vec![term::int(7), term::int(2)] );
/// assert_eq! { &format!("{}", t), "5" }
/// ```
#[inline]
pub fn sub(kids: Vec<Term>) -> Term {
    app(Op::Sub, kids)
}

/// Creates a subtraction, binary version.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::sub2( term::int_var(3), term::int(2) );
/// assert_eq! { &format!("{}", t), "(+ v_3 (- 2))" }
/// let t = term::sub2( term::int_var(7), term::int_var(7) );
/// assert_eq! { &format!("{}", t), "0" }
/// ```
#[inline]
pub fn sub2(kid_1: Term, kid_2: Term) -> Term {
    app(Op::Sub, vec![kid_1, kid_2])
}

/// Creates a unary minus.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::u_minus( term::int_var(3) );
/// assert_eq! { &format!("{}", t), "(* (- 1) v_3)" }
/// let t = term::u_minus( term::int(3) );
/// assert_eq! { &format!("{}", t), "(- 3)" }
/// let t = term::u_minus( t );
/// assert_eq! { &format!("{}", t), "3" }
/// let add = term::add2( term::int_var(7), term::int(5) );
/// let t = term::u_minus( add );
/// assert_eq! { &format!("{}", t), "(+ (* (- 1) v_7) (- 5))" }
/// ```
#[inline]
pub fn u_minus(kid: Term) -> Term {
    app(Op::Sub, vec![kid])
}

/// Creates a multiplication.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::mul( vec![ term::int_var(3), term::int_var(7) ] );
/// assert_eq! { &format!("{}", t), "(* v_3 v_7)" }
/// let t = term::mul( vec![ term::int_var(3), term::int(7) ] );
/// assert_eq! { &format!("{}", t), "(* 7 v_3)" }
/// assert! { t.cmul_inspect().is_some() }
/// let t = term::mul( vec![term::int(7), term::int(3)] );
/// assert_eq! { &format!("{}", t), "21" }
/// let t = term::mul( vec![term::int_var(3), term::add2(term::int_var(7), term::int(3))] );
/// assert_eq! { &format!("{}", t), "(* v_3 (+ v_7 3))" }
/// ```
#[inline]
pub fn mul(kids: Vec<Term>) -> Term {
    app(Op::Mul, kids)
}

/// Creates a multiplication by a constant.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::cmul( 7, term::int_var(3) );
/// assert_eq! { &format!("{}", t), "(* 7 v_3)" }
/// let t = term::cmul( 7, term::int(3) );
/// assert_eq! { &format!("{}", t), "21" }
/// let t = term::cmul( 7, term::add2(term::int_var(7), term::int(3)) );
/// assert_eq! { &format!("{}", t), "(+ 21 (* 7 v_7))" }
/// ```
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
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::idiv( vec![ term::int(7), term::int_var(3) ] );
/// assert_eq! { &format!("{}", t), "(div 7 v_3)" }
/// let t = term::idiv( vec![ term::int(7), term::int(3) ] );
/// assert_eq! { &format!("{}", t), "2" }
/// ```
#[inline]
pub fn idiv(kids: Vec<Term>) -> Term {
    app(Op::IDiv, kids)
}

/// Creates a division for terms of sort `Real`.
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::div( vec![ term::real_of(7.), term::real_var(3) ] );
/// assert_eq! { &format!("{}", t), "(/ 7.0 v_3)" }
/// let t = term::div( vec![ term::real_of(7.), term::real_of(3.) ] );
/// assert_eq! { &format!("{}", t), "(/ 7 3)" }
/// ```
#[inline]
pub fn div(kids: Vec<Term>) -> Term {
    app(Op::Div, kids)
}

/// Creates a modulo application.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::modulo( term::int(7), term::int_var(3) );
/// assert_eq! { &format!("{}", t), "(mod 7 v_3)" }
/// let t = term::modulo( term::int(7), term::int(3) );
/// assert_eq! { &format!("{}", t), "1" }
/// ```
#[inline]
pub fn modulo(a: Term, b: Term) -> Term {
    app(Op::Mod, vec![a, b])
}

/// Creates a conversion from `Int` to `Real`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::to_real( term::int_var(3) );
/// assert_eq! { &format!("{}", t), "(to_real v_3)" }
/// let t = term::to_real( term::int(3) );
/// assert_eq! { &format!("{}", t), "3.0" }
/// ```
#[inline]
pub fn to_real(int: Term) -> Term {
    app(Op::ToReal, vec![int])
}

/// Creates a conversion from `Real` to `Int`.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let t = term::to_int( term::real_var(3) );
/// assert_eq! { &format!("{}", t), "(to_int v_3)" }
/// let t = term::to_int( term::real_of(3.) );
/// assert_eq! { &format!("{}", t), "3" }
/// ```
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
    /// A new application to normalize.
    App(Typ, Op, Vec<NormRes>),
}

/// Normalizes an operation application.
fn normalize_app(mut op: Op, mut args: Vec<Term>, typ: Typ) -> NormRes {
    use crate::term::simplify;

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
        NormRes::Term(factory.mk(RTerm::new_app(typ, op, args)))
    }
}

//! Hash consed functions.
//!
//! "Functions" of this module are user-defined recursive functions and non-necessarily recursive
//! function create by hoice, typically when working with datatypes. Function can be evaluated and
//! can be used as qualifiers (for datatypes, typically).
//!
//! # Usage
//!
//! Creating (mutually) recursive is tricky: when constructing the body of the function(s), the
//! definition does not really exist yet ---since we're constructing the body which is part of the
//! definition. So if `f` calls itself recursively, we cannot create the term `(f <args>)` because
//! `f` does not really exist yet: hoice will fail to check that the call is legal because it
//! cannot retrieve `f`'s definition.
//!
//! To address this problem, this module allows to register some *function declarations*. The idea
//! is to
//!
//! - create a [`FunSig`] for all mutually recursive functions
//! - register these signatures using [`register_sig`], meaning that they become visible during
//!   term creation
//! - construct the bodies, including the recursive calls which are now legal
//! - retrieve the signatures with [`retrieve_sig`] and add the bodies constructed in the previous
//!   step
//! - create the [`RFun`] from the `FunSig`, and register it as a function using [`new`]
//!
//! # Examples
//!
//! Consider the following function
//!
//! ```lisp
//! (define-funs-rec
//!   (
//!     (len ( (l (List Int)) ) Int)
//!   )
//!   (
//!     (ite
//!       (= l nil)
//!       0
//!       (+ 1 (len (tail l)))
//!     )
//!   )
//! )
//! ```
//!
//! Then creating this function works as follows.
//!
//! ```rust
//! use hoice::{ common::*, info::VarInfo };
//! let int_list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
//! let fun_name = "fun_test_len";
//!
//! let mut var_infos = VarInfos::new();
//! let v_0 = var_infos.next_index();
//! var_infos.push( VarInfo::new("l", int_list.clone(), v_0) );
//!
//! let signature = fun::FunSig::new(fun_name, var_infos, typ::int());
//! fun::register_sig(signature).expect("while registering function signature");
//!
//! // Function declared, we can now create terms that use it.
//! let v_0 = term::var(v_0, int_list.clone());
//! let tail_of_v_0 = term::dtyp_slc(int_list.clone(), "tail", v_0.clone());
//! let rec_call = term::fun(fun_name, vec![ tail_of_v_0 ]);
//! let body = term::ite(
//!     term::eq(v_0.clone(), term::dtyp_new(int_list.clone(), "nil", vec![])),
//!     term::int(0),
//!     term::add( vec![ term::int(1), rec_call ] )
//! );
//! assert_eq! {
//!     format!("(ite (not (is-insert v_0)) 0 (+ ({} (tail v_0)) 1))", fun_name),
//!     format!("{}", body)
//! }
//!
//! // Retrieve and complete function definition.
//! let sig = fun::retrieve_sig(fun_name).expect("while retrieving signature");
//! let def = sig.into_fun(body);
//! let _ = fun::new(def).expect("while hashconsing function");
//!
//! // Done!
//! let len_app = term::fun(
//!     fun_name, vec![
//!         term::dtyp_new(
//!             int_list.clone(), "insert", vec![
//!                 term::int_var(0), term::dtyp_new(int_list.clone(), "nil", vec![])
//!             ]
//!         )
//!     ]
//! );
//! assert_eq! {
//!     format!("({} (insert v_0 (as nil (List Int))))", fun_name),
//!     format!("{}", len_app)
//! }
//!
//! let model: VarMap<Val> = vec![val::int(7)].into();
//! assert_eq! { len_app.eval(& model).expect("during evaluation"), val::int(1) }
//! ```
//!
//! # Testing
//!
//! The [`test`] module allows to create a length function over lists and should only be used in
//! documentation/unit tests. The module does not exist in `release`.
//!
//! [`FunSig`]: struct.FunSig.html (FunSig struct)
//! [`register_sig`]: fn.register_sig.html (register_sig function)
//! [`retrieve_sig`]: fn.retrieve_sig.html (retrieve_sig function)
//! [`Fun`]: type.Fun.html (Fun type)
//! [`new`]: fn.new.html (new function)
//! [`test`]: test/index.hmtl (function test module)

use std::sync::{RwLockReadGuard, RwLockWriteGuard};

use crate::common::*;

/// A hashconsed function.
pub type Fun = Arc<RFun>;

/// Type of the function factory.
type Factory = RwLock<BTreeMap<String, Fun>>;
lazy_static! {
    /// Function factory.
    static ref factory: Factory = RwLock::new(
        BTreeMap::new()
    ) ;

    /// Stores function signatures to construct the functions' bodies.
    static ref fun_sigs: RwLock< BTreeMap<String, FunSig> > = RwLock::new(
        BTreeMap::new()
    ) ;
}

/// Registers a function signature.
///
/// Used to create (mutually) recursive function(s), see [module-level documentation].
///
/// [module-level documentation]: index.html (module-level documentation)
pub fn register_sig(fun: FunSig) -> Res<()> {
    if let Ok(mut decs) = fun_sigs.write() {
        let prev = decs.insert(fun.name.clone(), fun);
        if let Some(prev) = prev {
            bail!("the function {} is declared twice", conf.bad(&prev.name))
        }
    } else {
        bail!("unable to access function declarations")
    }
    Ok(())
}

/// Retrieves a function signature.
///
/// Used to create (mutually) recursive function(s), see [module-level documentation].
///
/// [module-level documentation]: index.html (module-level documentation)
pub fn retrieve_sig(fun: &str) -> Res<FunSig> {
    if let Ok(mut sigs) = fun_sigs.write() {
        if let Some(sig) = sigs.remove(fun) {
            Ok(sig)
        } else {
            let mut s = format!(
                "trying to retrieve signature for unknown function {}\n",
                conf.bad(fun)
            );
            if sigs.is_empty() {
                s += "no function signature present"
            } else {
                s += "function(s) signatures available:";
                for (name, _) in sigs.iter() {
                    s += " ";
                    s += name;
                    s += ","
                }
            }

            bail!(s)
        }
    } else {
        bail!("unable to access function declarations")
    }
}

/// Accesses the signature of a function, if any.
///
/// Used to type-check function calls.
pub fn sig_do<F, T>(fun: &str, mut f: F) -> Result<T, TypError>
where
    F: for<'a> FnMut(&'a FunSig) -> Result<T, TypError>,
{
    if let Ok(defs) = factory.read() {
        if let Some(def) = defs.get(fun) {
            return f(&def.info);
        }
    } else {
        return Err(TypError::Msg("unable to retrieve function factory".into()));
    }

    if let Ok(sigs) = fun_sigs.read() {
        if let Some(sig) = sigs.get(fun) {
            f(sig)
        } else {
            let mut s = format!(
                "trying to retrieve signature for unknown function {}\n",
                conf.bad(fun)
            );
            if sigs.is_empty() {
                s += "no function signature present"
            } else {
                s += "function(s) signatures available:";
                for (name, _) in sigs.iter() {
                    s += " ";
                    s += name;
                    s += ","
                }
            }

            return Err(TypError::Msg(s));
        }
    } else {
        return Err(TypError::Msg(
            "unable to retrieve function declarations".into(),
        ));
    }
}

/// Read version of the factory.
fn read_factory<'a>() -> RwLockReadGuard<'a, BTreeMap<String, Fun>> {
    if let Ok(res) = factory.read() {
        res
    } else {
        panic!("failed to access function factory (read)")
    }
}
/// Write version of the factory.
fn write_factory<'a>() -> RwLockWriteGuard<'a, BTreeMap<String, Fun>> {
    factory
        .write()
        .expect("failed to access function factory (write)")
}

macro_rules! factory {
    (read) => {
        &read_factory()
    };
    (write) => {
        &mut write_factory()
    };
}

/// Iterates over all function definitions.
pub fn iter<F>(mut f: F) -> Res<()>
where
    F: FnMut(&Fun) -> Res<()>,
{
    let defs = read_factory();
    for def in defs.values() {
        f(def)?
    }
    Ok(())
}

/// Creates a function definition.
///
/// Fails if the function is already defined.
///
/// # Examples
///
/// ```rust
/// use hoice::{ common::*, fun, info::VarInfo };
/// let sig: VarInfos = vec![ VarInfo::new("v_0", typ::int(), 0.into()) ].into();
/// let fun_name = "fun_new_test_identity";
/// let sig = fun::FunSig::new(fun_name, sig, typ::int());
/// let def = sig.into_fun( term::int_var(0) );
/// fun::new(def.clone()).expect("during first function registration");
/// assert_eq! {
///     format!("{}", fun::new(def).unwrap_err()),
///     format!("attempting to redefine function `{}`", fun_name)
/// }
/// ```
pub fn new(fun: RFun) -> Res<Fun> {
    let fun = Arc::new(fun);
    let f = factory!(write);
    let prev = f.insert(fun.name().clone(), fun.clone());

    if let Some(prev) = prev {
        bail!("attempting to redefine function `{}`", prev.name())
    }

    Ok(fun)
}

/// Groups all functions by dependencies.
///
/// Returns a list of functions classes. A function class is a list of function that depend on each
/// other, meaning that they must be defined together at SMT-level.
fn ordered() -> Res<Vec<Vec<Fun>>> {
    let mut all: Vec<_> = read_factory().values().cloned().collect();

    let mut groups = vec![];

    while let Some(fun) = all.pop() {
        let mut group = vec![fun];
        if !group[0].deps.is_empty() {
            all.retain(|fun| {
                if group[0].deps.contains(fun.name()) {
                    group.push(fun.clone());
                    false
                } else {
                    true
                }
            });
        }
        groups.push(group)
    }

    Ok(groups)
}

/// Defines a function, and all functions related to it.
fn write<W>(w: &mut W, fun: &RFun, pref: &str) -> Res<()>
where
    W: Write,
{
    let f = factory!(read);
    let mut all = vec![];

    all.reserve(fun.deps.len() + 1);
    all.push(fun);
    for dep in &fun.deps {
        if let Some(dep) = f.get(dep) {
            all.push(dep)
        } else {
            bail!(
                "function `{}` depends on unknown function `{}`",
                conf.emph(fun.name()),
                conf.bad(&dep)
            )
        }
    }

    writeln!(w, "{}({} (", pref, consts::keywords::cmd::def_funs_rec)?;

    // Write all signatures.
    for fun in &all {
        write!(w, "{}  (", pref)?;
        write!(w, "{} (", fun.name())?;
        for info in fun.sig() {
            write!(w, " ({} {})", info.idx.default_str(), info.typ)?
        }
        writeln!(w, " ) {})", fun.typ())?
    }

    writeln!(w, "{}) (", pref)?;

    // Write all definitions.
    for fun in all.drain(0..) {
        write!(w, "{}  ", pref)?;
        fun.def.write(w, |w, var| var.default_write(w))?;
        writeln!(w)?
    }

    writeln!(w, "{}) )", pref)?;

    Ok(())
}

/// Defines all the functions needed for a model to make sense.
pub fn write_for_model<W: Write>(w: &mut W, pref: &str, model: ConjModelRef) -> Res<()> {
    {
        // Do nothing if there are no functions at all.
        let f = factory!(read);
        if f.is_empty() {
            return Ok(());
        }
    }

    let mut set = BTreeSet::new();
    for defs in model {
        for (_, ttermss) in defs {
            for tterms in ttermss {
                tterms.collect_funs(&mut set)
            }
        }
    }

    let mut ordered = ordered()?;

    let mut cnt = 0;
    while cnt < ordered.len() {
        if ordered[cnt].iter().any(|def| set.contains(&def.info.name)) {
            for fun in &ordered[cnt] {
                set.remove(&fun.info.name);
                for name in &fun.deps {
                    set.remove(name);
                }
            }
            cnt += 1
        } else {
            ordered.swap_remove(cnt);
        }
    }

    write_groups(w, pref, false, ordered)
}

/// Defines all the functions in SMT-LIB.
pub fn write_all<W: Write>(w: &mut W, pref: &str, invariants: bool) -> Res<()> {
    write_groups(w, pref, invariants, ordered()?)
}

/// Defines a bunch of functions in SMT-LIB.
fn write_groups<W: Write>(
    w: &mut W,
    pref: &str,
    invariants: bool,
    groups: Vec<Vec<Fun>>,
) -> Res<()> {
    for group in groups {
        if group.len() == 1 {
            let fun = &group[0];

            let def_key = if fun.recursive {
                consts::keywords::cmd::def_fun_rec
            } else {
                consts::keywords::cmd::def_fun
            };

            writeln!(w, "{}({} {}", pref, def_key, fun.name())?;
            write!(w, "{}  (", pref)?;
            for info in fun.sig() {
                write!(w, " ({} {})", info.idx.default_str(), info.typ)?
            }
            writeln!(w, " ) {}", fun.typ())?;

            write!(w, "{}  ", pref)?;

            fun.def.write(w, |w, var| var.default_write(w))?;
            writeln!(w, "\n{})", pref)?
        } else if group.len() > 1 {
            writeln!(w, "{}({} (", pref, consts::keywords::cmd::def_funs_rec)?;

            // Write all signatures.
            for fun in &group {
                write!(w, "{}  (", pref)?;
                write!(w, "{} (", fun.name())?;
                for info in fun.sig() {
                    write!(w, " ({} {})", info.idx.default_str(), info.typ)?
                }
                writeln!(w, " ) {})", fun.typ())?
            }

            writeln!(w, "{}) (", pref)?;

            // Write all definitions.
            for fun in &group {
                write!(w, "{}  ", pref)?;
                fun.def.write(w, |w, var| var.default_write(w))?;
                writeln!(w)?
            }

            writeln!(w, "{}) )", pref)?
        }

        writeln!(w)?;

        if invariants {
            let mut one_or_more = false;
            for fun in group {
                for inv in &fun.invariants {
                    one_or_more = true;
                    writeln!(w, "{}(assert", pref)?;
                    writeln!(w, "{}  (forall", pref)?;
                    write!(w, "{}    (", pref)?;
                    for info in fun.sig() {
                        write!(w, " ({} {})", info.idx.default_str(), info.typ)?
                    }
                    writeln!(w, " )")?;
                    write!(w, "{}    ", pref)?;
                    inv.write(w, |w, var| var.default_write(w))?;
                    writeln!(w, "\n{}) )", pref)?
                }
            }

            if one_or_more {
                writeln!(w)?
            }
        }
    }

    Ok(())
}

/// Retrieves all function definitions.
///
/// This used by term evaluation to zero-copy-evaluate function.
pub fn all_defs<'a>() -> ::std::sync::RwLockReadGuard<'a, BTreeMap<String, Fun>> {
    if let Ok(f) = factory.read() {
        f
    } else {
        panic!("failed to access function factory (read)")
    }
}

/// Retrieves the definition of a function.
pub fn get(name: &str) -> Option<Fun> {
    let f = factory!(read);
    f.get(name).cloned()
}

/// A function signature, used when creating (mutually) recursive function(s).
///
/// For details, see [module-level documentation].
///
/// [module-level documentation]: index.html (module-level documentation)
#[derive(Debug, Clone)]
pub struct FunSig {
    /// Name.
    pub name: String,
    /// Signature.
    pub sig: VarInfos,
    /// Type.
    pub typ: Typ,
}
impl PartialEq for FunSig {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}
impl Eq for FunSig {}

impl PartialOrd for FunSig {
    fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
        self.name.partial_cmp(&other.name)
    }
}
impl Ord for FunSig {
    fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

impl ::std::hash::Hash for FunSig {
    fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}
impl FunSig {
    /// Constructor.
    pub fn new<S>(name: S, sig: VarInfos, typ: Typ) -> Self
    where
        S: Into<String>,
    {
        FunSig {
            name: name.into(),
            sig,
            typ,
        }
    }

    /// Transforms a signature in a function definition.
    pub fn into_fun(self, def: Term) -> RFun {
        let mut deps = BTreeSet::new();
        let mut recursive = false;
        def.iter(|trm| {
            if let Some((name, _)) = trm.fun_inspect() {
                if name == &self.name {
                    recursive = true
                } else {
                    deps.insert(name.to_string());
                }
            }
        });

        RFun {
            info: self,
            deps,
            def,
            synthetic: None,
            invariants: TermSet::new(),
            recursive,
        }
    }
}

/// Real structure for functions.
///
/// For details, see [module-level documentation].
///
/// [module-level documentation]: index.html (module-level documentation)
#[derive(Debug, Clone)]
pub struct RFun {
    /// Signature.
    pub info: FunSig,
    /// Other functions this function depends on.
    pub deps: BTreeSet<String>,
    /// Definition.
    pub def: Term,
    /// The index of the predicate this function was created for.
    pub synthetic: Option<PrdIdx>,
    /// Invariants of the function.
    pub invariants: TermSet,
    /// True if the function is recursive.
    recursive: bool,
}

impl ::std::ops::Deref for RFun {
    type Target = FunSig;
    fn deref(&self) -> &FunSig {
        &self.info
    }
}

impl PartialEq for RFun {
    fn eq(&self, other: &Self) -> bool {
        self.info.name == other.info.name
    }
}
impl Eq for RFun {}

impl PartialOrd for RFun {
    fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
        self.info.name.partial_cmp(&other.info.name)
    }
}
impl Ord for RFun {
    fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
        self.info.name.cmp(&other.info.name)
    }
}

impl ::std::hash::Hash for RFun {
    fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
        self.info.name.hash(state)
    }
}

impl RFun {
    /// Constructor.
    ///
    /// The dependencies are initially empty, and the definition is set to
    /// `true`.
    pub fn new<S: Into<String>>(name: S, sig: VarInfos, typ: Typ) -> Self {
        let name = name.into();
        RFun {
            info: FunSig::new(name, sig, typ),
            deps: BTreeSet::new(),
            def: term::tru(),
            synthetic: None,
            invariants: TermSet::new(),
            recursive: false,
        }
    }

    /// Name of the function.
    #[inline]
    pub fn name(&self) -> &String {
        &self.info.name
    }
    /// Signature of the function.
    #[inline]
    pub fn sig(&self) -> &VarInfos {
        &self.info.sig
    }
    /// Type of the function.
    #[inline]
    pub fn typ(&self) -> &Typ {
        &self.info.typ
    }

    /// Flips the flag indicating that the function was created internally for a
    /// predicate.
    pub fn set_synthetic(&mut self, pred: PrdIdx) {
        self.synthetic = Some(pred)
    }

    /// True if the function is recursive.
    pub fn is_recursive(&self) -> bool {
        self.recursive
    }

    /// Checks the function is legal.
    pub fn check(&self) -> Res<()> {
        for dep in &self.deps {
            if get(dep).is_none() {
                bail!(
                    "function `{}` depends on unknown function `{}`",
                    conf.emph(self.name()),
                    conf.bad(dep)
                )
            }
        }
        Ok(())
    }

    /// Writes itself and all its dependencies.
    pub fn write<W>(&self, w: &mut W, pref: &str) -> Res<()>
    where
        W: Write,
    {
        write(w, self, pref)
    }
}

/// Stores functions from and to some type.
///
/// Automatically retrieves everything on creation. Only considers unary functions.
///
/// # Examples
///
/// ```rust
/// use hoice::{ parse, fun::Functions, common::* };
/// let (
///     lst_name, len_name, rpt_name, rdc_name
/// ) = (
///     "FunFunctionsTestLst",
///     "FunFunctionsTestLen",
///     "FunFunctionsTestRpt",
///     "FunFunctionsTestRdc",
/// );
/// parse::fun_dtyp(&format!("
///     (declare-datatypes ( ({lst_name} 1) ) (
///       (par (T) (
///         (nil)
///         (cons (head T) (tail ({lst_name} T)))
///       ) )
///     ) )
///     (define-funs-rec
///       ( ({len_name} ( (l ({lst_name} Int)) ) Int) )
///       ( (ite (= l nil) 0 (+ 1 ({len_name} (tail l)))) )
///     )
///     (define-funs-rec
///       ( ({rpt_name} ( (n Int) ) ({lst_name} Int)) )
///       ( (ite (= n 0) nil (cons n ({rpt_name} (- n 1)))) )
///     )
///     (define-funs-rec
///       ( ({rdc_name} ( (l ({lst_name} Int)) ) ({lst_name} Int)) )
///       ( (ite (= l nil) nil (tail l)) )
///     )
///     (exit)
/// ",
///     lst_name = lst_name,
///     len_name = len_name,
///     rpt_name = rpt_name,
///     rdc_name = rdc_name,
/// ));
/// let int_lst = typ::dtyp(
///     dtyp::get(lst_name).expect("while retrieving dtyp"), vec![typ::int()].into()
/// );
/// let funs = Functions::new(int_lst);
/// assert_eq! { &funs.from_typ[0].name, len_name }
/// assert_eq! { &funs.to_typ[0].name, rpt_name }
/// assert_eq! { &funs.from_to_typ[0].name, rdc_name }
/// ```
#[derive(Debug, Clone)]
pub struct Functions {
    /// Type these functions are for.
    pub typ: Typ,
    /// Functions from this type to another one.
    pub from_typ: Vec<Fun>,
    /// Function from another type to this one.
    pub to_typ: Vec<Fun>,
    /// Functions from this type to itself.
    pub from_to_typ: Vec<Fun>,
}
impl Functions {
    /// Constructor.
    pub fn new(typ: Typ) -> Self {
        let f = factory!(read);

        let mut from_typ = vec![];
        let mut to_typ = vec![];
        let mut from_to_typ = vec![];

        'find_funs: for fun in f.values() {
            let mut sig = fun.sig.iter();

            let ftyp = match sig.next() {
                Some(info) => info.typ == typ && sig.next().is_none(),
                _ => false,
            };

            let ttyp = fun.typ() == &typ;

            match (ftyp, ttyp) {
                (true, true) => from_to_typ.push(fun.clone()),
                (true, false) => from_typ.push(fun.clone()),
                (false, true) => to_typ.push(fun.clone()),
                (false, false) => continue 'find_funs,
            }
        }

        Functions {
            typ,
            from_typ,
            to_typ,
            from_to_typ,
        }
    }
}

/// Test-related stuff for functions.
///
/// This module is not available in `release` as it should only be used for testing purposes.
#[cfg(debug_assertions)]
pub mod test {

    /// Name of the length function over `(List Int)` (test mode only).
    pub fn length_fun_name() -> &'static str {
        "length"
    }

    /// Creates the list datatype and a length function over `(List Int)` this should only be used
    /// in (doc) tests.
    pub fn create_length_fun() {
        use super::*;
        let name = length_fun_name();
        if get(name).is_some() {
            return ();
        }

        crate::parse::fun_dtyp(&format!(
            "\
            (define-funs-rec
              (
                ({name} ( (l (List Int)) ) Int)
              )
              (
                (ite
                  (= l nil)
                  0
                  (+ 1 ({name} (tail l)))
                )
              )
            )
            (exit)
        ",
            name = name
        ))
    }
}

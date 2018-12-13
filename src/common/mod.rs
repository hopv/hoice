//! Base types and functions.

use clap::crate_version;
use mylib::impl_fmt;

pub use std::{
    collections::{BTreeMap, BTreeSet},
    io::stdout,
    io::{
        Result as IoRes, {Read, Write},
    },
    sync::{
        mpsc::{Receiver, Sender},
        Arc, RwLock,
    },
};

pub use either::Either;
pub use error_chain::bail;
pub use hashconsing::{coll::*, HashConsed, HashConsign};
pub use lazy_static::lazy_static;
pub use mylib::common::hash::*;
pub use num::{One, Signed, Zero};
pub use rand_xorshift::XorShiftRng as Rng;
pub use rsmt2::{actlit::Actlit, print::Expr2Smt, SmtRes, Solver};

pub use crate::{
    common::consts::keywords,
    dtyp,
    dtyp::DTyp,
    errors::*,
    fun,
    fun::Fun,
    instance::{Clause, Instance},
    term,
    term::{typ, Op, Quant, RTerm, TTerm, TTermSet, TTerms, Term, Typ},
    val,
    val::Val,
    var_to,
    var_to::{vals::SubsumeExt, VarTerms, VarVals},
};

mod wrappers;

#[macro_use]
pub mod macros;
pub mod config;

#[macro_use]
pub mod msg;
pub mod consts;
pub mod profiling;
pub mod smt;

pub use self::config::*;
pub use self::profiling::{CanPrint, Profiler};
pub use self::wrappers::*;

lazy_static! {
    /// Configuration from clap.
    pub static ref conf: Config = Config::clap();
    static ref version_string: String = crate_version!().into();
    /// Version with revision info.
    pub static ref version: & 'static str = & version_string;
}

// |===| Helpers.

/// Provides a discard function that drops anything.
pub trait Discard: Sized {
    /// Drops self.
    fn discard(self) {}
}
impl<T> Discard for T {}

/// Prints the stats if asked. Does nothing in bench mode.
#[cfg(feature = "bench")]
pub fn print_stats(_: &'static str, _: Profiler) {}
/// Prints the stats if asked. Does nothing in bench mode.
#[cfg(not(feature = "bench"))]
pub fn print_stats(name: &str, profiler: Profiler) {
    if conf.stats {
        let others = profiler.drain_others();
        println!();
        profiler.print(name, "", &["data"]);
        println!();
        for (name, other) in others {
            print_stats(&name, other)
        }
    }
}

/// Lock corrupted error.
pub fn corrupted_err<T>(_: T) -> Error {
    "[bug] lock on learning data is corrupted...".into()
}

/// Notifies the user and reads a line from stdin.
pub fn pause(s: &str, _profiler: &Profiler) {
    let mut dummy = String::new();
    println!();
    println!("; {} {}...", conf.emph("press return"), s);
    let _ = profile!(
      |_profiler| wrap {
        ::std::io::stdin().read_line(& mut dummy)
      } "waiting for user input"
    );
}

/// Notifies the user through a message and reads a line from stdin.
pub fn pause_msg(core: &msg::MsgCore, s: &str) {
    let mut dummy = String::new();
    let _ = core.msg(format!("; {} {}...", conf.emph("press return"), s));
    let _ = ::std::io::stdin().read_line(&mut dummy);
}

/// Identity function.
pub fn identity<T>(t: T) -> T {
    t
}

/// Creates a directory if it doesn't exist.
pub fn mk_dir<P: AsRef<::std::path::Path>>(path: P) -> Res<()> {
    use std::fs::DirBuilder;
    DirBuilder::new().recursive(true).create(path)?;
    Ok(())
}

/// Compares two data metrics.
///
/// Takes the amount of classified and unknown data from two data collections
/// and returns `Greater` if the first collection is considered better.
/// Typically because it has more classified data, or no unknown data.
///
/// # Examples
///
/// ```rust
/// use std::cmp::Ordering::* ;
/// use hoice::common::cmp_data_metrics as cmp ;
///
/// # println! ( "10, 0, 5, 0" ) ;
/// assert_eq! { cmp(10,  0,  5,  0), Greater }
/// # println! ( "5, 0, 10, 0" ) ;
/// assert_eq! { cmp( 5,  0, 10,  0), Less }
///
/// # println! ( "\n10, 0, 15, 10" ) ;
/// assert_eq! { cmp(10,  0, 15, 10), Greater }
/// # println! ( "15, 10, 10, 0" ) ;
/// assert_eq! { cmp(15, 10, 10,  0), Less }
///
/// # println! ( "\n15, 10, 15, 70" ) ;
/// assert_eq! { cmp(15, 10, 15, 70), Greater }
/// # println! ( "15, 70, 15, 10" ) ;
/// assert_eq! { cmp(15, 70, 15, 10), Less }
///
/// # println! ( "\n15, 70, 20, 90" ) ;
/// assert_eq! { cmp(15, 70, 20, 90), Greater }
/// # println! ( "20, 90, 15, 70" ) ;
/// assert_eq! { cmp(20, 90, 15, 70), Less }
///
/// # println! ( "\n20, 70, 15, 70" ) ;
/// assert_eq! { cmp(20, 70, 15, 70), Greater }
/// # println! ( "15, 70, 20, 70" ) ;
/// assert_eq! { cmp(15, 70, 20, 70), Less }
/// ```
pub fn cmp_data_metrics(
    classified_1: usize,
    unknown_1: usize,
    classified_2: usize,
    unknown_2: usize,
) -> ::std::cmp::Ordering {
    use std::cmp::Ordering::*;

    match (unknown_1 == 0, unknown_2 == 0) {
        (true, false) => Greater,
        (false, true) => Less,

        (true, true) => classified_1.cmp(&classified_2),

        (false, false) => match (classified_1 == 0, classified_2 == 0) {
            (true, false) => Less,
            (false, true) => Greater,

            (true, true) => unknown_1.cmp(&unknown_2),

            (false, false) => match (classified_1.cmp(&classified_2), unknown_1.cmp(&unknown_2)) {
                (Greater, Greater) => (classified_1 - classified_2).cmp(&(unknown_1 - unknown_2)),
                (Greater, _) | (Equal, Less) => Greater,

                (Less, Less) => (classified_2 - classified_1)
                    .cmp(&(unknown_2 - unknown_1))
                    .reverse(),
                (Less, _) | (Equal, Greater) => Less,

                (Equal, Equal) => Equal,
            },
        },
    }
}

// |===| Type and traits aliases.

/// Integers.
pub type Int = ::num::BigInt;
/// Rationals.
pub type Rat = ::num::BigRational;
/// Converts a float into a rational.
pub fn rat_of_float(f: f64) -> Rat {
    Rat::from_float(f).expect("can't construct a rational from NaN")
}

/// A set of terms.
pub type TermSet = HConSet<Term>;
/// A map from terms to stuff.
pub type TermMap<T> = HConMap<Term, T>;

/// A set of types.
pub type TypSet = HConSet<Typ>;
/// A map from terms to stuff.
pub type TypMap<T> = HConMap<Typ, T>;

/// A signature.
pub type Sig = VarMap<Typ>;

/// A predicate application.
pub type PredApp = (PrdIdx, VarTerms);

/// Some predicate applications.
pub type PredApps = PrdHMap<var_to::terms::VarTermsSet>;
/// Predicate application alias type extension.
pub trait PredAppsExt {
    /// Insert a predicate application. Returns true if the application is new.
    fn insert_pred_app(&mut self, pred: PrdIdx, args: VarTerms) -> bool;
}
impl PredAppsExt for PredApps {
    fn insert_pred_app(&mut self, pred: PrdIdx, args: VarTerms) -> bool {
        self.entry(pred)
            .or_insert_with(|| var_to::terms::VarTermsSet::with_capacity(4))
            .insert(args)
    }
}

/// Predicate information.
pub type Preds = PrdMap<crate::info::Pred>;
/// Variable information.
pub type VarInfos = VarMap<crate::info::VarInfo>;

/// Maps predicates to optional terms.
pub type Candidates = PrdMap<Option<Term>>;
unsafe impl<T: Send> Send for PrdMap<T> {}

/// Teaching result.
pub enum TeachRes {
    /// A model.
    Model(Candidates),
    /// An unsat result.
    Unsat(crate::unsat_core::UnsatRes),
}

/// Quantified variables for a top term.
pub type Quantfed = VarHMap<Typ>;

/// Dnf definition for a predicate.
pub type Dnf = Vec<(Quantfed, TTermSet)>;
/// Dnf definition for a predicate, reference version.
pub type DnfRef<'a> = &'a [(Quantfed, TTermSet)];

/// Associates predicates to some quantified variables and some top terms.
pub type Model = Vec<(PrdIdx, TTerms)>;
/// Reference version of a model.
pub type ModelRef<'a> = &'a [(PrdIdx, TTerms)];

/// A conjunction of candidates.
pub type ConjCandidates = PrdHMap<Vec<TTerms>>;

/// A model where definitions are conjunctions.
pub type ConjModel = Vec<Vec<(PrdIdx, Vec<TTerms>)>>;
/// A model of conjunctions, reference version.
pub type ConjModelRef<'a> = &'a [Vec<(PrdIdx, Vec<TTerms>)>];

/// A model or unsat.
#[derive(Clone, PartialEq, Eq)]
pub enum MaybeModel<M: Clone + PartialEq + Eq> {
    /// Unsat result.
    Unsat,
    /// A model.
    Model(M),
}
impl<M: Clone + PartialEq + Eq> MaybeModel<M> {
    /// True if unsat.
    pub fn is_unsat(&self) -> bool {
        *self == MaybeModel::Unsat
    }
    /// Turns itself to an option.
    pub fn into_option(self) -> Option<M> {
        if let MaybeModel::Model(model) = self {
            Some(model)
        } else {
            None
        }
    }
}

/// Indicates a bias in a counterexample for some clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bias {
    /// Left bias: the whole LHS of the clause should be considered positive.
    Lft,
    /// Right bias: the RHS should be considered negative.
    Rgt,
    /// Right bias: the RHS should be considered negative, and the whole LHS
    /// should be considered positive **except** for the predicate application
    /// mentioned.
    NuRgt(PrdIdx, VarTerms),
    /// No bias.
    Non,
}
impl Bias {
    /// True if `Non`.
    pub fn is_none(&self) -> bool {
        *self == Bias::Non
    }

    /// Pretty string representation.
    pub fn to_string(&self, instance: &Instance) -> String {
        match *self {
            Bias::NuRgt(pred, ref args) => format!("right({} {})", instance[pred], args),
            Bias::Lft => "left".into(),
            Bias::Rgt => "right".into(),
            Bias::Non => "none".into(),
        }
    }
}
impl_fmt! {
  Bias(self, fmt) {
    match * self {
      Bias::Lft => write!(fmt, "left"),
      Bias::Rgt => write!(fmt, "right"),
      Bias::NuRgt(pred, ref args) => write!(fmt, "right({} {})", pred, args),
      Bias::Non => write!(fmt, "none"),
    }
  }
}

/// Alias type for a counterexample for a clause.
pub type Cex = var_to::vals::RVarVals;
/// Alias type for a counterexample for a clause.
pub type BCex = (Cex, Bias);
/// Alias type for a counterexample for a sequence of clauses.
pub type Cexs = ClsHMap<Vec<BCex>>;

/// Signature trait, for polymorphic term insertion.
#[cfg_attr(feature = "cargo-clippy", allow(len_without_is_empty))]
pub trait Signature {
    /// Type of a variable.
    fn get(&self, var: VarIdx) -> Typ;
    /// Length of the signature.
    fn len(&self) -> usize;
}
impl Signature for VarMap<crate::info::VarInfo> {
    fn len(&self) -> usize {
        VarMap::len(self)
    }
    fn get(&self, var: VarIdx) -> Typ {
        self[var].typ.clone()
    }
}
impl Signature for VarMap<Typ> {
    fn len(&self) -> usize {
        VarMap::len(self)
    }
    fn get(&self, var: VarIdx) -> Typ {
        self[var].clone()
    }
}

/// Implemented by types lending themselves to evaluation.
#[cfg_attr(feature = "cargo-clippy", allow(len_without_is_empty))]
pub trait Evaluator {
    /// Retrieves the value associated with a variable.
    fn get(&self, var: VarIdx) -> &Val;
    /// Number of variables the evaluator supports.
    fn len(&self) -> usize;
    /// Prints itself (for debug).
    fn print(&self);
}
impl Evaluator for VarMap<Val> {
    #[inline]
    fn get(&self, var: VarIdx) -> &Val {
        &self[var]
    }
    #[inline]
    fn len(&self) -> usize {
        VarMap::len(self)
    }
    fn print(&self) {
        println!("varmap:");
        print!("  ");
        for (var, val) in self.index_iter() {
            print!("{} -> {}, ", var, val)
        }
        println!()
    }
}
impl Evaluator for () {
    #[inline]
    fn get(&self, _: VarIdx) -> &Val {
        panic!("trying actual evaluation with unit")
    }
    #[inline]
    fn len(&self) -> usize {
        0
    }
    fn print(&self) {
        println!("()")
    }
}
/// This implements a redirection `(map, vals)`, where a variable `var` from
/// the term evaluated is evaluated to `vals[ map[var] ]`.
impl<'a, E> Evaluator for (&'a VarMap<(VarIdx, Typ)>, &'a E)
where
    E: Evaluator,
{
    #[inline]
    fn get(&self, var: VarIdx) -> &Val {
        self.1.get(self.0[var].0)
    }
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }
    fn print(&self) {
        println!("varmap<(varidx, typ)>");
        print!("  ");
        for (v1, (v2, _)) in self.0.index_iter() {
            print!("{} -> {}", v1, v2)
        }
        println!();
        self.1.print()
    }
}

/// Something that can be evaluated to a boolean.
pub trait CanBEvaled: std::fmt::Display {
    /// Evaluates self.
    fn evaluate<E>(&self, e: &E) -> Res<Option<bool>>
    where
        E: Evaluator;
}
impl CanBEvaled for Term {
    fn evaluate<E>(&self, args: &E) -> Res<Option<bool>>
    where
        E: Evaluator,
    {
        self.bool_eval(args)
    }
}

/// Information returned by preprocessing techniques.
#[must_use]
#[derive(Debug, Default)]
pub struct RedInfo {
    /// Number of predicates eliminated.
    pub preds: usize,
    /// Number of clauses removed.
    pub clauses_rmed: usize,
    /// Number of clauses created.
    pub clauses_added: usize,
    /// Number of arguments removed.
    pub args_rmed: usize,
}
impl RedInfo {
    /// Basic constructor.
    pub fn new() -> Self {
        RedInfo {
            preds: 0,
            clauses_rmed: 0,
            clauses_added: 0,
            args_rmed: 0,
        }
    }
    /// Constructor from the number of predicates eliminated.
    pub fn of_preds(preds: usize) -> Self {
        let mut slf = Self::new();
        slf.preds += preds;
        slf
    }
    /// Constructor from the number of clauses removed.
    pub fn of_clauses_rmed(clauses_rmed: usize) -> Self {
        let mut slf = Self::new();
        slf.clauses_rmed += clauses_rmed;
        slf
    }
    /// Constructor from the number of clauses added.
    pub fn of_clauses_added(clauses_added: usize) -> Self {
        let mut slf = Self::new();
        slf.clauses_added += clauses_added;
        slf
    }
    /// True if one or more fields are non-zero.
    pub fn non_zero(&self) -> bool {
        self.preds > 0 || self.clauses_rmed > 0 || self.clauses_added > 0 || self.args_rmed > 0
    }

    /// True if `clause_added > clause_rmed`.
    pub fn added_clauses(&self) -> bool {
        self.clauses_added > self.clauses_rmed
    }
    /// Clauses added minus clauses removed.
    ///
    /// Zero if clauses removed greater than clauses added.
    pub fn clause_diff(&self) -> usize {
        if self.clauses_added > self.clauses_rmed {
            self.clauses_added - self.clauses_rmed
        } else {
            0
        }
    }
}
impl From<(usize, usize, usize)> for RedInfo {
    fn from((preds, clauses_rmed, clauses_added): (usize, usize, usize)) -> RedInfo {
        RedInfo {
            preds,
            clauses_rmed,
            clauses_added,
            args_rmed: 0,
        }
    }
}
impl std::ops::AddAssign for RedInfo {
    fn add_assign(
        &mut self,
        RedInfo {
            preds,
            clauses_rmed,
            clauses_added,
            args_rmed,
        }: Self,
    ) {
        self.preds += preds;
        self.clauses_rmed += clauses_rmed;
        self.clauses_added += clauses_added;
        self.args_rmed += args_rmed
    }
}
impl_fmt! {
  RedInfo(self, fmt) {
    write!(
      fmt, "\
        prd: {}, cls rm: {}, cls add: {}, args rm: {}\
      ", self.preds, self.clauses_rmed, self.clauses_added, self.args_rmed
    )
  }
}

// |===| Helper traits.

/// Provides user-friendly formatting: `pebcak_fmt`.
pub trait PebcakFmt<'a> {
    /// Info needed.
    type Info;
    /// User-friendly formatting.
    fn pebcak_io_fmt<Writer: Write>(&self, w: &mut Writer, i: Self::Info) -> IoRes<()>;
    /// Error specific to the implementor.
    fn pebcak_err(&self) -> ErrorKind;
    /// User-friendly formatting.
    fn pebcak_fmt<Writer: Write>(&self, w: &mut Writer, i: Self::Info) -> Res<()> {
        self.pebcak_io_fmt(w, i).chain_err(|| self.pebcak_err())
    }
    /// Formatted string.
    fn string_do<T, F>(&self, i: Self::Info, f: F) -> Res<T>
    where
        F: FnOnce(&str) -> T,
    {
        let mut v = vec![];
        self.pebcak_fmt(&mut v, i)?;
        std::str::from_utf8(&v)
            .chain_err(|| self.pebcak_err())
            .map(|s| f(s))
    }
    /// Formatted string.
    fn to_string_info(&self, i: Self::Info) -> Res<String> {
        self.string_do(i, |s| s.to_string())
    }
}

/// Indexed by `VarIdx`.
pub trait VarIndexed<T> {
    /// Gets the value associated with a variable.
    fn var_get(&self, var: VarIdx) -> Option<T>;
}
impl<Elem: Clone> VarIndexed<Elem> for VarMap<Elem> {
    fn var_get(&self, var: VarIdx) -> Option<Elem> {
        if var < self.len() {
            Some(self[var].clone())
        } else {
            None
        }
    }
}
impl VarIndexed<Term> for VarTerms {
    #[inline]
    fn var_get(&self, var: VarIdx) -> Option<Term> {
        if var < self.len() {
            Some(self[var].clone())
        } else {
            None
        }
    }
}
impl<Elem: Clone> VarIndexed<Elem> for VarHMap<Elem> {
    #[inline]
    fn var_get(&self, var: VarIdx) -> Option<Elem> {
        self.get(&var).cloned()
    }
}
impl VarIndexed<Term> for VarMap<(VarIdx, Typ)> {
    #[inline]
    fn var_get(&self, var: VarIdx) -> Option<Term> {
        if var < self.len() {
            Some(term::var(self[var].0, self[var].1.clone()))
        } else {
            None
        }
    }
}
impl VarIndexed<Term> for VarHMap<(VarIdx, Typ)> {
    #[inline]
    fn var_get(&self, var: VarIdx) -> Option<Term> {
        self.get(&var).map(|&(v, ref t)| term::var(v, t.clone()))
    }
}
impl VarIndexed<Term> for VarMap<crate::parse::PTTerms> {
    #[inline]
    fn var_get(&self, var: VarIdx) -> Option<Term> {
        if self.len() < *var {
            None
        } else if let Ok(res) = self[var].to_term() {
            res
        } else {
            None
        }
    }
}
impl<Elem, T, U> VarIndexed<Elem> for (T, U)
where
    T: VarIndexed<Elem>,
    U: VarIndexed<Elem>,
{
    #[inline]
    fn var_get(&self, var: VarIdx) -> Option<Elem> {
        if let Some(res) = self.0.var_get(var) {
            debug_assert!(self.1.var_get(var).is_none());
            Some(res)
        } else if let Some(res) = self.1.var_get(var) {
            debug_assert!(self.0.var_get(var).is_none());
            Some(res)
        } else {
            None
        }
    }
}
impl<'a, Elem, T> VarIndexed<Elem> for &'a T
where
    T: VarIndexed<Elem>,
{
    #[inline]
    fn var_get(&self, var: VarIdx) -> Option<Elem> {
        (*self).var_get(var)
    }
}

/// Luby series.
///
/// # Examples
///
/// ```
/// # use hoice::common::Luby ;
/// let mut luby = Luby::new() ;
/// let expected = vec![
///   1,
///   1, 2,
///   1, 2, 4,
///   1, 2, 4, 8,
///   1, 2, 4, 8, 16,
///   1, 2, 4, 8, 16, 32,
///   1, 2, 4, 8, 16, 32, 64,
///   1, 2, 4, 8, 16, 32, 64, 128,
///   1, 2, 4, 8, 16, 32, 64, 128, 256,
/// ] ;
/// for value in expected {
///   let luby = luby.next_value() ;
/// # println!("{} == {} ?", value, luby) ;
///   assert_eq! { luby, value.into() }
/// }
/// ```
#[derive(Default)]
pub struct Luby {
    /// Current max power of two.
    max_pow: usize,
    /// Current power of two, current values is `2^pow`.
    pow: usize,
}
impl Luby {
    /// Constructor.
    pub fn new() -> Self {
        Luby { max_pow: 0, pow: 0 }
    }
    /// Next value in the series.
    pub fn next_value(&mut self) -> Int {
        if self.pow > self.max_pow {
            self.pow = 0;
            self.max_pow += 1
        }
        let mut res: Int = 2.into();
        res = num::pow::pow(res, self.pow);
        self.pow += 1;
        res
    }
}

/// Counts up to the current value of the Luby series, outputs true and moves
/// on to the next value when it reaches it.
#[derive(Default)]
pub struct LubyCount {
    /// Luby series.
    luby: Luby,
    /// Current max value.
    max: Int,
    /// Counter.
    count: Int,
}
impl LubyCount {
    /// Constructor.
    pub fn new() -> Self {
        let mut luby = Luby::new();
        let max = luby.next_value();
        let count = 0.into();
        LubyCount { luby, max, count }
    }

    /// Increments the counter, returns true when it reaches the current luby
    /// value.
    pub fn inc(&mut self) -> bool {
        self.count = &self.count + 1;
        let ping = self.count >= self.max;
        if ping {
            self.max = self.luby.next_value();
            self.count = 0.into()
        }
        ping
    }
}

/// Iterator over all the combinations of some length of a collection of
/// something.
///
/// In the following, `len` is the length of the combinations we generate.
///
/// # Fields
///
/// `current` is `None` if there are no more combinations. Otherwise it stores
/// a list of pairs of length `len`, where `current[i]` stores
///
/// - the `i`th element `e` of the **next** combination ;
/// - the elements that follow `e` in the original collection, as an iterator.
///
/// `next` will be used to pass the next combination, if any, when the `next`
/// function is called.
///
/// `head` is the first element of the collection.
///
/// `tail` is the rest of the collection.
///
/// # Invariants
///
/// - `self.current.as_ref().map(|v| v.len()).unwrap_or(self.len())`
///   is equal to `self.len`
/// - `self.next.capacity() == self.len()`
/// - There's `self.len - 1` elements in `self.tail`
pub struct CombinationIter<Iter: Iterator + Clone> {
    current: Option<Vec<(Iter::Item, Iter)>>,
    len: usize,
    next: Vec<Iter::Item>,
    head: Iter::Item,
    tail: Iter,
}

impl<Iter> CombinationIter<Iter>
where
    Iter: Iterator + ExactSizeIterator + Clone,
    Iter::Item: Clone,
{
    /// Constructor.
    ///
    /// Fails if `coll.next().is_none()`, or if `len == 0`.
    pub fn new(mut coll: Iter, len: usize) -> Res<Self> {
        if len == 0 {
            bail!("trying to create all combinations of length 0, illegal")
        }
        let (head, tail) = if let Some(first) = coll.next() {
            (first, coll)
        } else {
            bail!("trying to create all combinations of an empty collection")
        };

        Ok(CombinationIter {
            current: Some(vec![(head.clone(), tail.clone()); len]),
            len,
            next: Vec::with_capacity(len),
            head,
            tail,
        })
    }

    /// Returns the next combination if any.
    pub fn next_combination(&mut self) -> Option<&Vec<Iter::Item>> {
        let mut res = None;

        if let Some(mut current) = std::mem::replace(&mut self.current, None) {
            self.next.clear();

            // Construct result, easy part.
            for (item, _) in &current {
                self.next.push(item.clone())
            }
            // Remember we have a next.
            res = Some(&self.next);

            // Tricky part.
            //
            // Remove from `current` the pairs that don't have a next element, until
            // we find one that does (starting from the end).
            'find_next: while let Some((_, mut curr)) = current.pop() {
                if let Some(next) = curr.next() {
                    // Found an element with a next.
                    current.push((next, curr));
                    // Now we restart all elements after this one (the elements we
                    // removed).
                    while current.len() < self.len {
                        current.push(
                            // Starting again from the beginning for this element.
                            (self.head.clone(), self.tail.clone()),
                        )
                    }
                    // Done, update current and break out.
                    self.current = Some(current);
                    break 'find_next;
                }
            }
        }
        res
    }
}

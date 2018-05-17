//! Base types and functions.

pub use std::io::{ Read, Write } ;
pub use std::io::Result as IoRes ;
pub use std::sync::{ Arc, RwLock } ;
pub use std::sync::mpsc::{ Receiver, Sender } ;

pub use mylib::common::hash::* ;

pub use hashconsing::HashConsign ;
pub use hashconsing::coll::* ;

pub use rsmt2::{ SmtRes, Solver } ;
pub use rsmt2::actlit::Actlit ;

pub use num::{ Zero, One, Signed } ;

pub use either::Either ;

pub use errors::* ;
pub use term ;
pub use term::{
  RTerm, Term, TTerm,
  TTermSet, TTerms,
  Val, Op, Typ, Quant,
} ;
pub use term::typ ;
pub use term::val ;
pub use term::args::{
  HTArgs, HTArgss
} ;
pub use instance::Instance ;
pub use common::consts::keywords ;

mod wrappers ;

#[macro_use]
pub mod macros ;
pub mod config ;
pub mod data ;
#[macro_use]
pub mod msg ;
pub mod consts ;
pub mod profiling ;
pub mod smt ;

pub use self::data::{ RArgs, Args, ArgsSet, ArgsMap } ;
pub use self::config::* ;
pub use self::profiling::{ Profiler, CanPrint } ;
pub use self::wrappers::* ;


lazy_static!{
  /// Configuration from clap.
  pub static ref conf: Config = Config::clap() ;
  static ref version_string: String = format!(
    "{}", crate_version!()
  ) ;
  /// Version with revision info.
  pub static ref version: & 'static str = & version_string ;
}




// |===| Helpers.

/// Stdout.
pub use ::std::io::stdout ;

/// Resets whatever flags, set-option and such need resetting.
pub fn reset() {
  conf.init() ;
  ()
}

/// Prints the stats if asked. Does nothing in bench mode.
#[cfg(feature = "bench")]
pub fn print_stats(_: & 'static str, _: Profiler) {}
/// Prints the stats if asked. Does nothing in bench mode.
#[cfg( not(feature = "bench") )]
pub fn print_stats(name: & str, profiler: Profiler) {
  if conf.stats {
    let others = profiler.drain_others() ;
    println!("") ;
    profiler.print( name, "", & [ "data" ] ) ;
    println!("") ;
    for (name, other) in others {
      print_stats(& name, other)
    }
  }
}

/// Lock corrupted error.
pub fn corrupted_err<T>(_: T) -> Error {
  "[bug] lock on learning data is corrupted...".into()
}

/// Notifies the user and reads a line from stdin.
pub fn pause(s: & str, _profiler: & Profiler) {
  let mut dummy = String::new() ;
  println!("") ;
  println!( "; {} {}...", conf.emph("press return"), s ) ;
  let _ = profile!(
    |_profiler| wrap {
      ::std::io::stdin().read_line(& mut dummy)
    } "waiting for user input"
  ) ;
}

/// Notifies the user through a message and reads a line from stdin.
pub fn pause_msg(core: & msg::MsgCore, s: & str) {
  let mut dummy = String::new() ;
  let _ = core.msg(
    format!( "; {} {}...", conf.emph("press return"), s )
  ) ;
  let _ = ::std::io::stdin().read_line(& mut dummy) ;
}

/// Identity function.
pub fn identity<T>(t: T) -> T { t }

/// Creates a directory if it doesn't exist.
pub fn mk_dir<P: AsRef<::std::path::Path>>(path: P) -> Res<()> {
  use std::fs::DirBuilder ;
  DirBuilder::new().recursive(true).create(path) ? ;
  Ok(())
}


// |===| Type and traits aliases.

/// Integers.
pub type Int = ::num::BigInt ;
/// Rationals.
pub type Rat = ::num::BigRational ;

/// A signature.
pub type Sig = VarMap<Typ> ;

/// A predicate application.
pub type PredApp = (PrdIdx, HTArgs) ;

/// Some predicate applications.
pub type PredApps = PrdHMap< HTArgss > ;
/// Predicate application alias type extension.
pub trait PredAppsExt {
  /// Insert a predicate application. Returns true if the application is new.
  fn insert_pred_app(& mut self, PrdIdx, HTArgs) -> bool ;
}
impl PredAppsExt for PredApps {
  fn insert_pred_app(& mut self, pred: PrdIdx, args: HTArgs) -> bool {
    self.entry(pred).or_insert_with(
      || HTArgss::with_capacity(4)
    ).insert(args)
  }
}

/// Predicate informations.
pub type PrdInfos = PrdMap<::instance::info::PrdInfo> ;
/// Variable informations.
pub type VarInfos = VarMap<::instance::info::VarInfo> ;

/// Maps predicates to optional terms.
pub type Candidates = PrdMap< Option<Term> > ;
unsafe impl<T: Send> Send for PrdMap<T> {}

/// Quantified variables for a top term.
pub type Quantfed = VarHMap<Typ> ;

/// Associates predicates to some quantified variables and some top terms.
pub type Model = Vec< (PrdIdx, TTerms) > ;
///
pub type ConjCandidates = PrdHMap< Vec<TTerms> > ;
///
pub type ConjModel = Vec< Vec<(PrdIdx, Vec<TTerms>)> > ;

/// Alias type for a counterexample for a clause.
pub type Cex = RArgs ;
/// Alias type for a counterexample for a sequence of clauses.
pub type Cexs = ClsHMap< Vec<Cex> > ;

/// Signature trait, for polymorphic term insertion.
pub trait Signature {
  /// Type of a variable.
  fn get(& self, VarIdx) -> Typ ;
  /// Length of the signature.
  fn len(& self) -> usize ;
}
impl Signature for VarMap<
  ::instance::info::VarInfo
> {
  fn len(& self) -> usize { VarMap::len(self) }
  fn get(& self, var: VarIdx) -> Typ {
    self[var].typ.clone()
  }
}
impl Signature for VarMap<Typ> {
  fn len(& self) -> usize { VarMap::len(self) }
  fn get(& self, var: VarIdx) -> Typ {
    self[var].clone()
  }
}


/// Implemented by types lending themselves to evaluation.
pub trait Evaluator {
  /// Retrieves the value associated with a variable.
  fn get(& self, var: VarIdx) -> & Val ;
  /// Number of variables the evaluator supports.
  fn len(& self) -> usize ;
}
impl Evaluator for VarMap<Val> {
  #[inline]
  fn get(& self, var: VarIdx) -> & Val {
    & self[var]
  }
  #[inline]
  fn len(& self) -> usize { VarMap::len(self) }
}
impl Evaluator for () {
  #[inline]
  fn get(& self, _: VarIdx) -> & Val {
    panic!("trying actual evaluation with unit")
  }
  #[inline]
  fn len(& self) -> usize { 0 }
}
/// This implements a redirection `(map, vals)`, where a variable `var` from
/// the term evaluated is evaluated to `vals[ map[var] ]`.
impl<'a, E> Evaluator for (& 'a VarMap<(VarIdx, Typ)>, & 'a E)
where E: Evaluator {
  #[inline]
  fn get(& self, var: VarIdx) -> & Val {
    self.1.get( self.0[var].0 )
  }
  #[inline]
  fn len(& self) -> usize { self.0.len() }
}


/// Something that can be evaluated to a boolean.
pub trait CanBEvaled: ::std::fmt::Display {
  /// Evaluates self.
  fn evaluate<E>(& self, & E) -> Res< Option<bool> >
  where E: Evaluator ;
}
impl CanBEvaled for Term {
  fn evaluate<E>(& self, args: & E) -> Res< Option<bool> >
  where E: Evaluator {
    self.bool_eval(args)
  }
}


/// Information returned by
/// [`RedStrat`](../instance/preproc/trait.RedStrat.html)s and
/// [`SolverRedStrat`](../instance/preproc/trait.SolverRedStrat.html)s.
#[must_use]
#[derive(Debug)]
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
      preds: 0, clauses_rmed: 0, clauses_added: 0, args_rmed: 0
    }
  }
  /// Constructor from the number of predicates eliminated.
  pub fn of_preds(preds: usize) -> Self {
    let mut slf = Self::new() ;
    slf.preds += preds ;
    slf
  }
  /// Constructor from the number of clauses removed.
  pub fn of_clauses_rmed(clauses_rmed: usize) -> Self {
    let mut slf = Self::new() ;
    slf.clauses_rmed += clauses_rmed ;
    slf
  }
  /// Constructor from the number of clauses added.
  pub fn of_clauses_added(clauses_added: usize) -> Self {
    let mut slf = Self::new() ;
    slf.clauses_added += clauses_added ;
    slf
  }
  /// True if one or more fields are non-zero.
  pub fn non_zero(& self) -> bool {
    self.preds > 0
    || self.clauses_rmed > 0
    || self.clauses_added > 0
    || self.args_rmed > 0
  }

  /// True if `clause_added > clause_rmed`.
  pub fn added_clauses(& self) -> bool {
    self.clauses_added > self.clauses_rmed
  }
  /// Clauses added minus clauses removed.
  ///
  /// Zero if clauses removed greater than clauses added.
  pub fn clause_diff(& self) -> usize {
    if self.clauses_added > self.clauses_rmed {
      self.clauses_added - self.clauses_rmed
    } else {
      0
    }
  }
}
impl From<(usize, usize, usize)> for RedInfo {
  fn from(
    (preds, clauses_rmed, clauses_added): (usize, usize, usize)
  ) -> RedInfo {
    RedInfo { preds, clauses_rmed, clauses_added, args_rmed: 0 }
  }
}
impl ::std::ops::AddAssign for RedInfo {
  fn add_assign(
    & mut self, RedInfo {
      preds, clauses_rmed, clauses_added, args_rmed
    }: Self
  ) {
    self.preds += preds ;
    self.clauses_rmed += clauses_rmed ;
    self.clauses_added += clauses_added ;
    self.args_rmed += args_rmed
  }
}
impl_fmt!{
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
  type Info ;
  /// User-friendly formatting.
  fn pebcak_io_fmt<Writer: Write>(
    & self, & mut Writer, Self::Info
  ) -> IoRes<()> ;
  /// Error specific to the implementor.
  fn pebcak_err(& self) -> ErrorKind ;
  /// User-friendly formatting.
  fn pebcak_fmt<Writer: Write>(
    & self, w: & mut Writer, i: Self::Info
  ) -> Res<()> {
    self.pebcak_io_fmt(w, i).chain_err(
      || self.pebcak_err()
    )
  }
  /// Formatted string.
  fn string_do<T, F>(& self, i: Self::Info, f: F) -> Res<T>
  where F: FnOnce(& str) -> T {
    let mut v = vec![] ;
    self.pebcak_fmt(& mut v, i) ? ;
    ::std::str::from_utf8(& v).chain_err(
      || self.pebcak_err()
    ).map(
      |s| f(s)
    )
  }
  /// Formatted string.
  fn to_string_info(& self, i: Self::Info) -> Res<String> {
    self.string_do(i, |s| s.to_string())
  }
}


/// Indexed by `VarIdx`.
pub trait VarIndexed<T> {
  /// Gets the value associated with a variable.
  #[inline(always)]
  fn var_get(& self, var: VarIdx) -> Option<T> ;
}
impl<Elem: Clone> VarIndexed<Elem> for VarMap<Elem> {
  fn var_get(& self, var: VarIdx) -> Option<Elem> {
    if var < self.len() {
      Some( self[var].clone() )
    } else {
      None
    }
  }
}
impl VarIndexed<Term> for HTArgs {
  fn var_get(& self, var: VarIdx) -> Option<Term> {
    if var < self.len() {
      Some( self[var].clone() )
    } else {
      None
    }
  }
}
impl<Elem: Clone> VarIndexed<Elem> for VarHMap<Elem> {
  fn var_get(& self, var: VarIdx) -> Option<Elem> {
    self.get(& var).map(|e| e.clone())
  }
}
impl VarIndexed<Term> for VarMap<(VarIdx, Typ)> {
  fn var_get(& self, var: VarIdx) -> Option<Term> {
    if var < self.len() {
      Some( term::var( self[var].0, self[var].1.clone() ) )
    } else {
      None
    }
  }
}
impl VarIndexed<Term> for VarHMap<(VarIdx, Typ)> {
  fn var_get(& self, var: VarIdx) -> Option<Term> {
    self.get(& var).map(
      |& (v, ref t)| term::var(v, t.clone())
    )
  }
}
impl VarIndexed<Term> for VarMap<::instance::parse::PTTerms> {
  fn var_get(& self, var: VarIdx) -> Option<Term> {
    if self.len() < * var {
      None
    } else {
      if let Ok(res) = self[var].to_term() {
        res
      } else {
        None
      }
    }
  }
}
impl<Elem, T, U> VarIndexed<Elem> for (T, U)
where T: VarIndexed<Elem>, U: VarIndexed<Elem> {
  fn var_get(& self, var: VarIdx) -> Option<Elem> {
    if let Some(res) = self.0.var_get(var) {
      debug_assert!( self.1.var_get(var).is_none() ) ;
      Some(res)
    } else if let Some(res) = self.1.var_get(var) {
      debug_assert!( self.0.var_get(var).is_none() ) ;
      Some(res)
    } else {
      None
    }
  }
}
impl<'a, Elem, T> VarIndexed<Elem> for & 'a T
where T: VarIndexed<Elem> {
  fn var_get(& self, var: VarIdx) -> Option<Elem> {
    (* self).var_get(var)
  }
}











/// Hash-related things.
///
/// What's inside this module is quite dangerous. The hashing functions are
/// type-specific and will crash if applied to something else.
mod hash {
  #![allow(non_upper_case_globals)]
  use std::hash::{ Hasher, BuildHasher } ;
  /// Number of bytes in a `u64`.
  pub const u64_bytes: usize = 8 ;

  /// Empty struct used to build `HashU64`.
  #[derive(Clone)]
  pub struct BuildHashU64 {}
  impl BuildHasher for BuildHashU64 {
    type Hasher = HashU64 ;
    fn build_hasher(& self) -> HashU64 {
      HashU64 { buf: [0 ; u64_bytes] }
    }
  }
  impl Default for BuildHashU64 {
    fn default() -> Self {
      BuildHashU64 {}
    }
  }

  /// Trivial hasher for `u64`. **This hasher is only for hashing `u64`s**.
  pub struct HashU64 {
    buf: [u8 ; u64_bytes]
  }
  impl HashU64 {
    /// Checks that a slice of bytes has the length of a `u64`. Only active
    /// in debug.
    #[cfg(debug_assertions)]
    #[inline(always)]
    fn test_bytes(bytes: & [u8]) {
      if bytes.len() != u64_bytes {
        panic!(
          "[illegal] `HashU64::hash` \
          called with non-`usize` argument ({} bytes, expected {})",
          bytes.len(), u64_bytes
        )
      }
    }
    /// Checks that a slice of bytes has the length of a `u64`. Only active
    /// in debug.
    #[cfg( not(debug_assertions) )]
    #[inline(always)]
    fn test_bytes(_: & [u8]) {}
  }
  impl Hasher for HashU64 {
    fn finish(& self) -> u64 {
      unsafe {
        ::std::mem::transmute(self.buf)
      }
    }
    fn write(& mut self, bytes: & [u8]) {
      Self::test_bytes(bytes) ;
      for n in 0..u64_bytes {
        self.buf[n] = bytes[n]
      }
    }
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
///   let luby = luby.next() ;
/// # println!("{} == {} ?", value, luby) ;
///   assert_eq! { luby, value.into() }
/// }
/// ```
pub struct Luby {
  /// Current max power of two.
  max_pow: usize,
  /// Current power of two, current values is `2^pow`.
  pow: usize
}
impl Luby {
  /// Constructor.
  pub fn new() -> Self {
    Luby { max_pow: 0, pow: 0 }
  }
  /// Next value in the series.
  pub fn next(& mut self) -> Int {
    if self.pow > self.max_pow {
      self.pow = 0 ;
      self.max_pow += 1
    }
    let mut res: Int = 2.into() ;
    res = ::num::pow::pow(res, self.pow) ;
    self.pow += 1 ;
    res
  }
}

/// Counts up to the current value of the Luby series, outputs true and moves
/// on to the next value when it reaches it.
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
    let mut luby = Luby::new() ;
    let max = luby.next() ;
    let count = 0.into() ;
    LubyCount { luby, max, count }
  }

  /// Increments the counter, returns true when it reaches the current luby
  /// value.
  pub fn inc(& mut self) -> bool {
    self.count = & self.count + 1 ;
    let ping = self.count >= self.max ;
    if ping {
      self.max = self.luby.next() ;
      self.count = 0.into()
    }
    ping
  }
}
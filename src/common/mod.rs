//! Base types and functions.

pub use std::io::{ Read, Write } ;
pub use std::io::Result as IoRes ;
pub use std::sync::{ Arc, RwLock } ;
pub use std::sync::mpsc::{ Receiver, Sender } ;

pub use mylib::common::hash::* ;

pub use hashconsing::HashConsign ;
pub use hashconsing::coll::* ;

pub use rsmt2::SmtRes ;

pub use num::{ Zero, One, Signed } ;

pub use either::Either ;

pub use errors::* ;
pub use term ;
pub use term::{ RTerm, Term, TTerm, TTerms, Val, Op, Typ } ;
pub use instance::Instance ;

mod wrappers ;
pub mod config ;

#[macro_use]
pub mod macros ;
pub mod data ;
#[macro_use]
pub mod msg ;
pub mod consts ;
pub mod profiling ;

pub use self::config::* ;
pub use self::profiling::{ Profiler, CanPrint } ;
pub use self::wrappers::* ;


lazy_static!{
  /// Configuration from clap.
  pub static ref conf: Config = Config::clap() ;
}




// |===| Helpers.

/// Lock corrupted error.
pub fn corrupted_err<T>(_: T) -> Error {
  "[bug] lock on learning data is corrupted...".into()
}

/// Notifies the user and reads a line from stdin.
pub fn pause(s: & str) {
  let mut dummy = String::new() ;
  println!("") ;
  println!( "; {}{}...", conf.emph("press return"), s ) ;
  let _ = ::std::io::stdin().read_line(& mut dummy) ;
}


// |===| Type and traits aliases.

/// Integers.
pub type Int = ::num::BigInt ;

/// A trivially hashed set of variable maps.
pub type VarMapSet<T> = HashSet< VarMap<T> > ;

/// Alias type for a map from arity to a map from terms to qualifier values.
///
/// The term to qualifier maps map the qualifier to their values. It sounds
/// stupid to do this since `QualValues` already contains the qualifier.
/// Ideally, it should be a set of values hashed by the qualifier. But we need
/// to iterate on this collection with `iter_mut` to update the values,
/// something `HashSet` does not admit as it is unsafe in general to do so.
///
/// Hence we have the qualifier twice, which is not that bad to check directly
/// if a term is a known qualifier or not.
///
/// # TODO
///
/// - investigate whether it would be possible to remove the qualifier from
///   `QualValues` entirely
pub type Quals = ArityMap<
  HConMap<Term, ::learning::ice::mining::QualValues>
> ;
/// Helpers for `Quals`.
pub trait QualsExt {
  /// Treats the `HConMap` as sets for inserting qualifiers.
  ///
  /// Returns true if the term was not there (think `is_new`).
  fn insert(& mut self, arity: Arity, term: Term) ;
}
impl QualsExt for Quals {
  fn insert(& mut self, arity: Arity, term: Term) {
    self[arity].entry( term.clone() ).or_insert_with(
      || ::learning::ice::mining::QualValues::new(term)
    ) ;
  }
}

/// A predicate application.
pub type PredApp = (PrdIdx, VarMap<Term>) ;

/// Some predicate applications.
pub type PredApps = PrdHMap< Vec<VarMap<Term>>  > ;
/// Predicate application alias type extension.
pub trait PredAppsExt {
  /// Insert a predicate application. Returns true if the application is new.
  fn insert_pred_app(& mut self, PrdIdx, VarMap<Term>) -> bool ;
}
impl PredAppsExt for PredApps {
  fn insert_pred_app(& mut self, pred: PrdIdx, args: VarMap<Term>) -> bool {
    let vec = self.entry(pred).or_insert_with(
      || Vec::with_capacity(4)
    ) ;
    for a in vec.iter() {
      if * a == args { return false }
    }
    vec.push(args) ;
    true
  }
}

/// Maps predicates to optional terms.
pub type Candidates = PrdMap< Option<Term> > ;
unsafe impl<T: Send> Send for PrdMap<T> {}

/// Qualified variables for a top term.
pub type Qualfed = VarHMap<Typ> ;

/// Associates predicates to some quantified variables and some top terms.
pub type Model = Vec< (PrdIdx, Option<Qualfed>, TTerms) > ;

/// Alias type for a counterexample for a clause.
pub type Cex = VarMap<Val> ;
/// Alias type for a counterexample for a sequence of clauses.
pub type Cexs = ClsHMap<Cex> ;

/// Mapping from variables to values, used for learning data.
pub type Args = VarMap<Val> ;

/// Alias trait for a solver with this module's parser.
pub trait Solver<'kid, P: Copy>: ::rsmt2::Solver<'kid, P> {}

impl<'kid, P, T> Solver<'kid, P> for T
where P: Copy, T: ::rsmt2::Solver<'kid, P> {}


/// Information returned by
/// [`RedStrat`](../instance/preproc/trait.RedStrat.html)s and
/// [`SolverRedStrat`](../instance/preproc/trait.SolverRedStrat.html)s.
pub struct RedInfo {
  /// Number of predicates eliminated.
  pub preds: usize,
  /// Number of clauses removed.
  pub clauses_rmed: usize,
  /// Number of clauses created.
  pub clauses_added: usize,
}
impl RedInfo {
  /// True if one or more fields are non-zero.
  pub fn non_zero(& self) -> bool {
    self.preds > 0 || self.clauses_rmed > 0 || self.clauses_added > 0
  }
}
impl From<(usize, usize, usize)> for RedInfo {
  fn from(
    (preds, clauses_rmed, clauses_added): (usize, usize, usize)
  ) -> RedInfo {
    RedInfo { preds, clauses_rmed, clauses_added }
  }
}
impl ::std::ops::AddAssign for RedInfo {
  fn add_assign(
    & mut self, RedInfo { preds, clauses_rmed, clauses_added }: Self
  ) {
    self.preds += preds ;
    self.clauses_rmed += clauses_rmed ;
    self.clauses_added += clauses_added
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
  fn var_get(& self, var: VarIdx) -> Option<& T> ;
}
impl<Elem> VarIndexed<Elem> for VarMap<Elem> {
  fn var_get(& self, var: VarIdx) -> Option<& Elem> {
    if var < self.len() {
      Some(& self[var])
    } else {
      None
    }
  }
}
impl<Elem> VarIndexed<Elem> for VarHMap<Elem> {
  fn var_get(& self, var: VarIdx) -> Option<& Elem> {
    self.get(& var)
  }
}
impl<Elem, T, U> VarIndexed<Elem> for (T, U)
where T: VarIndexed<Elem>, U: VarIndexed<Elem> {
  fn var_get(& self, var: VarIdx) -> Option<& Elem> {
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
  fn var_get(& self, var: VarIdx) -> Option<& Elem> {
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

  /// Trivial hasher for `usize`. **This hasher is only for hashing `usize`s**.
  pub struct HashU64 {
    buf: [u8 ; u64_bytes]
  }
  impl HashU64 {
    /// Checks that a slice of bytes has the length of a `usize`. Only active
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
    /// Checks that a slice of bytes has the length of a `usize`. Only active
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


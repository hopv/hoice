//! Base types and functions.

pub use std::io::{ Read, Write } ;
pub use std::io::Result as IoRes ;
pub use std::sync::{ Arc, RwLock } ;
pub use std::sync::mpsc::{ Receiver, Sender } ;

pub use mylib::common::hash::* ;
pub use mylib::safe::int::CanNew ;

pub use hashconsing::HashConsign ;

pub use rsmt2::errors::Res as SmtRes ;

pub use num::{ Zero, One, Signed } ;

pub use errors::* ;
pub use term ;
pub use term::{ RTerm, Term, TTerm, Val, Op, Typ } ;
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

/// Disjunction type.
pub enum Either<L, R> {
  Lft(L), Rgt(R)
}


// |===| Type and traits aliases.

/// Integers.
pub type Int = ::num::BigInt ;

/// Maps predicates to optional terms.
pub type Candidates = PrdMap< Option<Term> > ;
unsafe impl<T: Send> Send for PrdMap<T> {}
/// Maps predicates to terms.
pub type Model = Vec< (PrdIdx, Vec<TTerm>) > ;

/// Alias type for a counterexample for a clause.
pub type Cex = VarMap<Val> ;
/// Alias type for a counterexample for a sequence of clauses.
pub type Cexs = ClsHMap<Cex> ;

/// Mapping from variables to values, used for learning data.
pub type Args = VarMap<Val> ;

/// Alias trait for a solver with this module's parser.
pub trait Solver<'kid, P: 'static + ::rsmt2::ParseSmt2>:
  ::rsmt2::Solver<'kid, P> +
  ::rsmt2::Query<'kid, P> {}
impl<
  'kid,
  P: 'static + ::rsmt2::ParseSmt2,
  T: ::rsmt2::Solver<'kid, P> + ::rsmt2::Query<'kid, P>
> Solver<'kid, P> for T {}

/// Custom hash set with trivial hashing.
pub type HConSet<T> = HashSet<
  ::hashconsing::HConsed<T>, hash::BuildHashU64
> ;
/// Custom hash map with trivial hashing.
pub type HConMap<T,V> = HashMap<
  ::hashconsing::HConsed<T>, V, hash::BuildHashU64
> ;




// |===| Helper traits.



/// Extension for `HConSet`.
pub trait HConSetExt {
  /// Creates a new thing.
  #[inline]
  fn new() -> Self ;
  /// Creates a new thing with a capacity.
  #[inline]
  fn with_capacity(capacity: usize) -> Self ;
}

impl<T: Eq + ::std::hash::Hash> HConSetExt for HConSet<T> {
  fn new() -> Self { Self::with_hasher( hash::BuildHashU64 {} ) }
  fn with_capacity(capacity: usize) -> Self {
    Self::with_capacity_and_hasher(capacity, hash::BuildHashU64 {})
  }
}
impl<T: Eq + ::std::hash::Hash, V> HConSetExt for HConMap<T,V> {
  fn new() -> Self { Self::with_hasher( hash::BuildHashU64 {} ) }
  fn with_capacity(capacity: usize) -> Self {
    Self::with_capacity_and_hasher(capacity, hash::BuildHashU64 {})
  }
}


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


/// Basic parsing helpers.
pub mod parse {
  use common::* ;
  pub use nom::multispace ;

  named!{
    #[doc = "Comment parser."],
    pub cmt, re_bytes_find!(r#"^;.*[\n\r]*"#)
  }

  named!{
    #[doc = "Parses comments and spaces."],
    pub spc_cmt<()>, map!(
      many0!( alt_complete!(cmt | multispace) ), |_| ()
    )
  }

  named!{
    #[doc = "Integer parser."],
    pub int<Int>, map!(
      re_bytes_find!("^([1-9][0-9]*|0)"),
      |bytes| Int::parse_bytes(bytes, 10).expect(
        "[bug] problem in integer parsing"
      )
    )
  }
}

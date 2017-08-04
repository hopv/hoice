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

use ansi::{ Style, Colour } ;

pub use errors::* ;

pub mod data ;
#[macro_use]
pub mod msg ;
pub mod consts ;

lazy_static!{
  #[doc = "Configuration from clap."]
  pub static ref conf: Conf = Conf::clap() ;
}


/// Does something if not in bench mode.
#[macro_export]
#[cfg(not (feature = "bench") )]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($then)*
  ) ;
  ($($blah:tt)*) => ($($blah)*) ;
}
#[cfg(feature = "bench")]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($else)*
  ) ;
  ($($blah:tt)*) => () ;
}
/// Does something if in verbose mode.
#[macro_export]
#[cfg(not (feature = "bench") )]
macro_rules! if_verb {
  ($($blah:tt)*) => (
    if conf.verbose() {
      $($blah)*
    }
  ) ;
}
#[cfg(feature = "bench")]
macro_rules! if_verb {
  ($($blah:tt)*) => (()) ;
}



/// Logs at info level. Deactivated in release.
#[cfg( feature = "bench" )]
macro_rules! log_info {
  ($($tt:tt)*) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! log_info {
  ($($tt:tt)*) => ( info!{$($tt)*} ) ;
}


/// Logs at debug level. Deactivated in release.
#[cfg( feature = "bench" )]
macro_rules! log_debug {
  ($($tt:tt)*) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! log_debug {
  ($($tt:tt)*) => ( debug!{$($tt)*} ) ;
}


/// Does something if in debug mode.
#[macro_export]
#[cfg(not (feature = "bench") )]
macro_rules! if_debug {
  ($($blah:tt)*) => (
    if conf.debug() {
      $($blah)*
    }
  ) ;
}
#[cfg(feature = "bench")]
#[allow(unused_macros)]
macro_rules! if_debug {
  ($($blah:tt)*) => (()) ;
}


/// Disjunction type.
pub enum Either<L, R> {
  Lft(L), Rgt(R)
}



/// Lock corrupted error.
pub fn corrupted_err<T>(_: T) -> Error {
  "[bug] lock on learning data is corrupted...".into()
}


/// Integers.
pub type Int = ::num::BigInt ;




wrap_usize!{
  #[doc = "Predicate indices."]
  PrdIdx
  #[doc = "Range over predicates."]
  range: PrdRange
  #[doc = "Set of predicates."]
  set: PrdSet
  #[doc = "Hash map from predicates to something."]
  hash map: PrdHMap
  #[doc = "Total map from predicates to something."]
  map: PrdMap with iter: PrdMapIter
}


wrap_usize!{
  #[doc = "Variable indices."]
  VarIdx
  #[doc = "Range over variables."]
  range: VarRange
  #[doc = "Set of variables."]
  set: VarSet
  #[doc = "Hash map from variables to something."]
  hash map: VarHMap
  #[doc = "Total map from variables to something."]
  map: VarMap with iter: VarMapIter
}
use std::fmt ;
impl<T: fmt::Display> fmt::Display for VarMap<T> {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "(") ? ;
    for_first!{
      self.iter() => {
        |fst| write!(fmt, "{}", fst) ?,
        then |nxt| write!(fmt, ",{}", nxt)?
      }
    }
    write!(fmt, ")")
  }
}

impl ::rsmt2::Sym2Smt<()> for VarIdx {
  fn sym_to_smt2<Writer>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> where Writer: Write {
    smt_cast_io!{
      "while writing var index as symbol" =>
      write!(w, "v_{}", self)
    }
  }
}

impl ::rsmt2::Expr2Smt<()> for VarIdx {
  fn expr_to_smt2<Writer>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> where Writer: Write {
    use ::rsmt2::Sym2Smt ;
    self.sym_to_smt2(w, & ())
  }
}


wrap_usize!{
  #[doc = "Arity."]
  Arity
  #[doc = "Range over arity."]
  range: ArityRange
  #[doc = "Total map from Arity to something."]
  map: ArityMap with iter: ArityMapIter
}


wrap_usize!{
  #[doc = "Clause indices."]
  ClsIdx
  #[doc = "Range over variables."]
  range: ClsRange
  #[doc = "Set of variables."]
  set: ClsSet
  #[doc = "Hash map from variables to something."]
  hash map: ClsHMap
  #[doc = "Total map from variables to something."]
  map: ClsMap with iter: ClsMapIter
}


/// Maps predicates to terms.
pub type Candidates = PrdMap< ::instance::Term > ;
unsafe impl<T: Send> Send for PrdMap<T> {}



/// Can color things.
pub trait ColorExt {
  /// The styles in the colorizer: emph, happy, sad, and bad.
  #[inline]
  fn styles(& self) -> & Styles ;
  /// String emphasis.
  #[inline]
  fn emph<S: AsRef<str>>(& self, s: S) -> String {
    format!("{}", self.styles().emph.paint(s.as_ref()))
  }
  /// Happy string.
  #[inline]
  fn happy<S: AsRef<str>>(& self, s: S) -> String {
    format!("{}", self.styles().hap.paint(s.as_ref()))
  }
  /// Sad string.
  #[inline]
  fn sad<S: AsRef<str>>(& self, s: S) -> String {
    format!("{}", self.styles().sad.paint(s.as_ref()))
  }
  /// Bad string.
  #[inline]
  fn bad<S: AsRef<str>>(& self, s: S) -> String {
    format!("{}", self.styles().bad.paint(s.as_ref()))
  }
}




/// Contains some styles for coloring.
#[derive(Debug, Clone)]
pub struct Styles {
  /// Emphasis style.
  emph: Style,
  /// Happy style.
  hap: Style,
  /// Sad style.
  sad: Style,
  /// Bad style.
  bad: Style,
}
impl Default for Styles {
  fn default() -> Self { Styles::mk(true) }
}
impl ColorExt for Styles {
  fn styles(& self) -> & Styles { self }
}
impl Styles {
  /// Creates some styles.
  pub fn mk(colored: bool) -> Self {
    Styles {
      emph: if colored {
        Style::new().bold()
      } else { Style::new() },
      hap: if colored {
        Colour::Green.normal().bold()
      } else { Style::new() },
      sad: if colored {
        Colour::Yellow.normal().bold()
      } else { Style::new() },
      bad: if colored {
        Colour::Red.normal().bold()
      } else { Style::new() },
    }
  }
}


/// Verbose level.
#[derive(PartialEq, Eq, Debug)]
pub enum Verb {
  /// Quiet.
  Quiet,
  /// Verbose.
  Verb,
  /// Debug.
  Debug,
}
impl Verb {
  /// Default verbosity.
  pub fn default() -> Self {
    Verb::Quiet
  }
  /// Increments verbosity.
  pub fn inc(& mut self) {
    match * self {
      Verb::Quiet => * self = Verb::Verb,
      Verb::Verb => * self = Verb::Debug,
      _ => ()
    }
  }
  /// Decrements verbosity.
  pub fn dec(& mut self) {
    match * self {
      Verb::Debug => * self = Verb::Verb,
      Verb::Verb => * self = Verb::Quiet,
      _ => ()
    }
  }
  /// Log filter from verbosity.
  pub fn filter(& self) -> ::log::LogLevelFilter {
    match * self {
      Verb::Debug => ::log::LogLevelFilter::Debug,
      Verb::Verb => ::log::LogLevelFilter::Info,
      Verb::Quiet => ::log::LogLevelFilter::Error,
    }
  }

  /// True iff verbose or debug.
  pub fn verbose(& self) -> bool {
    * self != Verb::Quiet
  }
  /// True iff debug.
  pub fn debug(& self) -> bool {
    * self == Verb::Debug
  }
}


/// Basic configuration.
pub struct Conf {
  pub file: Option<String>,
  pub check: Option<String>,
  pub smt_log: bool,
  pub out_dir: String,
  pub smt_learn: bool,
  pub z3_cmd: String,
  pub step: bool,
  pub verb: Verb,
  styles: Styles,
}
impl ColorExt for Conf {
  fn styles(& self) -> & Styles { & self.styles }
}
impl Conf {
  /// Regular constructor.
  pub fn mk(
    file: Option<String>, check: Option<String>,
    smt_log: bool, z3_cmd: String, out_dir: String,
    step: bool, smt_learn: bool, 
    verb: Verb, color: bool
  ) -> Self {
    Conf {
      file, check, smt_log, out_dir, step, smt_learn, z3_cmd,
      verb, styles: Styles::mk(color)
    }
  }

  /// True iff verbose or debug.
  pub fn verbose(& self) -> bool {
    self.verb.verbose()
  }
  /// True iff debug.
  pub fn debug(& self) -> bool {
    self.verb.debug()
  }

  /// Initializes stuff.
  pub fn init(& self) -> Res<()> {
    // Are we gonna use the output directory?
    if self.smt_log {
      ::std::fs::DirBuilder::new().recursive(true).create(
        & self.out_dir
      ).chain_err(
        || format!("while creating output directory `{}`", self.out_dir)
      )
    } else {
      Ok(())
    }
  }

  /// Smt logging file.
  pub fn smt_log_file(
    & self, name: & str
  ) -> IoRes< Option<::std::fs::File> > {
    if self.smt_log {
      let mut path = ::std::path::PathBuf::from(& self.out_dir) ;
      path.push(name) ;
      path.set_extension("smt2") ;
      ::std::fs::OpenOptions::new().write(
        true
      ).truncate(true).create(true).open(& path).map(|f| Some(f))
    } else {
      Ok(None)
    }
  }

  /// Solver conf.
  pub fn solver_conf(& self) -> ::rsmt2::SolverConf {
    ::rsmt2::SolverConf::z3().cmd( self.z3_cmd.clone() )
  }


  /// CLAP constructor.
  pub fn clap() -> Self {
    use clap::{ Arg, App } ;
    use self::clap_utils::* ;

    let matches = App::new( crate_name!() ).author( crate_authors!() ).about(
      "ICE engine for systems described as Horn Clauses."
    ).arg(

      Arg::with_name("input file").help(
        "sets the input file to use"
      ).index(1)

    ).arg(

      Arg::with_name("verb").short("-v").help(
        "verbose output"
      ).takes_value(false).multiple(true)

    ).arg(

      Arg::with_name("quiet").short("-q").help(
        "quiet output"
      ).takes_value(false).multiple(true)

    ).arg(

      Arg::with_name("color").long("--color").short("-c").help(
        "(de)activates coloring"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("smt_learn").long("--smt_learn").help(
        "activates smt learning"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("step").long("--step").short("-s").help(
        "forces the teacher to wait for users to press return before sending \
        data"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("smt_log").long("--smt_log").help(
        "(de)activates smt logging to the output directory"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("z3_cmd").long("--z3").help(
        "sets the command used to call z3"
      ).default_value("z3").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("out_dir").long("--out_dir").short("-o").help(
        "sets the output directory (used only by smt logging currently)"
      ).value_name(
        "<DIR>"
      ).default_value(".").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("check").long("--check").help(
        "checks the output of a previous run (does not run inference)"
      ).value_name(
        "<FILE>"
      ).takes_value(true).number_of_values(1)

    ).get_matches() ;

    let file = matches.value_of("input file").map(|s| s.to_string()) ;
    let color = matches.value_of("color").and_then(
      |s| bool_of_str(& s)
    ).expect(
      "unreachable(color): default is provided and input validated in clap"
    ) ;
    let smt_learn = matches.value_of("smt_learn").and_then(
      |s| bool_of_str(& s)
    ).expect(
      "unreachable(smt_learn): default is provided and input validated in clap"
    ) ;
    let step = matches.value_of("step").and_then(
      |s| bool_of_str(& s)
    ).expect(
      "unreachable(step): default is provided and input validated in clap"
    ) ;
    let smt_log = matches.value_of("smt_log").and_then(
      |s| bool_of_str(& s)
    ).expect(
      "unreachable(smt_log): default is provided and input validated in clap"
    ) ;
    let z3_cmd = matches.value_of("z3_cmd").expect(
      "unreachable(out_dir): default is provided"
    ) ;
    let out_dir = matches.value_of("out_dir").expect(
      "unreachable(out_dir): default is provided"
    ) ;
    let check = matches.value_of("check").map(
      |s| s.to_string()
    ) ;

    let mut verb = Verb::default() ;

    for _ in 0..matches.occurrences_of("verb") {
      verb.inc()
    }
    for _ in 0..matches.occurrences_of("quiet") {
      verb.dec()
    }

    Conf::mk(
      file, check, smt_log, z3_cmd.into(), out_dir.into(), step, smt_learn,
      verb, color
    )
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




/// Mapping from variables to values, used for learning data.
pub type Args = VarMap<::instance::Val> ;




/// Helpers related to clap-ing.
pub mod clap_utils {
  /// Format for booleans.
  pub static bool_format: & str = "on|true|off|false" ;

  /// Boolean of a string.
  pub fn bool_of_str(s: & str) -> Option<bool> {
    match & s as & str {
      "on" | "true" => Some(true),
      "off" | "false" => Some(false),
      _ => None,
    }
  }

  /// Validates boolean input.
  pub fn bool_validator(s: String) -> Result<(), String> {
    if let Some(_) = bool_of_str(& s) {
      Ok(())
    } else {
      Err(
        format!("expected `on/true` or `off/false`, got `{}`", s)
      )
    }
  }


  /// Checks whether a directory exists.
  pub fn dir_exists(path: String) -> Result<(), String> {
    if ::std::path::Path::new(& path).is_dir() {
      Ok(())
    } else {
      Err( format!("`{}` is not a directory", path) )
    }
  }
}


/// Alias trait for a solver with this module's parser.
pub trait Solver<'kid, P: 'static + ::rsmt2::ParseSmt2>:
  ::rsmt2::Solver<'kid, P> +
  ::rsmt2::Query<'kid, P> {}
impl<
  'kid,
  P: 'static + ::rsmt2::ParseSmt2,
  T: ::rsmt2::Solver<'kid, P> + ::rsmt2::Query<'kid, P>
> Solver<'kid, P> for T {}








/// Hash-related things.
///
/// What's inside this module is quite dangerous. The hashing functions
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
    #[cfg(debug)]
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
    #[cfg( not(debug) )]
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


/// Custom hash set with trivial hashing.
pub type HConSet<T> = HashSet<
  ::hashconsing::HConsed<T>, hash::BuildHashU64
> ;
/// Custom hash map with trivial hashing.
pub type HConMap<T,V> = HashMap<
  ::hashconsing::HConsed<T>, V, hash::BuildHashU64
> ;

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
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




pub mod data ;
#[macro_use]
pub mod msg ;
pub mod consts ;


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
#[test]
fn verb() {
  let mut verb = Verb::Quiet ;
  assert!( ! verb.verbose() ) ;
  assert!( ! verb.debug() ) ;
  verb.inc() ;
  assert_eq!( verb, Verb::Verb ) ;
  assert!( verb.verbose() ) ;
  assert!( ! verb.debug() ) ;
  verb.inc() ;
  assert_eq!( verb, Verb::Debug ) ;
  assert!( verb.verbose() ) ;
  assert!( verb.debug() ) ;
  verb.dec() ;
  assert_eq!( verb, Verb::Verb ) ;
  assert!( verb.verbose() ) ;
  assert!( ! verb.debug() ) ;
  verb.dec() ;
  assert_eq!( verb, Verb::Quiet ) ;
  assert!( ! verb.verbose() ) ;
  assert!( ! verb.debug() ) ;
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
  pub fpice_synth: bool,
  pub step: bool,
  pub verb: Verb,
  pub stats: bool,
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
    step: bool, smt_learn: bool, fpice_synth: bool,
    verb: Verb, stats: bool, color: bool
  ) -> Self {
    Conf {
      file, check, smt_log, out_dir, step, smt_learn, fpice_synth, z3_cmd,
      verb, stats, styles: Styles::mk(color)
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

    // ).arg(

    //   Arg::with_name("fpice_synth").long("--fpice_synth").help(
    //     "activates fpice-style synthesis"
    //   ).validator(
    //     bool_validator
    //   ).value_name(
    //     bool_format
    //   ).default_value("on").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("stats").long("--stats").help(
        "reports some statistics at the end of the run"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

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
    let fpice_synth = true ;
    // matches.value_of("fpice_synth").and_then(
    //   |s| bool_of_str(& s)
    // ).expect(
    //   "unreachable(fpice_synth): default is provided and input validated in clap"
    // ) ;
    let stats = matches.value_of("stats").and_then(
      |s| bool_of_str(& s)
    ).expect(
      "unreachable(stats): default is provided and input validated in clap"
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
      fpice_synth, verb, stats, color
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



pub use std::time::{ Instant, Duration } ;

pub trait DurationExt {
  fn to_str(& self) -> String ;
}
impl DurationExt for Duration {
  fn to_str(& self) -> String {
    format!("{}.{:0>9}", self.as_secs(), self.subsec_nanos())
  }
}



/// Profile Tree.
#[derive(PartialEq, Eq)]
pub struct ProfileTree {
  /// Duration stored at this level.
  duration: Option<Duration>,
  /// Sub-branches.
  branches: HashMap<& 'static str, ProfileTree>,
}
impl ProfileTree {
  /// Tree with nothing but the top level.
  pub fn top(top: Duration) -> Self {
    ProfileTree {
      duration: Some(top),
      branches: HashMap::new(),
    }
  }

  /// Empty tree, not visible outside.
  fn empty() -> Self {
    ProfileTree { duration: None, branches: HashMap::new() }
  }

  /// Forces a scope to be equal to the sum of its sub branches.
  ///
  /// Only legal if the scope exists and its duration is `None`.
  pub fn lift(& mut self, scope: Vec<& 'static str>) -> Res<()> {
    let mut current = self ;
    for scp in & scope {
      let tmp = current ;
      current = (
        tmp.branches.get_mut(scp).ok_or(
          format!("trying to lift inexisting scope {:?}", scope).into()
        ) as Res<_>
      ) ?
    }
    let mut sum = Duration::from_secs(0) ;
    for (_, branch) in & current.branches {
      sum = sum + branch.duration.clone().unwrap_or( Duration::from_secs(0) )
    }
    if current.duration.is_some() {
      bail!( "trying to lift scope with existing duration {:?}", scope )
    }
    current.duration = Some(sum) ;
    Ok(())
  }

  /// Inserts something in the tree.
  pub fn insert(
    & mut self, scope: Vec<& 'static str>, duration: Duration
  ) {
    let (mut current, mut last_scope) = (self, "top") ;

    for scope in scope {
      let tmp = current ;
      current = tmp.branches.entry(scope).or_insert_with(
        || ProfileTree::empty()
      ) ;
      last_scope = scope
    }
    if current.duration.is_some() {
      panic!(
        "ProfileTree: trying to insert the same scope twice `{}`",
        conf.emph(last_scope)
      )
    }
    current.duration = Some(duration)
  }

  /// Iterator on the tree.
  ///
  /// Scopes are guaranteed to follow the topological order.
  pub fn iter<F>(& self, f: F)
  where F: Fn(& [& 'static str], & Duration, Duration) {
    if let Some(duration) = self.duration.as_ref() {
      let sub_duration = self.branches.iter().fold(
        Duration::from_secs(0),
        |acc, (_, time)| acc + time.duration.unwrap_or_else(
          || Duration::from_secs(0)
        )
      ) ;
      f(&[], duration, sub_duration)
    } else {
      panic!("ProfileTree: no top duration set but already iterating")
    }
    let mut stack: Vec< (_, Vec<_>) > = vec![
      ( vec![], self.branches.iter().map(|(s, p)| (*s, p)).collect() )
    ] ;

    while let Some( (scope, mut branches) ) = stack.pop() {
      if let Some( (s, profile) ) = branches.pop() {
        let mut this_scope = scope.clone() ;
        stack.push( (scope, branches) ) ;
        this_scope.push( s ) ;
        let sub_duration = profile.branches.iter().fold(
          Duration::from_secs(0),
          |acc, (_, time)| acc + time.duration.unwrap_or_else(
            || Duration::from_secs(0)
          )
        ) ;
        if let Some(duration) = profile.duration.as_ref() {
          f(& this_scope, duration, sub_duration)
        } else {
          let mut scope_str = "".to_string() ;
          for s in & this_scope {
            scope_str.push_str("::") ; scope_str.push_str(s)
          }
          warn!{
            "no duration for scope {}, setting to sum of branches",
            conf.emph(& scope_str)
          }
          f(& this_scope, & sub_duration, sub_duration.clone())
        }
        stack.push(
          (
            this_scope,
            profile.branches.iter().map(|(s, p)| (*s, p)).collect()
          )
        )
      }
    }
  }
}


/// Maps strings to counters.
pub type Stats = HashMap<& 'static str, usize> ;
/// Provides a debug print function.
pub trait CanPrint {
  /// Debug print (multi-line).
  fn print(& self) ;
}
impl CanPrint for Stats {
  fn print(& self) {
    for (stat, count) in self {
      let stat_len = ::std::cmp::min( 30, stat.len() ) ;
      println!(
        ";   {0: >1$}{2}: {3: >5}", "", 30 - stat_len, conf.emph(stat), count
      )
    }
  }
}
impl CanPrint for ProfileTree {
  fn print(& self) {
    self.iter(
      |scope, time, sub_time| if let Some(last) = scope.last() {
        println!(
          "; {0: >1$}|- {2}s {3}{4}", "", 2 * scope.len(), time.to_str(), last,
          if sub_time != Duration::from_secs(0) {
            format!(" ({}s)", sub_time.to_str())
          } else {
            "".into()
          }
        )
      } else {
        println!(
          "; total {}s{}", time.to_str(),
          if sub_time != Duration::from_secs(0) {
            format!(" ({}s)", sub_time.to_str())
          } else {
            "".into()
          }
        )
      }
    )
  }
}


/// Profiling macro.
///
/// If passed `self`, assumes `self` has a `_profiler` field.
#[macro_export]
#[cfg( not(feature = "bench") )]
macro_rules! profile {
  ( | $prof:ident | $stat:expr => add $e:expr ) => (
    $prof.stat_do( $stat, |val| val + $e )
  ) ;
  ( | $prof:ident | $meth:ident $( $scope:expr ),+ $(,)* ) => (
    $prof.$meth(
      vec![ $($scope),+ ]
    )
  ) ;
  ( $slf:ident $stat:expr => add $e:expr ) => ({
    let prof = & $slf._profiler ;
    profile!{ |prof| $stat => add $e }
  }) ;
  ( $slf:ident $meth:ident $( $scope:expr ),+ $(,)* ) => ({
    let prof = & $slf._profiler ;
    profile!{ |prof| $meth $($scope),+ }
  }) ;
}
#[cfg(feature = "bench")]
macro_rules! profile {
  ( $($tt:tt)* ) => (()) ;
}

/// Profiling structure, only in `not(bench)`.
///
/// Maintains statistics using a hashmap indexed by strings.
///
/// Internally, the structures are wrapped in `RefCell`s so that mutation
/// does not require `& mut self`.
#[cfg( not(feature = "bench") )]
pub struct Profile {
  /// String-indexed durations.
  map: ::std::cell::RefCell<
    HashMap< Vec<& 'static str>, (Option<Instant>, Duration)>
  >,
  /// Starting tick, for total time.
  start: Instant,
  /// Other statistics.
  stats: ::std::cell::RefCell< Stats >,
}
#[cfg(feature = "bench")]
pub struct Profile ;
impl Profile {
  /// Constructor.
  #[cfg( not(feature = "bench") )]
  pub fn mk() -> Self {
    use std::cell::RefCell ;
    Profile {
      map: RefCell::new( HashMap::new() ),
      start: Instant::now(),
      stats: RefCell::new( HashMap::new() ),
    }
  }
  #[cfg(feature = "bench")]
  pub fn mk() -> Self { Profile }

  /// Acts on a statistic.
  #[cfg( not(feature = "bench") )]
  pub fn stat_do<F>(& self, stat: & 'static str, f: F)
  where F: Fn(usize) -> usize {
    let mut map = self.stats.borrow_mut() ;
    let val = map.get(stat).map(|n| * n).unwrap_or(0) ;
    let _ = map.insert(stat, f(val)) ;
    ()
  }

  /// Ticks.
  #[cfg( not(feature = "bench") )]
  pub fn tick(& self, scope: Vec<& 'static str>) {
    if scope.is_empty() {
      panic!("Profile: can't use scope `total`")
    }
    let mut map = self.map.borrow_mut() ;
    let time = map.entry(scope).or_insert_with(
      || ( None, Duration::from_secs(0) )
    ) ;
    time.0 = Some( Instant::now() )
  }

  /// Registers the time since the last tick.
  ///
  /// Panics if there was no tick since the last time registration.
  #[cfg( not(feature = "bench") )]
  pub fn mark(& self, scope: Vec<& 'static str>) {
    if scope.is_empty() {
      panic!("Profile: can't use scope `total`")
    }
    let mut map = self.map.borrow_mut() ;
    if let Some(
      & mut (ref mut tick, ref mut sum)
    ) = map.get_mut(& scope) {
      let mut instant = None ;
      ::std::mem::swap(& mut instant, tick) ;
      if let Some(instant) = instant {
        * sum = (* sum) + Instant::now().duration_since(instant) ;
        * tick = None
      }
    } else {
      panic!("profiling: trying to mark the time without ticking first")
    }
  }

  /// Extracts the inner hash map.
  #[cfg( not(feature = "bench") )]
  pub fn extract(& self) -> HashMap< Vec<& 'static str>, Duration > {
    let mut map = HashMap::new() ;
    for (scope, & (ref tick, ref time)) in self.map.borrow().iter() {
      if tick.is_none() {
        let _ = map.insert(scope.clone(), * time) ;
      } else {
        panic!(
          "profiling: scope `{:?}` is still live but asked to extract", scope
        )
      }
    }
    let prev = map.insert(
      vec!["total"], Instant::now().duration_since(self.start)
    ) ;
    debug_assert!( prev.is_none() ) ;
    map
  }

  /// Extracts a profile tree.
  #[cfg( not(feature = "bench") )]
  pub fn extract_tree(self) -> (ProfileTree, Stats) {
    let mut tree = ProfileTree::top(
      Instant::now().duration_since(self.start)
    ) ;
    for (
      scope, & (ref should_be_none, ref time)
    ) in self.map.borrow().iter() {
      if should_be_none.is_some() {
        panic!(
          "Profile::extract_tree: still have a live instant for {:?}", scope
        )
      }
      tree.insert( scope.clone(), * time )
    }
    ( tree, self.stats.into_inner() )
  }
}








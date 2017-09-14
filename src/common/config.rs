//! Hoice's global configuration.

use std::path::PathBuf ;

use clap::Arg ;
use ansi::{ Colour, Style } ;

use errors::* ;

/// Clap `App` with static lifetimes.
pub type App = ::clap::App<'static, 'static> ;
/// Clap `ArgMatches` with static lifetime.
pub type Matches = ::clap::ArgMatches<'static> ;







/// Instance and factory configuration.
///
/// Currently, these options are static. They cannot be changed through clap.
pub struct InstanceConf {
  /// Initial capacity of the term factory.
  pub term_capa: usize,
  /// Initial capacity of the clause vector.
  pub clauses_capa: usize,
  /// Initial capacity of the predicate vector.
  pub pred_capa: usize,
}
impl InstanceConf {
  /// Adds clap options to a clap App.
  pub fn add_args(app: App) -> App { app }

  /// Creates itself from some matches.
  pub fn new(_: & Matches) -> Self {
    InstanceConf {
      term_capa: 3_000,
      clauses_capa: 42,
      pred_capa: 42,
    }
  }
}







/// Solver configuration.
pub struct SolverConf {
  /// Actual solver configuration.
  conf: ::rsmt2::SolverConf,
  /// Smt logging flag.
  pub log: bool,
}
impl SolverConf {
  /// Actual, `rsmt2` solver configuration.
  pub fn conf(& self) -> ::rsmt2::SolverConf {
    self.conf.clone()
  }

  /// Smt log file, if any.
  pub fn log_file(
    & self, name: & str
  ) -> ::common::IoRes< Option<::std::fs::File> > {
    use std::fs::OpenOptions ;
    if self.log {
      let mut path = ::common::conf.out_dir() ;
      path.push(name) ;
      path.set_extension("smt2") ;
      OpenOptions::new()
      .write(true).truncate(true).create(true)
      .open(& path).map(|f| Some(f))
    } else {
      Ok(None)
    }
  }

  /// Adds clap options to a clap App.
  pub fn add_args(app: App) -> App {
    app.arg(

      Arg::with_name("z3_cmd").long("--z3").help(
        "sets the command used to call z3"
      ).default_value("z3").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("smt_log").long("--smt_log").help(
        "(de)activates smt logging to the output directory"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let z3_cmd = matches.value_of("z3_cmd").expect(
      "unreachable(out_dir): default is provided"
    ).to_string() ;
    let conf = ::rsmt2::SolverConf::z3().cmd( z3_cmd ) ;

    let log = bool_of_matches(matches, "smt_log") ;

    SolverConf { conf, log }
  }
}







/// Pre-processing configuration.
pub struct PreprocConf {
  /// Pre-processing flag.
  pub active: bool,
  /// Simple reduction flag.
  pub simple_red: bool,
}
impl PreprocConf {
  /// Adds clap options to a clap App.
  pub fn add_args(app: App) -> App {
    app.arg(

      Arg::with_name("pre_proc").long("--pre_proc").help(
        "(de)activates pre-processing"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("simple_red").long("--simple_red").help(
        "(de)activates simple reduction"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let active = bool_of_matches(matches, "pre_proc") ;
    let simple_red = bool_of_matches(matches, "simple_red") ;

    PreprocConf { active, simple_red }
  }
}







/// Ice learner configuration.
pub struct IceConf {
  /// Fpice-style synthesis.
  pub fpice_synth: bool,
  /// Number of threads used for computing qualifier's gain.
  pub gain_threads: usize,
  /// Qualifier decay flag.
  pub decay: bool,
  /// Maximum decay above which qualifiers are dropped.
  pub max_decay: usize,
}
impl IceConf {
  /// Adds clap options to a clap App.
  pub fn add_args(app: App) -> App {
    app.arg(

      Arg::with_name("gain_threads").long("--gain_threads").help(
        "sets the number of threads to use when computing qualifier gains, \
        0 for auto"
      ).validator(
        int_validator
      ).value_name(
        "INT"
      ).default_value("1").takes_value(true).number_of_values(1)

    // ).arg(

    //   Arg::with_name("fpice_synth").long("--fpice_synth").help(
    //     "(de)activates fpice-style synthesis"
    //   ).validator(
    //     bool_validator
    //   ).value_name(
    //     bool_format
    //   ).default_value("on").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("decay").long("--decay").short("-d").help(
        "(de)activates qualifier decay (forgetting unused qualifiers)"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("max_decay").long("--max_decay").help(
        "maximum decay above which qualifiers are dropped"
      ).validator(
        int_validator
      ).value_name(
        "INT"
      ).default_value("50").takes_value(true).number_of_values(1)

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let fpice_synth = true ;
    // let fpice_synth = bool_of_matches(matches, "fpice_synth") ;

    let gain_threads = int_of_matches(matches, "gain_threads") ;

    let decay = matches.value_of("decay").and_then(
      |s| bool_of_str(& s)
    ).expect(
      "unreachable(decay): default is provided and input validated in clap"
    ) ;

    let max_decay = int_of_matches(matches, "max_decay") ;

    IceConf { fpice_synth, gain_threads, decay, max_decay }
  }
}






/// Teacher configuration.
pub struct TeacherConf {
  /// Stop before sending data to learner(s).
  pub step: bool,
}
impl TeacherConf {
  /// Adds clap options to a clap App.
  pub fn add_args(app: App) -> App {
    app.arg(

      Arg::with_name("step").long("--step").short("-s").help(
        "forces the teacher to progress incrementally"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let step = bool_of_matches(matches, "step") ;

    TeacherConf { step }
  }
}





/// Global configuration.
pub struct Config {
  file: Option<String>,
  /// Verbosity.
  pub verb: Verb,
  /// Statistics flag.
  pub stats: bool,
  /// Output directory.
  out_dir: String,
  /// Styles, for coloring.
  styles: Styles,

  /// Result check file.
  check: Option<String>,
  /// Eldarica result checking flag.
  pub check_eld: bool,

  /// Instance and factory configuration.
  pub instance: InstanceConf,
  /// Pre-processing configuration.
  pub preproc: PreprocConf,
  /// Solver configuration.
  pub solver: SolverConf,
  /// Ice configuration.
  pub ice: IceConf,
  /// Teacher configuration.
  pub teacher: TeacherConf,
}
impl ColorExt for Config {
  fn styles(& self) -> & Styles { & self.styles }
}
impl Config {
  /// Output directory as a `PathBuf`.
  pub fn out_dir(& self) -> PathBuf {
    PathBuf::from(& self.out_dir)
  }
  /// True iff verbose or debug.
  pub fn verbose(& self) -> bool {
    self.verb.verbose()
  }
  /// True iff debug.
  pub fn debug(& self) -> bool {
    self.verb.debug()
  }
  /// Input file.
  pub fn in_file(& self) -> Option<& String> {
    self.file.as_ref()
  }
  /// Result to check file.
  pub fn check_file(& self) -> Option<& String> {
    self.check.as_ref()
  }

  /// Parses command-line arguments and generates the configuration.
  pub fn clap() -> Self {
    let mut app = App::new( crate_name!() ) ;
    app = Self::add_args(app) ;
    app = Self::add_check_args(app) ;
    app = InstanceConf::add_args(app) ;
    app = PreprocConf::add_args(app) ;
    app = SolverConf::add_args(app) ;
    app = IceConf::add_args(app) ;
    app = TeacherConf::add_args(app) ;

    let matches = app.get_matches() ;

    /// Input file.
    let file = matches.value_of("input file").map(|s| s.to_string()) ;

    // Verbosity
    let mut verb = Verb::default() ;
    for _ in 0..matches.occurrences_of("verb") {
      verb.inc()
    }
    for _ in 0..matches.occurrences_of("quiet") {
      verb.dec()
    }

    // Colors.
    let color = bool_of_matches(& matches, "color") ;
    let styles = Styles::mk(color) ;

    // Output directory.
    let out_dir = matches.value_of("out_dir").expect(
      "unreachable(out_dir): default is provided"
    ).to_string() ;

    // Profiling.
    let stats = bool_of_matches(& matches, "stats") ;

    // Result checking.
    let check = matches.value_of("check").map(
      |s| s.to_string()
    ) ;
    let check_eld = matches.value_of("check_eld").and_then(
      |s| bool_of_str(& s)
    ).expect(
      "unreachable(check_eld): default is provided and input validated in clap"
    ) ;

    let instance = InstanceConf::new(& matches) ;
    let preproc = PreprocConf::new(& matches) ;
    let solver = SolverConf::new(& matches) ;
    let ice = IceConf::new(& matches) ;
    let teacher = TeacherConf::new(& matches) ;

    Config {
      file, verb, stats, out_dir, styles,
      check, check_eld,
      instance, preproc, solver, ice, teacher
    }
  }

  /// Adds clap options to a clap App.
  pub fn add_args(app: App) -> App {
    app.author( crate_authors!() ).about(
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

      Arg::with_name("out_dir").long("--out_dir").short("-o").help(
        "sets the output directory (used only by smt logging currently)"
      ).value_name(
        "DIR"
      ).default_value(".").takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("stats").long("--stats").help(
        "reports some statistics at the end of the run"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    )
  }

  /// Add args related to result checking.
  pub fn add_check_args(app: App) -> App {
    app.arg(

      Arg::with_name("check").long("--check").help(
        "checks the output of a previous run (does not run inference)"
      ).value_name(
        "FILE"
      ).takes_value(true).number_of_values(1)

    ).arg(

      Arg::with_name("check_eld").long("--check_eld").help(
        "if `check` is active, expect eldarica-style result"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).number_of_values(1)

    )
  }

  /// Initializes stuff.
  pub fn init(& self) -> Res<()> {
    // Setup the rayon thread pool.
    if self.ice.gain_threads > 1 {
      use rayon::{ Configuration, initialize } ;
      initialize(
        Configuration::new().num_threads(
          self.ice.gain_threads
        ).thread_name(
          |i| format!("hoice_gain_{}", i)
        )
      ).map_err(
        |e| Error::from_kind(
          ErrorKind::Msg( format!("{}", e) )
        )
      ).chain_err(
        || "during rayon initialization"
      ) ?
    }
    // Are we gonna use the output directory?
    if self.solver.log {
      ::std::fs::DirBuilder::new().recursive(true).create(
        & self.out_dir
      ).chain_err(
        || format!("while creating output directory `{}`", self.out_dir)
      )
    } else {
      Ok(())
    }
  }
}











#[doc = r#"Verbose level.

```
# use hoice_lib::common::Verb ;
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
```
"#]
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

/// Boolean of some matches.
///
/// Assumes a default is provided and the input has been validated with
/// `bool_validator`.
pub fn bool_of_matches(matches: & Matches, key: & str) -> bool {
  matches.value_of(key).and_then(
    |s| bool_of_str(& s)
  ).expect(
    "failed to retrieve boolean argument"
  )
}

/// Integer of some matches.
///
/// Assumes a default is provided and the input has been validated with
/// `bool_validator`.
pub fn int_of_matches(matches: & Matches, key: & str) -> usize {
  use std::str::FromStr ;
  matches.value_of(key).map(
    |s| usize::from_str(& s)
  ).expect(
    "failed to retrieve integer argument"
  ).expect(
    "failed to retrieve integer argument"
  )
}

/// Validates integer input.
pub fn int_validator(s: String) -> Result<(), String> {
  use std::str::FromStr ;
  match usize::from_str(& s) {
    Ok(_) => Ok(()),
    Err(_) => Err(
      format!("expected an integer, got `{}`", s)
    ),
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
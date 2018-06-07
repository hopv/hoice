//! Hoice's global configuration.

use std::path::PathBuf ;

use rsmt2::SmtConf as SolverConf ;

use clap::Arg ;
use ansi::{ Colour, Style } ;

use errors::* ;
use common::mk_dir ;
use instance::Instance ;

/// Clap `App` with static lifetimes.
pub type App = ::clap::App<'static, 'static> ;
/// Clap `ArgMatches` with static lifetime.
pub type Matches = ::clap::ArgMatches<'static> ;




/// Functions all sub-configurations must have.
pub trait SubConf {
  /// True if the options of the subconf need the output directory.
  fn need_out_dir(& self) -> bool ;
}




/// Instance and factory configuration.
///
/// Currently, these options are static. They cannot be changed through clap.
pub struct InstanceConf {
  /// Initial capacity of the term factory.
  pub term_capa: usize,
  /// Initial capacity of the clause vector.
  pub clause_capa: usize,
  /// Initial capacity of the predicate vector.
  pub pred_capa: usize,
}
impl SubConf for InstanceConf {
  fn need_out_dir(& self) -> bool { false }
}
impl InstanceConf {
  /// Adds clap options to a clap App.
  pub fn add_args(app: App, _: usize) -> App {
    app
  }

  /// Creates itself from some matches.
  pub fn new(_: & Matches) -> Self {
    InstanceConf {
      term_capa: 3_000,
      clause_capa: 42,
      pred_capa: 42,
    }
  }
}







/// Solver configuration.
pub struct SmtConf {
  /// Actual solver configuration.
  conf: SolverConf,
  /// Smt logging flag.
  pub log: bool,
}
impl SubConf for SmtConf {
  fn need_out_dir(& self) -> bool { self.log }
}
impl SmtConf {
  /// Actual, `rsmt2` solver configuration.
  pub fn conf(& self) -> SolverConf {
    self.conf.clone()
  }

  /// Spawns a solver.
  ///
  /// If logging is active, will log to `<name>.smt2`.
  pub fn spawn<Parser, I>(
    & self, name: & 'static str, parser: Parser, instance: I
  ) -> Res< ::rsmt2::Solver<Parser> >
  where I: AsRef<Instance> {
    let mut solver = ::rsmt2::Solver::new(self.conf(), parser) ? ;
    if let Some(log) = self.log_file(name, instance.as_ref()).chain_err(
      || format!(
        "While opening log file for {}", ::common::conf.emph(name)
      )
    ) ? {
      solver.tee(log) ?
    }
    Ok(solver)
  }

  /// Smt log dir, if any.
  fn log_dir(& self, instance: & Instance) -> Res< Option<PathBuf> > {
    if self.log {
      let mut path = ::common::conf.out_dir(instance) ;
      path.push("solvers") ;
      mk_dir(& path) ? ;
      Ok(Some(path))
    } else {
      Ok(None)
    }
  }

  /// Smt log file, if any.
  fn log_file<S: AsRef<str >>(
    & self, name: S, instance: & Instance
  ) -> Res< Option<::std::fs::File> > {
    use std::fs::OpenOptions ;
    if let Some(mut path) = self.log_dir(instance) ? {
      path.push(name.as_ref()) ;
      path.set_extension("smt2") ;
      let file = OpenOptions::new().write(true).truncate(true).create(
        true
      ).open(& path).chain_err(
        || format!("while creating smt log file {}", path.to_string_lossy())
      ) ? ;
      Ok( Some(file) )
    } else {
      Ok(None)
    }
  }

  /// Adds clap options to a clap `App`.
  pub fn add_args(app: App, mut order: usize) -> App {
    let mut order = || {
      order += 1 ;
      order
    } ;

    app.arg(

      Arg::with_name("z3_cmd").long("--z3").help(
        "sets the command used to call z3"
      ).default_value(
        "z3"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("smt_log").long("--smt_log").help(
        "(de)activates smt logging to the output directory"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).display_order( order() )

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let z3_cmd = matches.value_of("z3_cmd").expect(
      "unreachable(out_dir): default is provided"
    ).to_string() ;
    let mut conf = SolverConf::z3() ;
    conf.cmd( z3_cmd ) ;
    conf.models() ;

    let log = bool_of_matches(matches, "smt_log") ;

    SmtConf { conf, log }
  }
}







/// Pre-processing configuration.
pub struct PreprocConf {
  /// (De)activates the whole preprocessing.
  pub active: bool,

  /// Dump all steps of the preprocessing as smt2 systems.
  pub dump: bool,
  /// Dump predicate dependency graphs.
  ///
  /// The predicate dependency graphs are constructed by [`CfgRed`][cfg red].
  /// For each of its runs, it will log the dependencies before and after
  /// reduction.
  ///
  /// [cfg red]: ../../instance/preproc/struct.CfgRed.html
  /// (CfgRed reduction strategy)
  pub dump_pred_dep: bool,

  /// Horn reduction flag.
  ///
  /// (De)activates [`SimpleOneLhs`][slhs], [`SimpleOneRhs`][srhs],
  /// [`OneLhs`][lhs], and [`OneRhs`][rhs]. If true, then these strategies are
  /// controlled separately by the flags below.
  ///
  /// [slhs]: ../../instance/preproc/struct.SimpleOneLhs.html
  /// (SimpleOneLhs reduction strategy)
  /// [srhs]: ../../instance/preproc/struct.SimpleOneRhs.html
  /// (SimpleOneRhs reduction strategy)
  /// [lhs]: ../../instance/preproc/struct.OneLhs.html
  /// (OneLhs reduction strategy)
  /// [rhs]: ../../instance/preproc/struct.OneRhs.html
  /// (OneRhs reduction strategy)
  pub reduction: bool,

  /// Allows right-hand side Horn reduction.
  ///
  /// Deactivates [`OneRhs`][rhs] and [`SimpleOneRhs`][srhs] if false.
  ///
  /// [rhs]: ../../instance/preproc/struct.OneRhs.html
  /// (OneRhs reduction strategy)
  /// [srhs]: ../../instance/preproc/struct.SimpleOneRhs.html
  /// (SimpleOneRhs reduction strategy)
  pub one_rhs: bool,
  /// Allows full right-hand side Horn reduction.
  ///
  /// Deactivates [`OneRhs`][rhs] if false.
  ///
  /// [rhs]: ../../instance/preproc/struct.OneRhs.html
  /// (OneRhs reduction strategy)
  pub one_rhs_full: bool,
  /// Allows left-hand side Horn reduction.
  ///
  /// Deactivates [`OneLhs`][lhs] and [`SimpleOneLhs`][slhs] if false.
  ///
  /// [lhs]: ../../instance/preproc/struct.OneLhs.html
  /// (OneLhs reduction strategy)
  /// [slhs]: ../../instance/preproc/struct.SimpleOneLhs.html
  /// (SimpleOneLhs reduction strategy)
  pub one_lhs: bool,
  /// Allows full left-hand side Horn reduction.
  ///
  /// Deactivates [`OneLhs`][lhs] if false.
  ///
  /// [lhs]: ../../instance/preproc/struct.OneLhs.html
  /// (OneLhs reduction strategy)
  pub one_lhs_full: bool,

  /// Allows cfg reduction.
  ///
  /// (De)activates [`CfgRed`][cfg red].
  ///
  /// [cfg red]: ../../instance/preproc/struct.CfgRed.html
  /// (CfgRed reduction strategy)
  pub cfg_red: bool,

  /// Allows argument reduction.
  ///
  /// (De)activates [`ArgRed`][arg red].
  ///
  /// [arg red]: ../../instance/preproc/struct.ArgRed.html
  /// (ArgRed reduction strategy)
  pub arg_red: bool,

  /// Reverse unrolling.
  pub runroll: bool,

  /// Allows positive clever unrolling.
  ///
  /// (De)activates [`BiasedUnroll`][unroll] (positive version).
  ///
  /// [unroll]: ../../instance/preproc/struct.BiasedUnroll.html
  /// (BiasedUnroll strategy)
  pub pos_unroll: bool,

  /// Allows negative clever unrolling.
  ///
  /// (De)activates [`BiasedUnroll`][unroll] (negative version).
  ///
  /// [unroll]: ../../instance/preproc/struct.BiasedUnroll.html
  /// (BiasedUnroll strategy)
  pub neg_unroll: bool,

  /// Allows clause term pruning.
  ///
  /// This is part of the [`Simplify`][simpl] strategy as well as the
  /// simplification that run on the clauses modified by all reduction
  /// strategies. This can be expensive as it relies on SMT queries for
  /// pruning.
  ///
  /// [simpl]: ../../instance/preproc/struct.Simplify.html
  /// (Simplify reduction strategy)
  pub prune_terms: bool,

  /// Allows strengthening when splitting.
  pub split_strengthen: bool,

  /// Allows clause sorting when splitting.
  pub split_sort: bool,
}
impl SubConf for PreprocConf {
  fn need_out_dir(& self) -> bool {
    self.dump && self.active || self.dump_pred_dep
  }
}
impl PreprocConf {
  /// Instance dump dir.
  fn log_dir<Path>(& self, sub: Path, instance: & Instance) -> Res<PathBuf>
  where Path: AsRef<::std::path::Path> {
    let mut path = ::common::conf.out_dir(instance) ;
    path.push("preproc") ;
    path.push(sub) ;
    mk_dir(& path) ? ;
    Ok(path)
  }

  /// Instance dump file.
  pub fn instance_log_file<S: AsRef<str>>(
    & self, name: S, instance: & Instance
  ) -> Res< Option<::std::fs::File> > {
    use std::fs::OpenOptions ;
    if self.dump && self.active {
      let mut path = self.log_dir("instances", instance) ? ;
      path.push(name.as_ref()) ;
      path.set_extension("smt2") ;
      let file = OpenOptions::new().write(true).truncate(true).create(
        true
      ).open(& path).chain_err(
        || format!(
          "while creating instance dump file {}", path.to_string_lossy()
        )
      ) ? ;
      Ok(Some(file))
    } else {
      Ok(None)
    }
  }

  /// Predicate dependency file.
  pub fn pred_dep_file<S: AsRef<str>>(
    & self, name: S, instance: & Instance
  ) -> Res<
    Option< (::std::fs::File, ::std::path::PathBuf) >
  > {
    use std::fs::OpenOptions ;
    if self.dump_pred_dep {
      let mut path = self.log_dir("pred_dep", instance) ? ;
      path.push(name.as_ref()) ;
      path.set_extension("gv") ;
      let file = OpenOptions::new().write(true).truncate(true).create(
        true
      ).open(& path).chain_err(
        || format!(
          "while creating predicade dependency graph file {}",
          path.to_string_lossy()
        )
      ) ? ;
      Ok(Some((file, path)))
    } else {
      Ok(None)
    }
  }

  /// Adds clap options to a clap `App`.
  pub fn add_args(app: App, mut order: usize) -> App {
    let mut order = || {
      order += 1 ;
      order
    } ;

    app.arg(

      Arg::with_name("preproc").long("--preproc").help(
        "(de)activates pre-processing"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("dump_preproc").long("--dump_preproc").help(
        "(de)activates instance dumping during preprocessing"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("prune_terms").long("--prune_terms").help(
        "(de)activates clause term pruning when simplifying clauses"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).hidden(
        true
      ).display_order( order() )

    ).arg(

      Arg::with_name("reduction").long("--reduction").help(
        "(de)activates all Horn reduction"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("one_rhs").long("--one_rhs").help(
        "(de)activates one rhs reduction"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("one_rhs_full").long("--one_rhs_full").help(
        "(de)activates full one rhs reduction (might introduce quantifiers)"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("one_lhs").long("--one_lhs").help(
        "(de)activates reduction of predicate \
        appearing in exactly one clause lhs"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("one_lhs_full").long("--one_lhs_full").help(
        "(de)activates full one lhs reduction (might introduce quantifiers)"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("arg_red").long("--arg_red").help(
        "(de)activates argument reduction"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("cfg_red").long("--cfg_red").help(
        "(de)activates control flow graph reduction"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("dump_pred_dep").long("--dump_pred_dep").help(
        "(de)activates predicate dependency dumps (cfg_red)"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("runroll").long("--runroll").help(
        "(de)activates reverse unrolling"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("pos_unroll").long("--pos_unroll").help(
        "(de)activates positive unrolling"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("neg_unroll").long("--neg_unroll").help(
        "(de)activates negative unrolling"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(true).hidden(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("split_strengthen").long("--split_strengthen").help(
        "(de)activates strengthening when splitting is active"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("split_sort").long("--split_sort").help(
        "(de)activates clause sorting when splitting is active"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(
        true
      ).number_of_values(1).display_order( order() )

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let active = bool_of_matches(matches, "preproc") ;
    let reduction = bool_of_matches(matches, "reduction") ;
    let arg_red = bool_of_matches(matches, "arg_red") ;
    let one_rhs = bool_of_matches(matches, "one_rhs") ;
    let one_rhs_full = bool_of_matches(matches, "one_rhs_full") ;
    let one_lhs = bool_of_matches(matches, "one_lhs") ;
    let one_lhs_full = bool_of_matches(matches, "one_lhs_full") ;
    let cfg_red = bool_of_matches(matches, "cfg_red") ;
    let dump = bool_of_matches(matches, "dump_preproc") ;
    let dump_pred_dep = bool_of_matches(matches, "dump_pred_dep") ;
    let prune_terms = bool_of_matches(matches, "prune_terms") ;
    let runroll = bool_of_matches(matches, "runroll") ;
    let pos_unroll = bool_of_matches(matches, "pos_unroll") ;
    let neg_unroll = bool_of_matches(matches, "neg_unroll") ;
    let split_strengthen = bool_of_matches(matches, "split_strengthen") ;
    let split_sort = bool_of_matches(matches, "split_sort") ;

    PreprocConf {
      dump, dump_pred_dep, active,
      reduction, one_rhs, one_rhs_full, one_lhs, one_lhs_full, cfg_red,
      arg_red, prune_terms, runroll, pos_unroll, neg_unroll,
      split_strengthen, split_sort
    }
  }
}







/// Ice learner configuration.
pub struct IceConf {
  /// Ignore unclassified data when computing entropy.
  pub simple_gain_ratio: f64,
  /// Sort predicates.
  pub sort_preds: f64,
  /// Randomize qualifiers.
  pub rand_quals: bool,
  /// Generate complete transformations for qualifiers.
  pub complete: bool,
  /// Biases qualifier selection based on the predicates the qualifier was
  /// created for.
  pub qual_bias: bool,
  /// Activates qualifier printing.
  pub qual_print: bool,
  /// Gain above which a qualifier is considered acceptable for splitting data.
  pub gain_pivot: f64,
  ///
  pub gain_pivot_inc: f64,
  ///
  pub gain_pivot_mod: usize,
  /// Same as `gain_pivot` but for qualifier synthesis.
  pub gain_pivot_synth: Option<f64>,
  /// Run a learner that does not mine the instance.
  pub pure_synth: bool,
  /// Mine conjunction of terms.
  pub mine_conjs: bool,
  /// Add synthesized qualifiers.
  pub add_synth: bool,
  /// Lockstep for qualifiers.
  pub qual_step: bool,
  /// Lockstep for synthesized qualifiers only.
  pub qual_synth_step: bool,
}
impl SubConf for IceConf {
  fn need_out_dir(& self) -> bool { false }
}
impl IceConf {
  /// Adds clap options to a clap App.
  pub fn add_args(app: App, mut order: usize) -> App {
    let mut order = || {
      order += 1 ;
      order
    } ;

    app.arg(

      Arg::with_name("simple_gain_ratio").long("--simple_gain_ratio").help(
        "percent of times simple gain will be used"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value(
        "20"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("sort_preds").long("--sort_preds").help(
        "predicate sorting before learning probability"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value(
        "40"
      ).takes_value(true).number_of_values(1).display_order(
        order()
      ).hidden(true)

    ).arg(

      Arg::with_name("rand_quals").long("--rand_quals").help(
        "randomize the qualifiers before gain computation"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "on"
      ).takes_value(true).number_of_values(1).display_order(
        order()
      ).hidden(true)

    ).arg(

      Arg::with_name("complete").long("--qual_complete").help(
        "generate complete transformations for qualifiers"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("no").takes_value(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("qual_bias").long("--qual_bias").help(
        "predicate-based bias for qualifier section"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("qual_print").long("--qual_print").help(
        "(de)activates qualifier printing"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("no").takes_value(
        true
      ).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("gain_pivot").long("--gain_pivot").help(
        "first qualifier with a gain higher than this value will be used\n\
        (between 0 and 100)"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value("5").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("gain_pivot_synth").long("--gain_pivot_synth").help(
        "same as `--gain_pivot` but for qualifier synthesis \
        (inactive if > 100)"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value("1").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("gain_pivot_inc").long("--gain_pivot_inc").help(
        "undocumented"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value("0").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("gain_pivot_mod").long("--gain_pivot_mod").help(
        "undocumented"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value("100000").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("pure_synth").long("--pure_synth").help(
        "if true, runs another pure-synthesis learner"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("no").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("add_synth").long("--add_synth").help(
        "add synthesized qualifiers as normal qualifiers"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("mine_conjs").long("--mine_conjs").help(
        "mine conjunctions of atoms from clauses"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("on").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("qual_step").long("--qual_step").help(
        "lockstep qualifier selection"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    ).arg(

      Arg::with_name("qual_synth_step").long("--qual_synth_step").help(
        "lockstep qualifier selection (synthesis only)"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value("off").takes_value(
        true
      ).number_of_values(1).hidden(true).display_order( order() )

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let simple_gain_ratio = {
      let mut value = int_of_matches(
        matches, "simple_gain_ratio"
      ) as f64 / 100.0 ;
      if value < 0.0 {
        0.0
      } else if 1.0 < value {
        1.0
      } else {
        value
      }
    } ;
    let sort_preds = {
      let mut value = int_of_matches(
        matches, "sort_preds"
      ) as f64 / 100. ;
      if value < 0.0 {
        0.0
      } else if 1.0 < value {
        1.0
      } else {
        value
      }
    } ;

    let rand_quals = bool_of_matches(matches, "rand_quals") ;

    let complete = bool_of_matches(matches, "complete") ;
    let qual_bias = bool_of_matches(matches, "qual_bias") ;
    let qual_print = bool_of_matches(matches, "qual_print") ;
    let gain_pivot = {
      let mut value = int_of_matches(
        matches, "gain_pivot"
      ) as f64 / 100.0 ;
      if value < 0.0 {
        0.0
      } else if 1.0 < value {
        1.0
      } else {
        value
      }
    } ;
    let gain_pivot_inc = {
      let mut value = int_of_matches(
        matches, "gain_pivot_inc"
      ) as f64 / 100.0 ;
      if value < 0.0 {
        0.0
      } else if 1.0 < value {
        1.0
      } else {
        value
      }
    } ;
    let gain_pivot_synth = {
      let mut value = int_of_matches(
        matches, "gain_pivot_synth"
      ) as f64 / 100.0 ;
      if value < 0.0 {
        Some(0.0)
      } else if 1.0 < value {
        None
      } else {
        Some(value)
      }
    } ;
    let gain_pivot_mod = int_of_matches(matches, "gain_pivot_mod") ;
    let add_synth = bool_of_matches(matches, "add_synth") ;
    let pure_synth = bool_of_matches(matches, "pure_synth") ;
    let mine_conjs = bool_of_matches(matches, "mine_conjs") ;
    let qual_step = bool_of_matches(matches, "qual_step") ;
    let qual_synth_step = bool_of_matches(matches, "qual_synth_step") ;

    IceConf {
      simple_gain_ratio, sort_preds, rand_quals, complete,
      qual_bias, qual_print,
      gain_pivot, gain_pivot_inc, gain_pivot_mod, gain_pivot_synth,
      pure_synth, mine_conjs, add_synth, qual_step, qual_synth_step
    }
  }
}






/// Teacher configuration.
pub struct TeacherConf {
  /// Stop before sending data to learner(s).
  pub step: bool,
  /// Run the assistant to break implication constraints.
  pub assistant: bool,
  /// Try to find implication constraints related to existing samples first.
  pub bias_cexs: bool,
  /// Maximize bias: remove all constraints when there are pos/neg cexs.
  pub max_bias: bool,
  /// Allow partial samples.
  pub partial: bool,
}
impl SubConf for TeacherConf {
  fn need_out_dir(& self) -> bool { false }
}
impl TeacherConf {
  /// Adds clap options to a clap App.
  pub fn add_args(app: App, mut order: usize) -> App {
    let mut order = || {
      order += 1 ;
      order
    } ;

    app.arg(

      Arg::with_name("teach_step").long("--teach_step").help(
        "forces the teacher to progress incrementally"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("assistant").long("--assistant").help(
        "(de)activate breaking implication constraints"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "on"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("bias_cexs").long("--bias_cexs").help(
        "(de)activate biased implication constraints"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "on"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("max_bias").long("--max_bias").help(
        "(de)activate constraint pruning when there's at least one \
        pos/neg sample"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "off"
      ).takes_value(true).number_of_values(1).display_order(
        order()
      ).hidden(true)

    ).arg(

      Arg::with_name("partial").long("--partial").help(
        "(de)activate partial samples"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "on"
      ).takes_value(true).number_of_values(1).display_order( order() )

    )
  }

  /// Creates itself from some matches.
  pub fn new(matches: & Matches) -> Self {
    let step = bool_of_matches(matches, "teach_step") ;
    let assistant = bool_of_matches(matches, "assistant") ;
    let bias_cexs = bool_of_matches(matches, "bias_cexs") ;
    let max_bias = bool_of_matches(matches, "max_bias") ;
    let partial = bool_of_matches(matches, "partial") ;

    TeacherConf {
      step, assistant, bias_cexs, max_bias, partial
    }
  }
}



use std::time::{ Instant, Duration } ;


/// Global configuration.
pub struct Config {
  file: Option<String>,
  /// Verbosity.
  pub verb: usize,
  /// Statistics flag.
  pub stats: bool,
  /// Inference flag.
  pub infer: bool,
  /// Reason on each negative clause separately.
  pub split: bool,
  /// Pause between negative clauses when in split mode.
  pub split_step: bool,
  /// Instant at which we'll timeout.
  timeout: Option<Instant>,
  /// Output directory.
  out_dir: String,
  /// Styles, for coloring.
  styles: Styles,

  /// Result check file.
  check: Option<String>,
  /// Eldarica result checking flag.
  pub check_eld: bool,
  /// If true, SMT-check all simplifications.
  pub check_simpl: bool,
  /// Level of term simplification.
  pub term_simpl: usize,

  /// Instance and factory configuration.
  pub instance: InstanceConf,
  /// Pre-processing configuration.
  pub preproc: PreprocConf,
  /// Solver configuration.
  pub solver: SmtConf,
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
  #[inline]
  pub fn out_dir(& self, instance: & Instance) -> PathBuf {
    let mut path = PathBuf::from(& self.out_dir) ;
    if let Some(clause) = instance.split() {
      path.push( format!("split_on_clause_{}", clause) )
    }
    path
  }

  /// Input file.
  #[inline]
  pub fn in_file(& self) -> Option<& String> {
    self.file.as_ref()
  }
  /// Result to check file.
  #[inline]
  pub fn check_file(& self) -> Option<& String> {
    self.check.as_ref()
  }

  /// Checks if we're out of time.
  #[inline]
  pub fn check_timeout(& self) -> Res<()> {
    if let Some(max) = self.timeout.as_ref() {
      if & Instant::now() > max {
        bail!( ErrorKind::Timeout )
      }
    }
    Ok(())
  }
  /// Time until timeout.
  #[inline]
  pub fn until_timeout(& self) -> Option<Duration> {
    if let Some(timeout) = self.timeout.as_ref() {
      let now = Instant::now() ;
      if & now > timeout {
        Some( Duration::new(0,0) )
      } else {
        Some( * timeout - now )
      }
    } else {
      None
    }
  }

  /// Parses command-line arguments and generates the configuration.
  pub fn clap() -> Self {
    let mut app = App::new( crate_name!() ) ;
    app = Self::add_args(app, 0) ;
    app = PreprocConf::add_args(app, 100) ;
    app = InstanceConf::add_args(app, 200) ;
    app = SmtConf::add_args(app, 300) ;
    app = IceConf::add_args(app, 400) ;
    app = TeacherConf::add_args(app, 500) ;
    app = Self::add_check_args(app, 600) ;

    let matches = app.get_matches() ;

    // Input file.
    let file = matches.value_of("input file").map(|s| s.to_string()) ;

    // Verbosity
    let mut verb = 0 ;
    for _ in 0..matches.occurrences_of("verb") {
      verb += 1
    }
    for _ in 0..matches.occurrences_of("quiet") {
      if verb > 0 {
        verb -= 1
      }
    }

    // Colors.
    let color = ::isatty::stdout_isatty() && bool_of_matches(
      & matches, "color"
    ) ;
    let styles = Styles::new(color) ;

    // Output directory.
    let out_dir = matches.value_of("out_dir").expect(
      "unreachable(out_dir): default is provided"
    ).to_string() ;

    // Profiling.
    let stats = bool_of_matches(& matches, "stats") ;

    // Inference flag.
    let infer = bool_of_matches(& matches, "infer") ;

    // Inference flag.
    let split_step = bool_of_matches(& matches, "split_step") ;

    // Timeout.
    let timeout = match int_of_matches(& matches, "timeout") {
      0 => None,
      n => Some(
        Instant::now() + Duration::new(n as u64, 0)
      ),
    } ;

    let split = bool_of_matches(& matches, "split") ;

    // Result checking.
    let check = matches.value_of("check").map(
      |s| s.to_string()
    ) ;
    let check_eld = bool_of_matches(& matches, "check_eld") ;
    let check_simpl = bool_of_matches(& matches, "check_simpl") ;

    // Timeout.
    let term_simpl = int_of_matches(& matches, "term_simpl") ;

    let instance = InstanceConf::new(& matches) ;
    let preproc = PreprocConf::new(& matches) ;
    let solver = SmtConf::new(& matches) ;
    let ice = IceConf::new(& matches) ;
    let teacher = TeacherConf::new(& matches) ;

    Config {
      file, verb, stats, infer, split, split_step,
      timeout, out_dir, styles,
      check, check_eld, check_simpl, term_simpl,
      instance, preproc, solver, ice, teacher,
    }
  }

  /// Adds clap options to a clap App.
  pub fn add_args(app: App, mut order: usize) -> App {
    let mut order = || {
      order += 1 ;
      order
    } ;

    app.author( crate_authors!() ).version(
      * ::common::version
    ).about(
      "ICE engine for systems described as Horn Clauses."
    ).arg(

      Arg::with_name("input file").help(
        "sets the input file to use"
      ).index(1).display_order( order() )

    ).arg(

      Arg::with_name("verb").short("-v").help(
        "increases verbosity"
      ).takes_value(false).multiple(true).display_order( order() )

    ).arg(

      Arg::with_name("quiet").short("-q").help(
        "decreases verbosity"
      ).takes_value(false).multiple(true).display_order( order() )

    ).arg(

      Arg::with_name("color").long("--color").short("-c").help(
        "(de)activates coloring (off if output is not a tty)"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "on"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("out_dir").long("--out_dir").short("-o").help(
        "sets the output directory"
      ).value_name(
        "DIR"
      ).default_value(
        "hoice_out"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("stats").long("--stats").short("-s").help(
        "reports some statistics at the end of the run"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("infer").long("--infer").short("-i").help(
        "if `off`, ignore `check-sat` and `get-model` queries"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "on"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("timeout").long("--timeout").short("-t").help(
        "sets a timeout in seconds, `0` for none"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value(
        "0"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("split").long("--split").help(
        "reason on each negative clause separately"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "on"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("split_step").long("--split_step").help(
        "pause between negative clauses in split mode"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "off"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("term_simpl").long("--term_simpl").help(
        "level of term simplification between 0 and 3"
      ).validator(
        int_validator
      ).value_name(
        "int"
      ).default_value(
        "1"
      ).takes_value(true).number_of_values(1).display_order(
        order()
      ).hidden(true)

    ).arg(

      Arg::with_name("check_simpl").long("--check_simpl").help(
        "if true, check all simplifications"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).display_order(
        order()
      ).hidden(true)

    )
  }

  /// Add args related to result checking.
  pub fn add_check_args(app: App, mut order: usize) -> App {
    let mut order = || {
      order += 1 ;
      order
    } ;

    app.arg(

      Arg::with_name("check").long("--check").help(
        "checks a model for the input system (does not run inference)"
      ).value_name(
        "FILE"
      ).takes_value(true).number_of_values(1).display_order( order() )

    ).arg(

      Arg::with_name("check_eld").long("--check_eld").help(
        "if `check` is active, expect eldarica-style result"
      ).validator(
        bool_validator
      ).value_name(
        bool_format
      ).default_value(
        "no"
      ).takes_value(true).number_of_values(1).display_order( order() )

    )
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
  fn default() -> Self { Styles::new(true) }
}
impl ColorExt for Styles {
  fn styles(& self) -> & Styles { self }
}
impl Styles {
  /// Creates some styles.
  pub fn new(colored: bool) -> Self {
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
pub static bool_format: & str = "on/true|no/off/false" ;

/// Boolean of a string.
pub fn bool_of_str(s: & str) -> Option<bool> {
  match & s as & str {
    "on" | "true" => Some(true),
    "no" | "off" | "false" => Some(false),
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

/// Validates integer input between some bounds.
pub fn bounded_int_validator(
  s: String, lo: usize, hi: usize
) -> Result<(), String> {
  use std::str::FromStr ;
  match usize::from_str(& s) {
    Ok(val) => if lo <= val && val <= hi {
      Ok(())
    } else {
      Err(
        format!(
          "expected a value between {} and {}, got `{}`", lo , hi, val
        )
      )
    },
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
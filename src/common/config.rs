//! Hoice's global configuration.
//!
//! (Sub-)configurations are created with the `make_conf` macro. That way the help and long help
//! for each field of the (sub-)configs end up as comments automatically.

use std::path::PathBuf;

use ansi_term::{Colour, Style};
use clap::{crate_authors, crate_name, Arg};
use error_chain::bail;
use rsmt2::SmtConf as SolverConf;

use crate::{common::mk_dir, errors::*, instance::Instance};

/// Creates a function adding arguments to a `clap::App`.
macro_rules! app_fun {
    // Internal rules.
    (@app $app:expr, $order:expr =>) => ($app);
    (@app $app:expr, $o7rder:expr =>
        , $($tail:tt)*
    ) => (
        app_fun!(@app $app, $order => $($tail)*)
    );
    (@app $app:expr, $order:expr =>
        $id:ident($($stuff:tt)*) $($tail:tt)*
    ) => ({
        let arg = app_fun!(
            @arg Arg::new(stringify!($id)).display_order(*$order) => $($stuff)*
        );
        *$order += 1;
        let app = $app.arg(arg);
        app_fun!(@app app, $order => $($tail)*)
    });

    (@arg $arg:expr => long $long:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.long($long) => $($stuff)*)
    );
    (@arg $arg:expr => short $short:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.short($short) => $($stuff)*)
    );
    (@arg $arg:expr => help $help:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.help($help) => $($stuff)*)
    );
    (@arg $arg:expr => long_help $long_help:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.long_help($long_help) => $($stuff)*)
    );
    (@arg $arg:expr => validator $validator:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.validator($validator) => $($stuff)*)
    );
    (@arg $arg:expr => val_name $val_name:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.value_name($val_name) => $($stuff)*)
    );
    (@arg $arg:expr => default $default:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.default_value($default) => $($stuff)*)
    );
    (@arg $arg:expr => takes_val, $($stuff:tt)*) => (
        app_fun!(@arg $arg.takes_value(true) => $($stuff)*)
    );
    (@arg $arg:expr => val_nb $val_nb:expr, $($stuff:tt)*) => (
        app_fun!(@arg $arg.number_of_values($val_nb) => $($stuff)*)
    );
    (@arg $arg:expr => hide, $($stuff:tt)*) => (
        app_fun!(@arg $arg.hide(true) => $($stuff)*)
    );
    (@arg $arg:expr => $(,)*) => ($arg);
    (@arg $arg:expr => $stuff:tt) => (
        app_fun!(@arg $arg => $stuff,)
    );
    (@arg $arg:expr => $stuff_1:tt $stuff_2:tt) => (
        app_fun!(@arg $arg => $stuff_1 $stuff_2,)
    );

    // Entry point.
    ($(#[$doc:meta])* $fun:ident $($stuff:tt)*) => (
        $(#[$doc])*
        pub fn $fun(app: App, order: &mut usize) -> App {
            app_fun!(@app app, order => $($stuff)*)
        }
    );
}

/// Creates a structure with some fields corresponding to CLAs.
///
/// A field is an ident followed by a comma-separated list of CLAP options between parens. The
/// first two elements of the list need to be the **short help** followed by the **long help**.
macro_rules! make_conf {
    ($(#[$struct_meta:meta])* $struct:ident {$(
        $arg:ident, $field:ident: $field_ty:ty {
            help $help:expr,
            long_help $long_help:expr,
            $($tail:tt)*
        } {
            |$mtch:ident| $field_do:expr
        }
    )*}

    $($rest:tt)*

    ) => (
        $(#[$struct_meta])*
        pub struct $struct {
            $(
                #[doc = $help]
                #[doc = ""]
                #[doc = $long_help]
                pub $field: $field_ty,
            )*
        }
        impl $struct {
            app_fun! {
                /// Adds CLAP info to an `App`.
                add_args
                $(
                    $arg ( help $help, long_help $long_help, $($tail)* )
                )*
            }

            /// Constructor from some CLAP matches.
            pub fn new(matches: &Matches) -> Self {
                $(let $field = {
                    let $mtch = matches.value_of(stringify!($arg)).unwrap_or_else(
                        || panic!(
                            "unreachable, default for {} should be provided",
                            stringify!($arg)
                        )
                    );
                    $field_do
                };)*
                $struct {
                    $($field),*
                }
            }
        }

        $($rest)*
    );
}

/// Clap `App` with static lifetimes.
pub type App = clap::Command<'static>;
/// Clap `ArgMatches` with static lifetime.
pub type Matches = clap::ArgMatches;

/// Functions all sub-configurations must have.
pub trait SubConf {
    /// True if the options of the subconf need the output directory.
    fn need_out_dir(&self) -> bool;
}

make_conf! {
    /// Solver configuration.
    SmtConf {
        z3_cmd, conf: SolverConf {
            help "Sets the command used to call z3.",
            long_help "\
                Specifies which command to run to spawn z3. Hoice automatically launches it in \
                *interactive* mode, so there's no need to specify `-in`.\
            ",
            long "--z3",
            default "z3",
            takes_val,
            val_nb 1,
        } {
            |mtch| {
                let mut conf = SolverConf::z3(mtch);
                conf.models();
                conf
            }
        }
        log_smt, log: bool {
            help "(De)activates smt logging to the output directory.",
            long_help "\
                If active, logs the interactions with *all* the solvers in the output directory.\
            ",
            long "--log_smt",
            validator bool_validator,
            val_name bool_format,
            default "no",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }
    }

    impl SubConf for SmtConf {
        fn need_out_dir(&self) -> bool {
            self.log
        }
    }

    impl SmtConf {
        /// Actual, `rsmt2` solver configuration.
        pub fn conf(&self) -> SolverConf {
            self.conf.clone()
        }

        /// Spawns a solver.
        ///
        /// Performs the solver initialization step given by `common::smt::init`.
        ///
        /// If logging is active, will log to `<name>.smt2`.
        fn internal_spawn<Parser, I>(
            &self,
            name: &'static str,
            parser: Parser,
            instance: I,
            preproc: bool,
        ) -> Res<::rsmt2::Solver<Parser>>
        where
            I: AsRef<Instance>,
        {
            let mut smt_conf = self.conf.clone();
            if let Some(timeout) = crate::common::conf.until_timeout() {
                smt_conf.option(format!("-T:{}", timeout.as_secs() + 1));
            }

            let mut solver = ::rsmt2::Solver::new(smt_conf, parser)?;
            if let Some(log) = self
                .log_file(name, instance.as_ref())
                .chain_err(|| format!("While opening log file for {}", crate::common::conf.emph(name)))?
            {
                solver.tee(log)?
            }

            if preproc {
                crate::smt::preproc_init(&mut solver)?
            } else {
                crate::smt::init(&mut solver, instance)?
            }
            Ok(solver)
        }

        /// Spawns a solver.
        ///
        /// Performs the solver initialization step given by `common::smt::init`.
        ///
        /// If logging is active, will log to `<name>.smt2`.
        pub fn spawn<Parser, I>(
            &self,
            name: &'static str,
            parser: Parser,
            instance: I,
        ) -> Res<::rsmt2::Solver<Parser>>
        where
            I: AsRef<Instance>,
        {
            self.internal_spawn(name, parser, instance, false)
        }

        /// Spawns a preprocessing solver.
        ///
        /// Performs the solver initialization step given by `common::smt::init`.
        ///
        /// If logging is active, will log to `<name>.smt2`.
        pub fn preproc_spawn<Parser, I>(
            &self,
            name: &'static str,
            parser: Parser,
            instance: I,
        ) -> Res<::rsmt2::Solver<Parser>>
        where
            I: AsRef<Instance>,
        {
            self.internal_spawn(name, parser, instance, true)
        }

        /// Smt log dir, if any.
        fn log_dir(&self, instance: &Instance) -> Res<Option<PathBuf>> {
            if self.log {
                let mut path = crate::common::conf.out_dir(instance);
                path.push("solvers");
                mk_dir(&path)?;
                Ok(Some(path))
            } else {
                Ok(None)
            }
        }

        /// Smt log file, if any.
        fn log_file<S: AsRef<str>>(
            &self,
            name: S,
            instance: &Instance,
        ) -> Res<Option<::std::fs::File>> {
            use std::fs::OpenOptions;
            if let Some(mut path) = self.log_dir(instance)? {
                path.push(name.as_ref());
                path.set_extension("smt2");
                let file = OpenOptions::new()
                    .write(true)
                    .truncate(true)
                    .create(true)
                    .open(&path)
                    .chain_err(
                        || format!("while creating smt log file {}", path.to_string_lossy())
                    )?;
                Ok(Some(file))
            } else {
                Ok(None)
            }
        }
    }
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
    fn need_out_dir(&self) -> bool {
        false
    }
}
impl InstanceConf {
    /// Adds clap options to a clap App.
    pub fn add_args(app: App, _: usize) -> App {
        app
    }

    /// Creates itself from some matches.
    pub fn new(_: &Matches) -> Self {
        InstanceConf {
            term_capa: 3_000,
            clause_capa: 42,
            pred_capa: 42,
        }
    }
}

make_conf! {
    /// Preprocessing configuration.
    PreprocConf {

        preproc, active: bool {
            help "(De)activates pre-processing.",
            long_help "\
                If inactive, almost none of the pre-processors will run. Only `simplify` will \
                run, the pre-processor in charge of simplifying clauses locally. That is, clauses \
                are looked at one by one, not in relation with one another.\
            ",
            long "--preproc",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        log_preproc, log_preproc: bool {
            help "(De)activates instance logging during preprocessing.",
            long_help "\
                If active, the instance will be logged in the output directory whenever a \
                pre-processor runs and modifies it.\
            ",
            long "--log_preproc",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "no",
        } {
            |val| bool_of_match(val)
        }

        prune_terms, prune_terms: bool {
            help "(De)activates expensive clause term pruning when simplifying clauses.",
            long_help "\
                If active, runs an SMT-solver to check atoms one by one for redundancy and \
                conflicts.\
            ",
            long "--prune_terms",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "no",
            hide,
        } {
            |val| bool_of_match(val)
        }

        one_rhs, one_rhs: bool {
            help "(De)activates one rhs reduction.",
            long_help "\
                If active, predicates that appear as a consequent in exactly one clause will be \
                replaced by the tail of said clause, when possible. This pre-processor might \
                introduce quantifiers in the predicates' definitions.\
            ",
            long "--one_rhs",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        one_lhs, one_lhs: bool {
            help "(De)activates reduction of predicate appearing in exactly one clause lhs.",
            long_help "\
                If active, predicates that appear as a consequent in exactly one clause will be \
                replaced by the definition inferred from said clause, when possible. This \
                pre-processor might introduce quantifiers in the predicates' definitions.\
            ",
            long "--one_lhs",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        arg_red, arg_red: bool {
            help "(De)activates argument reduction.",
            long_help "\
                If active, looks for predicate arguments that can be removed without changing the \
                semantics. Only removes arguments that are irrelevant, similar to a cone of \
                influence analysis.\
            ",
            long "--arg_red",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        cfg_red, cfg_red: bool {
            help "(De)activates control flow graph reduction.",
            long_help "\
                If active, analyzes the *control flow graph* of the predicates and inlines \
                predicates that are not involved in loops. This pre-processor might introduce \
                quantifiers in the predicates' definitions.\
            ",
            long "--cfg_red",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        log_pred_dep, log_pred_dep: bool {
            help "(De)activates predicate dependency dumps (cfg_red).",
            long_help "\
                If active, dumps the dependencies between the predicates as a `dot` graph. If \
                `dot` is available on your computer, the pdf will be generated automatically. In \
                addition to the original dependency graph, a new graph is dumped each time a \
                pre-processor changed the relations between the predicates.\
            ",
            long "--log_pred_dep",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "no",
        } {
            |val| bool_of_match(val)
        }

        runroll, runroll: bool {
            help "(De)activates reverse unrolling.",
            long_help "\
                If active, predicates appearing in negative clauses will be unrolled in reverse.\
            ",
            long "--runroll",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "off",
            hide,
        } {
            |val| bool_of_match(val)
        }

        pos_unroll, pos_unroll: bool {
            help "(De)activates positive unrolling.",
            long_help "\
                If active, predicates appearing in positive clauses will be unrolled if unrolling \
                them creates positive clauses for predicates that did not appear in positive \
                clauses yet.\
            ",
            long "--pos_unroll",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        neg_unroll, neg_unroll: bool {
            help "(De)activates negative unrolling.",
            long_help "\
                If active, predicates appearing in negative clauses will be unrolled if unrolling \
                them creates negative clauses for predicates that did not appear in negative \
                clauses yet.\
            ",
            long "--neg_unroll",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        split_strengthen, split_strengthen: bool {
            help "(De)activates strengthening when splitting is active.",
            long_help "\
                If active, negative clauses ignored while splitting will be injected in \
                implication clauses. This strengthens a given split using information from \
                (currently) ignored negative clauses.\
            ",
            long "--split_strengthen",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
        } {
            |val| bool_of_match(val)
        }

        split_sort, split_sort: bool {
            help "(De)activates clause sorting when splitting is active.",
            long_help "\
                If active, hoice will sort the negative clauses before splitting on them. This \
                is a heuristic and does not give any guarantees as to whether it really improves \
                solving.\
            ",
            long "--split_sort",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
        } {
            |val| bool_of_match(val)
        }

        strict_neg, strict_neg: bool {
            help "(De)activates strengthening by strict negative clauses.",
            long_help "\
                If active, hoice will use strict negative clauses (clauses that have only one \
                predicate application) to infer partial definitions for the predicates. If `pred` \
                appears in `tail => (pred _)`, then `pred` will be constructed as
                `tail /\\ <def>` where `<def>` needs to be inferred by hoice.\
            ",
            long "--strict_neg",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }

        fun_preds, fun_preds: bool {
            help "(De)activates predicate-to-function reduction.",
            long_help "\
                If active, hoice will attempt to reconstruct some of the predicates as functions. \
                Only works on horn clauses over datatypes.\
            ",
            long "--fun_preds",
            takes_val,
            val_name bool_format,
            val_nb 1,
            validator bool_validator,
            default "on",
            hide,
        } {
            |val| bool_of_match(val)
        }
    }

    impl SubConf for PreprocConf {
        fn need_out_dir(&self) -> bool {
            self.log_preproc && self.active || self.log_pred_dep
        }
    }

    impl PreprocConf {
        /// Instance dump dir.
        fn log_dir<Path>(&self, sub: Path, instance: &Instance) -> Res<PathBuf>
        where
            Path: AsRef<::std::path::Path>,
        {
            let mut path = crate::common::conf.out_dir(instance);
            path.push("preproc");
            path.push(sub);
            mk_dir(&path)?;
            Ok(path)
        }

        /// Instance dump file.
        pub fn instance_log_file<S: AsRef<str>>(
            &self,
            name: S,
            instance: &Instance,
        ) -> Res<Option<::std::fs::File>> {
            use std::fs::OpenOptions;
            if self.log_preproc && self.active {
                let mut path = self.log_dir("instances", instance)?;
                path.push(name.as_ref());
                path.set_extension("smt2");
                let file = OpenOptions::new()
                    .write(true)
                    .truncate(true)
                    .create(true)
                    .open(&path)
                    .chain_err(|| {
                        format!(
                            "while creating instance dump file {}",
                            path.to_string_lossy()
                        )
                    })?;
                Ok(Some(file))
            } else {
                Ok(None)
            }
        }

        /// Predicate dependency file.
        pub fn pred_dep_file<S: AsRef<str>>(
            &self,
            name: S,
            instance: &Instance,
        ) -> Res<Option<(::std::fs::File, ::std::path::PathBuf)>> {
            use std::fs::OpenOptions;
            if self.log_pred_dep {
                let mut path = self.log_dir("pred_dep", instance)?;
                path.push(name.as_ref());
                path.set_extension("gv");
                let file = OpenOptions::new()
                    .write(true)
                    .truncate(true)
                    .create(true)
                    .open(&path)
                    .chain_err(|| {
                        format!(
                            "while creating predicade dependency graph file {}",
                            path.to_string_lossy()
                        )
                    })?;
                Ok(Some((file, path)))
            } else {
                Ok(None)
            }
        }
    }
}

make_conf! {
    /// Ice learner configuration.
    IceConf {

        simple_gain_ratio, simple_gain_ratio: f64 {
            help "Percent of times simple gain will be used.",
            long_help "\
                Percent of times the learner uses *simple* gain instead of the normal gain \
                function. Simple gain only takes into account positive/negative data, and \
                ignores unclassified data.\
            ",
            long "--simple_gain_ratio",
            validator int_validator,
            val_name "int",
            default "20",
            takes_val,
            val_nb 1,
        } {
            |mtch| {
                let value = int_of_match(mtch) as f64 / 100.0;
                if value < 0.0 {
                    0.0
                } else if 1.0 < value {
                    1.0
                } else {
                    value
                }
            }
        }

        sort_preds, sort_preds: f64 {
            help "Predicate sorting before learning probability.",
            long_help "\
                Probability hoice will sort the predicates before it starts learning. Sorting \
                the predicates based on their learning data is almost always helpful, but \
                should not be systematic in order to avoid bad biases.\
            ",
            long "--sort_preds",
            validator int_validator,
            val_name "int",
            default "40",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| {
                let value = int_of_match(mtch) as f64 / 100.;
                if value < 0.0 {
                    0.0
                } else if 1.0 < value {
                    1.0
                } else {
                    value
                }
            }
        }

        rand_quals, rand_quals: bool {
            help "Randomizes the qualifiers before gain computation.",
            long_help "\
                If active, forces the learner to look at the qualifiers in random order each \
                time. The goal is to break the bad biases hoice might get when looking at the \
                qualifiers in the same order everytime.\
            ",
            long "--rand_quals",
            validator bool_validator,
            val_name bool_format,
            default "on",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }

        complete, complete: bool {
            help "Generates complete transformations for qualifiers.",
            long_help "\
                If active, generates a lot of qualifiers from the start for each predicate. \
                This might cause an explosion in the number of qualifiers. Probably best to \
                avoid it on big problems.\
            ",
            long "--qual_complete",
            validator bool_validator,
            val_name bool_format,
            default "no",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }

        qual_bias, qual_bias: bool {
            help "Predicate bias for qualifier section.",
            long_help "\
                If active, the qualifiers that are generated for a specific predicate will not be \
                generalized to other predicates. \
                This might cause an explosion in the number of qualifiers. Probably best to \
                avoid it on big problems.\
            ",
            long "--qual_bias",
            validator bool_validator,
            val_name bool_format,
            default "on",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }

        qual_print, qual_print: bool {
            help "(De)activates qualifier printing.",
            long_help "\
                If active, prints all the qualifiers at the beginning of the run and before each \
                learning step. Used for debugging.\
            ",
            long "--qual_print",
            validator bool_validator,
            val_name bool_format,
            default "no",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }

        gain_pivot, gain_pivot: f64 {
            help "Gain in percent above which hoice considers a qualifier satisfactory.",
            long_help "\
                Specifies the minimal gain for a qualifier to be considered satisfactory. The \
                learner evaluates the gain of each qualifier at each decision step, and keeps \
                the first one that has a gain greater than this value.\n
                \n\
                The value is in percent, between 0 and 100.\
            ",
            long "--gain_pivot",
            validator int_validator,
            val_name "int",
            default "10",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| {
                let value = int_of_match(mtch) as f64 / 100.0;
                if value < 0.0 {
                    0.0
                } else if 1.0 < value {
                    1.0
                } else {
                    value
                }
            }
        }

        gain_pivot_synth, gain_pivot_synth: Option<f64> {
            help "Same as `--gain_pivot` but for qualifier synthesis (inactive if > 100)",
            long_help "\
                Same as `--gain_pivot` but for qualifier synthesis. If > 100, the learner \
                considers there is no pivot and it will evaluate all synthesis candidates.\
            ",
            long "--gain_pivot_synth",
            validator int_validator,
            val_name "int",
            default "10",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| {
                let value = int_of_match(mtch) as f64 / 100.0;
                if value < 0.0 {
                    Some(0.0)
                } else if 1.0 < value {
                    None
                } else {
                    Some(value)
                }
            }
        }

        gain_pivot_inc, gain_pivot_inc: f64 {
            help "Increment for the gain pivot.",
            long_help "\
                Every `mod` learning step (where `mod` is the `--gain_pivot_mod`), the learner \
                will increase the gain pivot (`--gain_pivot`) by this value. Inactive if `0`.\
            ",
            long "--gain_pivot_inc",
            validator int_validator,
            val_name "int",
            default "0",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| {
                let value = int_of_match(mtch) as f64 / 100.0;
                if value < 0.0 {
                    0.0
                } else if 1.0 < value {
                    1.0
                } else {
                    value
                }
            }
        }

        gain_pivot_mod, gain_pivot_mod: usize {
                help "Number of learning steps before the gain pivot is increased.",
                long_help "\
                    Specifies the number of steps after which the gain pivot is increased \
                    by the value given by `--gain_pivot_inc`.\
                ",
                long "--gain_pivot_mod",
                validator int_validator,
                val_name "int",
                default "100000",
                takes_val,
                val_nb 1,
                hide,
        } {
            |mtch| int_of_match(mtch)
        }

        pure_synth, pure_synth: bool {
            help "If true, runs another pure-synthesis learner.",
            long_help "\
                If active, another learner will run in addition to the normal one. This \
                additional learner does not mine for qualifiers: it splits the data by relying \
                solely on qualifier synthesis.\
            ",
            long "--pure_synth",
            validator bool_validator,
            val_name bool_format,
            default "no",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }

        add_synth, add_synth: bool {
            help "Add synthesized qualifiers as normal qualifiers.",
            long_help "\
                If active, then whenever a qualifier obtained by synthesis is chosen to split \
                the data, this qualifier will be added as a regular qualifier for later.\
            ",
            long "--add_synth",
            validator bool_validator,
            val_name bool_format,
            default "on",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }

        mine_conjs, mine_conjs: bool {
            help "Mines conjunctions of atoms from clauses.",
            long_help "\
                If active, qualifier mining will generate conjunctions using the atoms appearing \
                in the tail of the clauses.\
            ",
            long "--mine_conjs",
            validator bool_validator,
            val_name bool_format,
            default "on",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }

        qual_step, qual_step: bool {
            help "Wait for user input on each (non-synthesis) qualifier.",
            long_help "\
                If active, the learner will display the current (non-synthesis) qualifier and its \
                gain, and wait for user input to keep going.\
            ",
            long "--qual_step",
            validator bool_validator,
            val_name bool_format,
            default "off",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }

        qual_synth_step, qual_synth_step: bool {
            help "Wait for user input on each synthesis qualifier.",
            long_help "\
                If active, the learner will display the current synthesis qualifier and its gain, \
                and wait for user input to keep going.\
            ",
            long "--qual_synth_step",
            validator bool_validator,
            val_name bool_format,
            default "off",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }
    }

    impl SubConf for IceConf {
        fn need_out_dir(&self) -> bool {
            false
        }
    }
}

make_conf! {
    /// Ice learner configuration.
    TeacherConf {

        teach_step, step: bool {
            help "Forces the teacher will wait for user input between learning steps.",
            long_help "\
                If active, the teacher will stop before *i)* checking the candidates and *ii)* \
                sending learning data to the learner. Progress will resume when the user says so.\
            ",
            long "--teach_step",
            validator bool_validator,
            val_name bool_format,
            default "no",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }

        assistant, assistant: bool {
            help "(De)activates breaking implication constraints.",
            long_help "\
                If active the assistant will run: it receives (new) implications constraints \
                from the teacher and attempts to break them. Almost always useful, but might \
                slow progress down slightly.\
            ",
            long "--assistant",
            validator bool_validator,
            val_name bool_format,
            default "on",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }

        bias_cexs, bias_cexs: bool {
            help "(De)activates biased implication constraints.",
            long_help "\
                If active, when the teacher checks implication constraint, it will look for \
                counterexamples that have at least one positive/negative sample.\
            ",
            long "--bias_cexs",
            validator bool_validator,
            val_name bool_format,
            default "on",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }

        max_bias, max_bias: bool {
            help "(De)activates a more extreme version of `--bias_cexs`.",
            long_help "\
                If active, only considers counterexamples that have no unclassified data when \
                possible.\
            ",
            long "--max_bias",
            validator bool_validator,
            val_name bool_format,
            default "off",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }

        partial, partial: bool {
            help "(De)activates partial samples.",
            long_help "\
                If active, the teacher is allowed to generate *partial samples*. These are \
                samples that have unspecified, *don't care* values.\
            ",
            long "--partial",
            validator bool_validator,
            val_name bool_format,
            default "on",
            takes_val,
            val_nb 1,
        } {
            |mtch| bool_of_match(mtch)
        }

        restart_on_cex, restart_on_cex: bool {
            help "Restarts the teacher's solver for each counterexample query.",
            long_help "\
                If active, the teacher will always restart before checking the learner's \
                candidates for counterexamples. Note that if the clauses mention datatypes \
                the solver is always restarted.\
            ",
            long "--restart_on_cex",
            validator bool_validator,
            val_name bool_format,
            default "off",
            takes_val,
            val_nb 1,
            hide,
        } {
            |mtch| bool_of_match(mtch)
        }
    }

    impl SubConf for TeacherConf {
        fn need_out_dir(&self) -> bool {
            false
        }
    }
}

use std::time::{Duration, Instant};

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
    fn styles(&self) -> &Styles {
        &self.styles
    }
}
impl Config {
    /// Output directory as a `PathBuf`.
    #[inline]
    pub fn out_dir(&self, instance: &Instance) -> PathBuf {
        let mut path = PathBuf::from(&self.out_dir);
        if let Some(clause) = instance.split() {
            path.push(format!("split_on_clause_{}", clause))
        }
        path
    }

    /// Input file.
    #[inline]
    pub fn in_file(&self) -> Option<&String> {
        self.file.as_ref()
    }
    /// Result to check file.
    #[inline]
    pub fn check_file(&self) -> Option<&String> {
        self.check.as_ref()
    }

    /// Checks if we're out of time.
    #[inline]
    pub fn check_timeout(&self) -> Res<()> {
        if let Some(max) = self.timeout.as_ref() {
            if Instant::now() > *max {
                bail!(ErrorKind::Timeout)
            }
        }
        Ok(())
    }
    /// Time until timeout.
    #[inline]
    pub fn until_timeout(&self) -> Option<Duration> {
        if let Some(timeout) = self.timeout.as_ref() {
            let now = Instant::now();
            if now > *timeout {
                Some(Duration::new(0, 0))
            } else {
                Some(*timeout - now)
            }
        } else {
            None
        }
    }

    /// Parses command-line arguments and generates the configuration.
    pub fn clap() -> Self {
        let mut app = App::new(crate_name!());
        // let mut order = 0;
        app = Self::add_args(app, 0);
        app = PreprocConf::add_args(app, &mut 100);
        app = InstanceConf::add_args(app, 200);
        app = SmtConf::add_args(app, &mut 300);
        app = IceConf::add_args(app, &mut 400);
        app = TeacherConf::add_args(app, &mut 500);
        app = Self::add_check_args(app, 600);

        let matches = app.get_matches();

        // Input file.
        let file = matches.value_of("input file").map(|s| s.to_string());

        // Verbosity
        let mut verb = 0;
        for _ in 0..matches.occurrences_of("verb") {
            verb += 1
        }
        for _ in 0..matches.occurrences_of("quiet") {
            if verb > 0 {
                verb -= 1
            }
        }

        // Colors.
        let color = ::atty::is(::atty::Stream::Stdout) && bool_of_matches(&matches, "color");
        let styles = Styles::new(color);

        // Output directory.
        let out_dir = matches
            .value_of("out_dir")
            .expect("unreachable(out_dir): default is provided")
            .to_string();

        // Profiling.
        let stats = bool_of_matches(&matches, "stats");

        // Inference flag.
        let infer = bool_of_matches(&matches, "infer");

        // Inference flag.
        let split_step = bool_of_matches(&matches, "split_step");

        // Timeout.
        let timeout = match int_of_matches(&matches, "timeout") {
            0 => None,
            n => Some(Instant::now() + Duration::new(n as u64, 0)),
        };

        let split = bool_of_matches(&matches, "split");

        // Result checking.
        let check = matches.value_of("check").map(|s| s.to_string());
        let check_eld = bool_of_matches(&matches, "check_eld");
        let check_simpl = bool_of_matches(&matches, "check_simpl");

        // Timeout.
        let term_simpl = int_of_matches(&matches, "term_simpl");

        let instance = InstanceConf::new(&matches);
        let preproc = PreprocConf::new(&matches);
        let solver = SmtConf::new(&matches);
        let ice = IceConf::new(&matches);
        let teacher = TeacherConf::new(&matches);

        Config {
            file,
            verb,
            stats,
            infer,
            split,
            split_step,
            timeout,
            out_dir,
            styles,
            check,
            check_eld,
            check_simpl,
            term_simpl,
            instance,
            preproc,
            solver,
            ice,
            teacher,
        }
    }

    /// Adds clap options to a clap App.
    pub fn add_args(app: App, mut order: usize) -> App {
        let mut order = || {
            order += 1;
            order
        };

        app.author(crate_authors!())
            .version(*crate::common::version)
            .about("ICE engine for systems described as Horn Clauses.")
            .arg(
                Arg::new("input file")
                    .help("sets the input file to use")
                    .index(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("verb")
                    .short('v')
                    .help("increases verbosity")
                    .takes_value(false)
                    .multiple_occurrences(true)
                    .display_order(order()),
            )
            .arg(
                Arg::new("quiet")
                    .short('q')
                    .help("decreases verbosity")
                    .takes_value(false)
                    .multiple_occurrences(true)
                    .display_order(order()),
            )
            .arg(
                Arg::new("color")
                    .long("--color")
                    .short('c')
                    .help("(de)activates coloring (off if output is not a tty)")
                    .validator(bool_validator)
                    .value_name(bool_format)
                    .default_value("on")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("out_dir")
                    .long("--out_dir")
                    .short('o')
                    .help("sets the output directory")
                    .value_name("DIR")
                    .default_value("hoice_out")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("stats")
                    .long("--stats")
                    .short('s')
                    .help("reports some statistics at the end of the run")
                    .validator(bool_validator)
                    .value_name(bool_format)
                    .default_value("no")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("infer")
                    .long("--infer")
                    .short('i')
                    .help("if `off`, ignore `check-sat` and `get-model` queries")
                    .validator(bool_validator)
                    .value_name(bool_format)
                    .default_value("on")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("timeout")
                    .long("--timeout")
                    .short('t')
                    .help("sets a timeout in seconds, `0` for none")
                    .validator(int_validator)
                    .value_name("int")
                    .default_value("0")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("split")
                    .long("--split")
                    .help("reason on each negative clause separately")
                    .validator(bool_validator)
                    .value_name(bool_format)
                    .default_value("off")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("split_step")
                    .long("--split_step")
                    .help("pause between negative clauses in split mode")
                    .validator(bool_validator)
                    .value_name(bool_format)
                    .default_value("off")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order()),
            )
            .arg(
                Arg::new("term_simpl")
                    .long("--term_simpl")
                    .help("level of term simplification between 0 and 3")
                    .validator(int_validator)
                    .value_name("int")
                    .default_value("1")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order())
                    .hide(true),
            )
            .arg(
                Arg::new("check_simpl")
                    .long("--check_simpl")
                    .help("if true, check all simplifications")
                    .validator(bool_validator)
                    .value_name(bool_format)
                    .default_value("no")
                    .takes_value(true)
                    .number_of_values(1)
                    .display_order(order())
                    .hide(true),
            )
    }

    /// Add args related to result checking.
    pub fn add_check_args(app: App, mut order: usize) -> App {
        let mut order = || {
            order += 1;
            order
        };

        app.arg(
            Arg::new("check")
                .long("--check")
                .help("checks a model for the input system (does not run inference)")
                .value_name("FILE")
                .takes_value(true)
                .number_of_values(1)
                .display_order(order()),
        )
        .arg(
            Arg::new("check_eld")
                .long("--check_eld")
                .help("if `check` is active, expect eldarica-style result")
                .validator(bool_validator)
                .value_name(bool_format)
                .default_value("no")
                .takes_value(true)
                .number_of_values(1)
                .display_order(order()),
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
    fn default() -> Self {
        Styles::new(true)
    }
}
impl ColorExt for Styles {
    fn styles(&self) -> &Styles {
        self
    }
}
impl Styles {
    /// Creates some styles.
    pub fn new(colored: bool) -> Self {
        Styles {
            emph: if colored {
                Style::new().bold()
            } else {
                Style::new()
            },
            hap: if colored {
                Colour::Green.normal().bold()
            } else {
                Style::new()
            },
            sad: if colored {
                Colour::Yellow.normal().bold()
            } else {
                Style::new()
            },
            bad: if colored {
                Colour::Red.normal().bold()
            } else {
                Style::new()
            },
        }
    }
}

/// Can color things.
pub trait ColorExt {
    /// The styles in the colorizer: emph, happy, sad, and bad.
    fn styles(&self) -> &Styles;
    /// String emphasis.
    #[inline]
    fn emph<S: AsRef<str>>(&self, s: S) -> String {
        format!("{}", self.styles().emph.paint(s.as_ref()))
    }
    /// Happy string.
    #[inline]
    fn happy<S: AsRef<str>>(&self, s: S) -> String {
        format!("{}", self.styles().hap.paint(s.as_ref()))
    }
    /// Sad string.
    #[inline]
    fn sad<S: AsRef<str>>(&self, s: S) -> String {
        format!("{}", self.styles().sad.paint(s.as_ref()))
    }
    /// Bad string.
    #[inline]
    fn bad<S: AsRef<str>>(&self, s: S) -> String {
        format!("{}", self.styles().bad.paint(s.as_ref()))
    }
}

/// Format for booleans.
pub static bool_format: &str = "on/true|no/off/false";

/// Boolean of a string.
pub fn bool_of_str(s: &str) -> Option<bool> {
    match &s as &str {
        "on" | "true" => Some(true),
        "no" | "off" | "false" => Some(false),
        _ => None,
    }
}

/// Boolean of a match value.
pub fn bool_of_match(mtch: &str) -> bool {
    bool_of_str(mtch).expect("failed to retrieve boolean argument")
}

/// Boolean of some matches.
///
/// Assumes a default is provided and the input has been validated with
/// `bool_validator`.
pub fn bool_of_matches(matches: &Matches, key: &str) -> bool {
    bool_of_match(
        matches
            .value_of(key)
            .unwrap_or_else(|| panic!("could not retrieve value for CLA `{}`", key)),
    )
}

/// Integer of a single match.
pub fn int_of_match(mtch: &str) -> usize {
    use std::str::FromStr;
    usize::from_str(mtch).expect("failed to retrieve integer argument")
}

/// Integer of some matches.
///
/// Assumes a default is provided and the input has been validated with
/// `bool_validator`.
pub fn int_of_matches(matches: &Matches, key: &str) -> usize {
    matches
        .value_of(key)
        .map(|s| int_of_match(&s))
        .expect("failed to retrieve integer argument")
}

/// Validates integer input.
#[cfg_attr(feature = "cargo-clippy", allow(needless_pass_by_value))]
pub fn int_validator(s: &str) -> Result<(), String> {
    use std::str::FromStr;
    match usize::from_str(s) {
        Ok(_) => Ok(()),
        Err(_) => Err(format!("expected an integer, got `{}`", s)),
    }
}

/// Validates integer input between some bounds.
#[cfg_attr(feature = "cargo-clippy", allow(needless_pass_by_value))]
pub fn bounded_int_validator(s: String, lo: usize, hi: usize) -> Result<(), String> {
    use std::str::FromStr;
    match usize::from_str(&s) {
        Ok(val) => {
            if lo <= val && val <= hi {
                Ok(())
            } else {
                Err(format!(
                    "expected a value between {} and {}, got `{}`",
                    lo, hi, val
                ))
            }
        }
        Err(_) => Err(format!("expected an integer, got `{}`", s)),
    }
}

/// Validates boolean input.
#[cfg_attr(feature = "cargo-clippy", allow(needless_pass_by_value))]
pub fn bool_validator(s: &str) -> Result<(), String> {
    if bool_of_str(s).is_some() {
        Ok(())
    } else {
        Err(format!("expected `on/true` or `off/false`, got `{}`", s))
    }
}

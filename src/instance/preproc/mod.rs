//! Reduction strategies.
//!
//! The strategies are attached `struct`s so that they can be put in a vector
//! using single dispatch. That way, they can be combined however we want.

use common::* ;
use instance::* ;

pub mod utils ;

mod one_rhs ;
mod one_lhs ;
mod cfg_red ;
mod arg_red ;
mod bias_unroll ;
mod unroll ;
mod strict_neg_clauses ;
mod fun_preds ;

use self::{
  one_lhs::OneLhs,
  one_rhs::OneRhs,
  arg_red::ArgRed,
  cfg_red::CfgRed,
  bias_unroll:: BiasedUnroll,
  unroll::RUnroll,
  strict_neg_clauses::StrictNeg,
  fun_preds:: FunPreds,
} ;



/// Extension for a predicate.
///
/// Used by `extend_pred_left`.
pub type PredExtension = (
  TermSet, Vec<(Quantfed, Term)>
) ;



/// Runs pre-processing.
///
/// The boolean indicates wether a first pass of simplification runs on the
/// whole system before the rest. Should be true for top-level preproc, and
/// false for subsystems.
///
/// Finalizes the instance.
pub fn work(
  instance: & mut Instance, profiler: & Profiler,
) -> Res<()> {
  let res = {
    let instance = profile! {
      |profiler| wrap {
        PreInstance::new(instance) ?
      } "preproc", "pre-instance creation"
    } ;
    run(instance, profiler, true)
  } ;
  finalize(res, instance, profiler)
}

/// Runs pre-processing from a pre-instance.
fn run(
  instance: PreInstance, profiler: & Profiler, simplify_first: bool
) -> Res<()> {
  profile! { |profiler| tick "preproc" }

  let mut reductor = profile! {
    |profiler| wrap {
      Reductor::new(instance) ?
    } "preproc", "creation"
  } ;
  let res = reductor.run(profiler, simplify_first).and_then(
    |_| profile! {
      |profiler| wrap {
        reductor.destroy()
      } "preproc", "reductor destruction"
    }
  ) ;

  profile! { |profiler| mark "preproc" }
  res
}

/// Finalizes pre-processing
fn finalize(
  res: Res<()>, instance: & mut Instance, _profiler: & Profiler
) -> Res<()> {
  profile!(
    |_profiler| wrap {
      instance.finalize()
    } "finalizing"
  ) ? ;

  profile! {
    |_profiler|
    "positive          clauses" => add instance.pos_clauses().len()
  }
  profile! {
    |_profiler|
    "negative          clauses" => add instance.neg_clauses().len()
  }
  profile! {
    |_profiler|
    "negative (strict) clauses" => add instance.strict_neg_clauses().len()
  }

  match res {
    Err(e) => {
      if e.is_unsat() {
        instance.set_unsat()
      }
      bail!(e)
    },
    Ok(()) => ()
  }

  Ok(())
}


/// Runs pre-processing on a split version of the input instance.
///
/// Fails if `to_keep` is not a negative clause in `instance`.
///
/// Does **not** remove clauses that are tagged as being from unrolling.
pub fn work_on_split(
  instance: & Instance, to_keep: ClsIdx,
  ignore: & ClsSet, profiler: & Profiler
) -> Res<Instance> {

  profile! { |profiler| tick "splitting" }

  let mut split_instance = instance.clone_with_clauses(to_keep) ;

  let mut to_forget: Vec<_> = instance.neg_clauses(
  ).iter().filter_map(
    |c| if c == & to_keep /* || instance[* c].from_unrolling */ {
      None
    } else {
      Some(* c)
    }
  ).collect() ;

  let mut strict_neg_clauses = Vec::with_capacity(
    instance.neg_clauses().len()
  ) ;

  // We're going to forget clauses (swap-remove), going in descending order.
  to_forget.sort_unstable_by(|c_1, c_2| c_2.cmp(c_1)) ;
  for clause_idx in to_forget {
    if clause_idx != to_keep {
      let clause = split_instance.forget_clause(clause_idx) ? ;
      if conf.preproc.split_strengthen
      && ! ignore.contains(& clause_idx)
      && instance.strict_neg_clauses().contains(& clause_idx) {
        strict_neg_clauses.push(clause)
      }
    }
  }

  profile! { |profiler| mark "splitting" }

  let res = {

    let mut pre_instance = PreInstance::new(& mut split_instance) ? ;

    if conf.preproc.split_strengthen && strict_neg_clauses.len() < 30 {

      profile! { |profiler| tick "strengthening" }

      log! { @debug
        "strengthening using {} clauses", strict_neg_clauses.len()
      }

      let mut info = RedInfo::new() ;

      // Maps predicates to strengthening terms.
      let mut strength_map = PrdHMap::new() ;

      for clause in strict_neg_clauses {
        macro_rules! inconsistent {
          () => ({
            instance.check("work_on_split (instance)") ? ;
            instance.check("work_on_split (split)") ? ;
            bail!("inconsistent instance state")
          }) ;
        }

        let (pred, args) = {
          let mut pred_apps = clause.lhs_preds().iter() ;

          if let Some((pred, argss)) = pred_apps.next() {
            debug_assert! { pred_apps.next().is_none() }

            let mut argss = argss.iter() ;
            if let Some(args) = argss.next() {
              debug_assert! { argss.next().is_none() }
              (* pred, args)
            } else {
              inconsistent!()
            }
          } else {
            inconsistent!()
          }
        } ;

        log! { @debug
          "Strengthening using {}",
          clause.to_string_info( instance.preds() ) ?
        }

        use instance::preproc::utils::ExtractRes ;

        match profile!(
          |profiler| wrap {
            pre_instance.extraction().0.terms_of_lhs_app(
              true, & instance, & clause.vars,
              ( clause.lhs_terms(), clause.lhs_preds() ),
              None, (pred, args)
            )
          } "strengthening", "extraction"
        ) ? {
          ExtractRes::Trivial => bail!(
            "trivial clause during work_on_split"
          ),
          ExtractRes::Failed => bail!(
            "extraction failure during work_on_split"
          ),
          ExtractRes::SuccessTrue => bail!(
            "extracted true during work_on_split"
          ),
          ExtractRes::SuccessFalse => bail!(
            "extracted false during work_on_split"
          ),
          ExtractRes::Success((qvars, is_none, only_terms)) => {
            debug_assert! { is_none.is_none() } ;
            let (terms, preds) = only_terms.destroy() ;
            debug_assert! { preds.is_empty() } ;
            let entry = strength_map.entry(pred).or_insert_with(
              || (TermSet::new(), Vec::new())
            ) ;
            let terms = term::or(
              terms.into_iter().map(term::not).collect()
            ) ;
            if qvars.is_empty() {
              entry.0.insert( terms ) ;
            } else {
              entry.1.push((qvars, terms))
            }
          },
        }
      }

      info += profile! {
        |profiler| wrap {
          pre_instance.extend_pred_left(& strength_map) ?
        } "strengthening", "extend"
      } ;

      profile! { |profiler| mark "strengthening" }

      profile! {
        |profiler| "strengthening   pred red" => add info.preds
      }
      profile! {
        |profiler| "strengthening clause red" => add info.clauses_rmed
      }
      profile! {
        |profiler| "strengthening clause add" => add info.clauses_added
      }
    }

    if conf.preproc.active {
      run(pre_instance, profiler, true)
    } else {
      Ok(())
    }
  } ;

  finalize(res, & mut split_instance, profiler) ? ;

  Ok(split_instance)
}




/// Stores and applies the reduction techniques.
pub struct Reductor<'a> {
  /// The pre-instance.
  instance: PreInstance<'a>,
  /// Preinstance simplification.
  simplify: Option<Simplify>,
  /// Optional predicate argument reduction pre-processor.
  arg_red: Option<ArgRed>,
  /// Optional one rhs pre-processor.
  one_rhs: Option<OneRhs>,
  /// Optional one lhs pre-processor.
  one_lhs: Option<OneLhs>,
  /// Optional cfg pre-processor.
  cfg_red: Option<CfgRed>,
  /// Optional biased unroller.
  biased_unroll: Option<BiasedUnroll>,
  /// Optional reverse unroller.
  runroll: Option<RUnroll>,
  /// Optional strengthener by strict negative clauses.
  strict_neg: Option<StrictNeg>,
  /// Optional predicate-to-function reduction.
  fun_preds: Option<FunPreds>,
}
impl<'a> Reductor<'a> {
  /// Constructor.
  ///
  /// Checks the configuration to initialize the pre-processors.
  pub fn new(instance: PreInstance<'a>) -> Res<Self> {

    macro_rules! some_new {
      ($red:ident if $flag:ident $(and $flags:ident )*) => (
        some_new! { $red |if| conf.preproc.$flag $( && conf.preproc.$flags )* }
      ) ;
      ($red:ident if $flag:ident $(or $flags:ident )*) => (
        some_new! { $red |if| conf.preproc.$flag $( && conf.preproc.$flags )* }
      ) ;
      ($red:ident |if| $cond:expr) => (
        if $cond {
          Some( $red::new(& instance) )
        } else {
          None
        }
      ) ;
    }

    let simplify = Some( Simplify::new(& instance) ) ;
    let arg_red = some_new! { ArgRed if arg_red } ;

    let one_rhs = some_new! {
      OneRhs if one_rhs and one_rhs_full and reduction
    } ;
    let one_lhs = some_new! {
      OneLhs if one_lhs and one_lhs_full and reduction
    } ;

    let cfg_red = some_new! { CfgRed if cfg_red } ;

    let biased_unroll = some_new! {
      BiasedUnroll if pos_unroll or neg_unroll
    } ;
    let runroll = some_new! {
      RUnroll if neg_unroll
    } ;
    let strict_neg = some_new! {
      StrictNeg if strict_neg
    } ;
    let fun_preds = some_new! {
      FunPreds if fun_preds
    } ;

    Ok(
      Reductor {
        instance, simplify, arg_red,
        one_rhs, one_lhs,
        cfg_red, biased_unroll, runroll,
        strict_neg, fun_preds,
      }
    )
  }

  /// Destroys the reductor.
  pub fn destroy(self) -> Res<()> {
    self.instance.destroy()
  }

  /// Runs the full pre-processing.
  pub fn run(
    & mut self, _profiler: & Profiler, simplify_first: bool
  ) -> Res<()> {
    // Counter for preproc dumping.
    //
    // Starts at `1`, `0` is reserved for the fixed point.
    let mut count = 1 ;

    // Runs and profiles a pre-processor.
    //
    // Returns `true` if the pre-processor did something.
    macro_rules! run {
      (@ info $info_opt:expr) => (
        $info_opt.unwrap_or( RedInfo::new() )
      ) ;
      (@ bool $info_opt:expr) => (
        $info_opt.map(|info: RedInfo| info.non_zero()).unwrap_or(false)
      ) ;

      ($preproc:ident) => ( run!($preproc bool) ) ;
      ($preproc:ident $($tail:tt)*) => (
        if let Some(preproc) = self.$preproc.as_mut() {
          if let Some(red_info) = utils::run_preproc(
            & mut self.instance, _profiler, preproc, & mut count
          ) ? {
            run! { @ $($tail)* Some(red_info) }
          } else {
            return Ok(())
          }
        } else {
          run! { @ $($tail)* None }
        }
      ) ;
    }

    utils::register_stats(& self.instance, _profiler, count) ? ;

    if simplify_first {
      run! { simplify } ;
    }

    if ! conf.preproc.active || self.instance.track_samples() {
      return Ok(())
    }

    // Used to avoid running cfg reduction if nothing has changed since the
    // last run.
    let mut changed_since_cfg_red = true ;

    loop {

      if self.instance.is_solved() { break }
      conf.check_timeout() ? ;

      run! { arg_red } ;

      let changed = false ;

      if changed {
        changed_since_cfg_red = true ;
        continue
      }

      let changed = run! { one_rhs } ;
      let changed = run! { one_lhs } || changed ;

      if changed {
        changed_since_cfg_red = true ;
        continue
      }

      if self.instance.is_solved() { break }

      let changed = run! { fun_preds } ;

      if changed {
        changed_since_cfg_red = true ;
        continue
      }

      if changed_since_cfg_red {
        let changed = run! { cfg_red } ;

        if ! changed {
          break
        } else {
          changed_since_cfg_red = false
        }
      } else {
        break
      }

    }

    conf.check_timeout() ? ;


    if self.instance.split().is_none() && self.instance.clauses().len() > 20 {
      let biased_info = run!(biased_unroll info) ;
      if biased_info.non_zero() {
        run! { simplify } ;
      }

      let strict_neg_count = self.instance.strict_neg_clauses().2.fold(
        0, |acc, _| acc + 1
      ) ;
      if strict_neg_count <= 1
      && conf.preproc.runroll {
        let info = run!( runroll info ) ;
        if info.non_zero() {
          run! { simplify } ;
        }
      }
    }

    run! { strict_neg } ;

    utils::register_final_stats(& self.instance, _profiler) ? ;

    Ok(())
  }
}







/// Reduction strategy trait.
pub trait RedStrat {
  /// Pre-processor's name.
  fn name(& self) -> & 'static str ;

  /// Constructor.
  fn new(& Instance) -> Self ;

  /// Applies the reduction strategy. Returns the number of predicates reduced
  /// and the number of clauses forgotten.
  fn apply(
    & mut self, & mut PreInstance
  ) -> Res<RedInfo> ;
}


/// Calls `PredInstance::simplify_all`.
pub struct Simplify ;

impl RedStrat for Simplify {
  fn name(& self) -> & 'static str { "simplify" }

  fn new(_: & Instance) -> Self { Simplify }

  fn apply(
    & mut self, instance: & mut PreInstance
  ) -> Res<RedInfo> {
    instance.simplify_all()
  }
}
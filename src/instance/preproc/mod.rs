//! Reduction strategies.
//!
//! The strategies are attached `struct`s so that they can be put in a vector
//! using single dispatch. That way, they can be combined however we want.

use common::* ;
use instance::{
  *, preproc::utils::ExtractionCxt,
} ;

pub mod utils ;
use self::utils::{ ExtractRes } ;
pub mod graph ;
pub mod arg_red ;

use self::{
  arg_red::ArgRed as ArgRedInner,
  graph::Graph,
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
              clause.lhs_terms(), clause.lhs_preds(), None,
              pred, args
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
  /// Optional simple one rhs pre-processor.
  s_one_rhs: Option<SimpleOneRhs>,
  /// Optional simple one lhs pre-processor.
  s_one_lhs: Option<SimpleOneLhs>,
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

    let s_one_rhs = some_new! {
      SimpleOneRhs if one_rhs and reduction
    } ;
    let s_one_lhs = some_new! {
      SimpleOneLhs if one_lhs and reduction
    } ;

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

    Ok(
      Reductor {
        instance, simplify, arg_red,
        s_one_rhs, s_one_lhs, one_rhs, one_lhs,
        cfg_red, biased_unroll, runroll,
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

    // Checks if the instance is already solved.
    macro_rules! check_solved {
      () => (
        if self.instance.is_solved() {
          if ! self.instance.is_unsat() {
            profile! {
              |_profiler| tick "preproc", "final simplify"
            }
            // Check remaining clauses, maybe some of them are unsat.
            match self.instance.simplify_all() {
              Ok(_) => (),
              Err(e) => {
                if e.is_unsat() {
                  self.instance.set_unsat()
                }
                bail!(e)
              },
            }
            profile! {
              |_profiler| mark "preproc", "final simplify"
            }
          }
          return Ok(())
        }
      ) ;
    }

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

      // (
      //   |simplify| simplify $preproc:expr, $count:ident, $info:expr
      // ) => (
      // ) ; 
      // (
      //   |$name:ident| simplify $preproc:expr, $count:ident, $info:expr
      // ) => (
      //   $info += if let Some(simplify) = self.simplify.as_mut() {
      //     simplify.apply(& mut self.instance) ?
      //   } else {
      //     bail!("simplify should always be active")
      //   } ;
      //   preproc_dump!(
      //     self.instance =>
      //     format!("preproc_{:0>4}_{}_simplify", $count, $preproc.name()),
      //     format!(
      //       "Instance after running `{}` and simplifying.", $preproc.name()
      //     )
      //   ) ? ;
      // ) ;

      ($preproc:ident) => ( run!($preproc bool) ) ;
      ($preproc:ident $($tail:tt)*) => (
        if let Some(preproc) = self.$preproc.as_mut() {
          profile! {
            |_profiler| tick "preproc", preproc.name()
          }
          log! { @verb
            "running {}", conf.emph( preproc.name() )
          }
          let mut red_info = preproc.apply( & mut self.instance ) ? ;
          profile! {
            |_profiler| mark "preproc", preproc.name()
          }

          if red_info.non_zero() {
            // red_info += self.instance.force_trivial() ? ;
            count += 1 ;
            preproc_dump!(
              self.instance =>
              format!("preproc_{:0>4}_{}", count, preproc.name()),
              format!("Instance after running `{}`.", preproc.name())
            ) ? ;

            // run! { |$preproc| simplify preproc, count, red_info }

            profile!{
              |_profiler| format!(
                "{:>10}   pred red", preproc.name()
              ) => add red_info.preds
            }
            profile!{
              |_profiler| format!(
                "{:>10} clause red", preproc.name()
              ) => add red_info.clauses_rmed
            }
            profile!{
              |_profiler| format!(
                "{:>10} clause add", preproc.name()
              ) => add red_info.clauses_added
            }
            profile!{
              |_profiler| format!(
                "{:>10}    arg red", preproc.name()
              ) => add red_info.args_rmed
            }
            log! { @verb
              "{}: {}", conf.emph( preproc.name() ), red_info
            }
            conf.check_timeout() ? ;
            check_solved!() ;
            run! { @ $($tail)* Some(red_info) }
          } else {
            log! { @verb
              "{}: did nothing", conf.emph( preproc.name() )
            }
            run! { @ $($tail)* Some(red_info) }
          }
        } else {
          run! { @ $($tail)* None }
        }
      ) ;
    }

    preproc_dump!(
      self.instance =>
        format!("preproc_{:0>4}_original_instance", count),
        "Instance before pre-processing."
    ) ? ;
    profile!{
      |_profiler|
        "clause count original" => add self.instance.clauses().len()
    }
    profile!{
      |_profiler|
        "nl clause count original" => add {
          let mut count = 0 ;
          'clause_iter: for clause in self.instance.clauses() {
            for (_, argss) in clause.lhs_preds() {
              if argss.len() > 1 {
                count += 1 ;
                continue 'clause_iter
              }
            }
          }
          count
        }
    }
    profile!{
      |_profiler|
        "pred count original" => add {
          let mut count = 0 ;
          for pred in self.instance.pred_indices() {
            if ! self.instance.is_known(pred) {
              count += 1
            }
          }
          count
        }
    }
    profile!{
      |_profiler|
        "arg count original" => add {
          let mut args = 0 ;
          for info in self.instance.preds() {
            if ! self.instance.is_known(info.idx) {
              args += info.sig.len()
            }
          }
          args
        }
    }

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

      let changed = run! { s_one_rhs } ;

      let changed = run! { s_one_lhs } || changed ;

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

    // let max_clause_add = if conf.preproc.mult_unroll
    // && ! self.instance.clauses().is_empty() {
    //   let clause_count = self.instance.clauses().len() ;
    //   ::std::cmp::min(
    //     clause_count, (
    //       50. * ( clause_count as f64 ).log(2.)
    //     ).round() as usize
    //   )
    // } else {
    //   0
    // } ;


    if self.instance.split().is_none() && self.instance.clauses().len() > 20 {
      let biased_info = run!(biased_unroll info) ;
      if biased_info.non_zero() {
        run! { simplify } ;
      }

      let strict_neg_count = self.instance.strict_neg_clauses().fold(
        0, |acc, _| acc + 1
      ) ;
      if strict_neg_count <= 1 && conf.preproc.runroll {
        let info = run!( runroll info ) ;
        if info.non_zero() {
          run! { simplify } ;
        }
      }
    }



    // let strict_neg_count = self.instance.strict_neg_clauses().fold(
    //   0, |acc, _| acc + 1
    // ) ;

    // let (
    //   mut added, mut r_added,
    //   mut added_pre, mut r_added_pre,
    // ) = if conf.preproc.unroll {
    //   (
    //     0, 0, run!(runroll info).clause_diff(), run!(unroll info).clause_diff()
    //   )
    // } else if strict_neg_count <= 1
    // && self.instance.split().is_none() {
    //   // This is a special case, triggered one the first preproc run (split is
    //   // none) and if there's only one negative clause. In this case, force run
    //   // reverse unroll so that we can split later.
    //   (0, 0, run!(runroll info).clause_diff(), 0)
    // } else {
    //   (0, 0, 0, 0)
    // } ;


    // loop {
    //   added += added_pre ;
    //   r_added += r_added_pre ;

    //   if_verb! { 
    //     log_verb! {
    //       "{}: forward {} ({})", conf.emph("unrolling"), added, added_pre
    //     }
    //     log_verb! {
    //       "           bakward {} ({})", r_added, r_added_pre
    //     }
    //     log_verb! {
    //       "             total {} / {}", added + r_added, max_clause_add
    //     }
    //   }

    //   if (
    //     added_pre == 0 && r_added_pre == 0
    //   ) || added + r_added > max_clause_add {
    //     // (R)Unrolling is not producing anything anymore or has gone above the
    //     // threshold.
    //     break
    //   } else if added_pre == 0 || added > r_added {
    //     // Unrolling is stuck or has produced more clauses than runrolling.
    //     r_added_pre = run!(runroll info).clause_diff()
    //   } else {
    //     added_pre = run!(unroll info).clause_diff()
    //   }
    // }

    preproc_dump!(
      self.instance =>
        "preproc_0000_fixed_point",
        "Instance after reaching preproc fixed-point."
    ) ? ;

    profile!{
      |_profiler|
        "clause count    final" => add self.instance.clauses().len()
    }
    profile!{
      |_profiler|
        "nl clause count    final" => add {
          let mut count = 0 ;
          'clause_iter: for clause in self.instance.clauses() {
            for (_, argss) in clause.lhs_preds() {
              if argss.len() > 1 {
                count += 1 ;
                continue 'clause_iter
              }
            }
          }
          count
        }
    }

    profile!{
      |_profiler|
        "pred count    final" => add {
          let mut count = 0 ;
          for pred in self.instance.pred_indices() {
            if ! self.instance.is_known(pred) {
              count += 1
            }
          }
          count
        }
    }

    profile!{
      |_profiler|
        "arg count    final" => add {
          let mut args = 0 ;
          for info in self.instance.preds() {
            if ! self.instance.is_known(info.idx) {
              args += info.sig.len()
            }
          }
          args
        }
    }

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
  fn apply<'a>(
    & mut self, & mut PreInstance<'a>
  ) -> Res<RedInfo> ;
}


/// Calls `PredInstance::simplify_all`.
pub struct Simplify ;

impl RedStrat for Simplify {
  fn name(& self) -> & 'static str { "simplify" }

  fn new(_: & Instance) -> Self { Simplify }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    instance.simplify_all()
  }
}


/// Calls [`Instance::arg_reduce`][arg_reduce].
///
/// [arg_reduce]: ../instance/struct.Instance.html#method.arg_reduce
/// (Instance's arg_reduce method)
pub struct ArgRed {
  inner: ArgRedInner,
}

impl RedStrat for ArgRed {
  fn name(& self) -> & 'static str { "arg_reduce" }

  fn new(_: & Instance) -> Self {
    ArgRed {
      inner: ArgRedInner::new(),
    }
  }

  fn apply<'a>(
    & mut self, instance:& mut PreInstance<'a>
  ) -> Res<RedInfo> {
    let keep = self.inner.run(instance) ;
    instance.rm_args(keep)
  }
}






/// Works on predicates that appear in only one rhs.
///
/// # Restrictions
///
/// Unfolds a predicate `P` iff
///
/// - it appears in exactly one clause rhs, say in clause `C`
/// - `P` does not appear in the lhs of `C`
/// - the lhs of `C` has no top term relating the variables `vars` appearing in
///   the application of `P` and the other variables `other_vars` of the clause
/// - the predicate applications in the lhs of `C` do not mention `other_vars`
///
/// | This reduction does not run on:        |                           |
/// |:---------------------------------------|:--------------------------|
/// | `(p ...)    and ... => (p ...)`        | `p` appears in lhs        |
/// | `(v'' > v)  and ... => (p v (v' + 1))` | `v''` and `v` are related |
/// | `(p' v'' v) and ... => (p v (v' + 1))` | `p'` mentions `v''`       |
///
/// | But it runs on:                    | `p v_0 v_1 =`               |
/// |:-----------------------------------|:----------------------------|
/// | `(v > v'  + 2)        => (p v v')` | `(v_0 > v_1 + 2)`           |
/// | `(v > 0)              => (p 7 v )` | `(v_0 = 7) and (v_1 > 0)`   |
/// | `(v > 0)              => (p 7 v')` | `(v_0 = 7)`                 |
/// | `(v > 0)              => (p v v )` | `(v_0 = v_1) and (v_0 > 0)` |
/// | `(v > 0) and (v <= 0) => (p 7 v')` | `false` (by check-sat)      |
///
pub struct SimpleOneRhs {
  /// Predicates found to be equivalent to true, but not propagated yet.
  true_preds: PrdSet,
  /// Predicates found to be equivalent to false, but not propagated yet.
  false_preds: PrdSet,
  /// Predicates to propagate.
  preds: PrdHMap< Vec<TTerm> >,
}

impl RedStrat for SimpleOneRhs {
  fn name(& self) -> & 'static str { "simple_one_rhs" }

  fn new(_: & Instance) -> Self {
    SimpleOneRhs {
      true_preds: PrdSet::with_capacity(7),
      false_preds: PrdSet::with_capacity(7),
      preds: PrdHMap::with_capacity(7),
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut red_info = RedInfo::new() ;

    for pred in instance.pred_indices() {
      conf.check_timeout() ? ;

      if instance.clauses_of(pred).1.len() == 1 {

        let clause = * instance.clauses_of(
          pred
        ).1.iter().next().unwrap() ;
        log_debug! {
          "looking at {} ({}, {})",
          instance[pred],
          instance.clauses_of(pred).0.len(),
          instance.clauses_of(pred).1.len() ;
          "trying to unfold {}", instance[pred]
        }

        let res = {
          let (extraction, instance) = instance.extraction() ;

          if let Some((_this_pred, args)) = instance[clause].rhs() {
            debug_assert_eq!( pred, _this_pred ) ;

            // Does `pred` appear in the lhs?
            match instance[clause].lhs_preds().get(& pred) {
              Some(apps) if ! apps.is_empty() => {
                ExtractRes::SuccessFalse
              },
              _ => extraction.terms_of_rhs_app(
                false, instance, instance[clause].vars(),
                instance[clause].lhs_terms(), instance[clause].lhs_preds(),
                pred, args
              ) ?,
            }
          } else {
            bail!("inconsistent instance state")
          }
        } ;

        if res.is_failed() { continue }

        log! { @debug
          "from {}",
          instance.clauses()[clause].to_string_info( instance.preds() ) ?
        }

        log! { @verb
          "unfolding {}", conf.emph(& instance[pred].name)
        }

        use self::ExtractRes::* ;
        match res {
          Trivial => {
            log! { @ 4 "=> trivial" }
            red_info += instance.force_false(pred) ?
          },
          SuccessTrue => {
            log! { @ 4 "=> true" }
            red_info += instance.force_true(pred) ?
          },
          SuccessFalse => {
            log! { @ 4 "=> false" }
            red_info += instance.force_false(pred) ?
          },
          Success( (qvars, tterms) ) => {
            debug_assert! { qvars.is_empty() } ;
            if_log! { @4
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log! { @4
                    "=> ({} {})", instance[* pred], args
                  }
                }
              }
              for term in tterms.terms() {
                log! { @4 "  => {}", term }
              }
            }
            red_info += instance.force_pred_left(
              pred, qvars, tterms
            ) ?
          },
          // Failed is caught before this match.
          Failed => continue,
        }

        debug_assert! { instance.is_known(pred) }

        red_info.preds += 1
      }
    }

    Ok( red_info )
  }
}







/// Tries to reduce predicates that appear as an antecedent in exactly one
/// clause.
///
/// For a predicate `p`, if the clause in question is
///
/// ```bash
/// lhs(v_1, ..., v_n) and p(v_1, ..., v_n) => rhs(v_1, ..., v_n)
/// ```
///
/// then `p` is reduced to
///
/// ```bash
/// (not lhs(v_1, ..., v_n)) or rhs(v_1, ..., v_n)
/// ```
///
/// **iff** `p` is the only predicate application in the clause, `lhs` is sat
/// and `(not rhs)` is sat.
///
/// If `lhs` or `(not rhs)` is unsat, then the clause is dropped and `p` is
/// reduced to `true` since it does not appear as an antecedent anywhere
/// anymore.
pub struct SimpleOneLhs {
  /// Predicates found to be equivalent to true, but not propagated yet.
  true_preds: PrdSet,
  /// Predicates found to be equivalent to false, but not propagated yet.
  false_preds: PrdSet,
  /// Predicates to propagate.
  preds: PrdHMap< Vec<TTerm> >,
}

impl RedStrat for SimpleOneLhs {
  fn name(& self) -> & 'static str { "simple_one_lhs" }

  fn new(_: & Instance) -> Self {
    SimpleOneLhs {
      true_preds: PrdSet::with_capacity(7),
      false_preds: PrdSet::with_capacity(7),
      preds: PrdHMap::with_capacity(7),
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut red_info = RedInfo::new() ;

    for pred in instance.pred_indices() {
      conf.check_timeout() ? ;

      let clause_idx = {
        let mut lhs_clauses = instance.clauses_of(pred).0.iter() ;
        if let Some(clause) = lhs_clauses.next() {
          if lhs_clauses.next().is_none() {
            * clause
          } else {
            continue
          }
        } else {
          continue
        }
      } ;

      log! { @debug
        "looking at {} ({}, {})",
        instance[pred],
        instance.clauses_of(pred).0.len(),
        instance.clauses_of(pred).1.len(),
      }

      // Skip if the clause mentions this predicate more than once.
      if let Some( argss ) = instance[clause_idx].lhs_preds().get(& pred) {
        if argss.len() > 1 { continue }
      }

      log! { @debug
        "trying to unfold {}", instance[pred]
      }

      let res = {
        let (extraction, instance) = instance.extraction() ;

        let clause = & instance[clause_idx] ;
        // log_debug!{
        //   "from {}", clause.to_string_info( instance.preds() ) ?
        // }
        let args = if let Some(argss) = clause.lhs_preds().get(& pred) {
          let mut iter = argss.iter() ;
          let res = iter.next().unwrap() ;
          // Guaranteed by the check before the `log_debug`.
          debug_assert!( iter.next().is_none() ) ;
          res
        } else {
          bail!("inconsistent instance state")
        } ;

        // Is the rhs an application of `pred`?
        match clause.rhs() {
          Some((p, _)) if p == pred => {
            ExtractRes::SuccessTrue
          },
          _ => extraction.terms_of_lhs_app(
            false, instance, clause.vars(),
            clause.lhs_terms(), clause.lhs_preds(), clause.rhs(),
            pred, args
          ) ?,
        }
      } ;

      if res.is_failed() { continue }

      log! { @debug
        "from {}",
        instance.clauses()[clause_idx].to_string_info( instance.preds() ) ?
      }

      // instance.forget_clause(clause_idx) ? ;
      // red_info.clauses_rmed += 1 ;

      // log_verb!{ "  instance:\n{}", instance.to_string_info( () ) ? }

      log! { @verb
        "unfolding {}", conf.emph(& instance[pred].name)
      }
      use self::ExtractRes::* ;
      match res {
        SuccessTrue => {
          log! { @4 "=> true" }
          red_info += instance.force_true(pred) ?
        },
        SuccessFalse => {
          log! { @4 "=> false" }
          red_info += instance.force_false(pred) ?
        },
        Trivial => {
          log! { @4 "=> trivial" }
          red_info += instance.force_true(pred) ?
        },
        Success((qualfed, pred_app, tterms)) => {
          debug_assert! { qualfed.is_empty() }
          if pred_app.is_none() && tterms.is_empty() {
            log! { @4 "=> false" }
            red_info += instance.force_false(pred) ?
          } else {
            if_log!{ @4
              log!{ @4"  => (or" }
              if let Some((pred, ref args)) = pred_app {
                let mut s = format!("({}", instance[pred]) ;
                for arg in args.iter() {
                  s = format!("{} {}", s, arg)
                }
                log! { @4 "    {})", s }
              }
              log! { @4
                "    (not" ;
                "      (and"
              }
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log! { @4
                    "        ({} {})", instance[* pred], args
                  }
                }
              }
              for term in tterms.terms() {
                log!{ @4
                  "        {}", term
                }
              }
            }
            red_info += instance.force_pred_right(
              pred, qualfed, pred_app, tterms
            ) ?
          }

          instance.check("after unfolding") ?
        },
        // Failed is caught before this match.
        Failed => continue,
      }

      debug_assert! { instance.is_known(pred) }

      red_info.preds += 1
    }

    Ok( red_info )
  }
}






/// Works on predicates that appear in only one rhs.
///
/// Only works on predicates that need qualifiers to be reduced, complements
/// `SimpleOneRhs`.
///
/// If a predicate `p` appears as a rhs in only in one clause
///
/// ```bash
/// lhs(v_1, ..., v_n, v_n+1, ..., v_k) => p(v_1, ..., v_n)
/// ```
///
/// then it is forced to
///
/// ```bash
/// p(v_1, ..., v_n) = exists (v_n+1, ..., v_k) . lhs(v_1, ..., v_k)
/// ```
pub struct OneRhs {
  /// Stores new variables discovered as we iterate over the lhs of clauses.
  new_vars: VarSet,
}

impl RedStrat for OneRhs {
  fn name(& self) -> & 'static str { "one_rhs" }

  fn new(_: & Instance) -> Self {
    OneRhs {
      new_vars: VarSet::with_capacity(17)
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    debug_assert!( self.new_vars.is_empty() ) ;
    let mut red_info = RedInfo::new() ;

    'all_preds: for pred in instance.pred_indices() {
      conf.check_timeout() ? ;

      if instance.clauses_of(pred).1.len() == 1 {
        log! { @4
          "looking at {} ({}, {})",
          instance[pred],
          instance.clauses_of(pred).0.len(),
          instance.clauses_of(pred).1.len(),
        }
        let clause =
          * instance.clauses_of(pred).1.iter().next().unwrap() ;

        if instance.clauses_of(pred).0.contains(& clause) {
        // || instance[clause].lhs_pred_apps_len() > 1 {
          continue 'all_preds
        }

        log!{ @5
          "trying to unfold {}", instance[pred]
        }

        let res = {
          let (extraction, instance) = instance.extraction() ;

          if let Some((_this_pred, args)) = instance[clause].rhs() {
            debug_assert_eq!( pred, _this_pred ) ;

            // Does `pred` appear in the lhs?
            match instance[clause].lhs_preds().get(& pred) {
              Some(apps) if ! apps.is_empty() => {
                ExtractRes::SuccessFalse
              },
              _ => extraction.terms_of_rhs_app(
                true, instance, instance[clause].vars(),
                instance[clause].lhs_terms(), instance[clause].lhs_preds(),
                pred, args
              ) ?,
            }
          } else {
            bail!("inconsistent instance state")
          }
        } ;

        if res.is_failed() {
          log! { @debug "  skipping" }
          continue
        }

        log! { @debug
          "from {}",
          instance.clauses()[clause].to_string_info( instance.preds() ) ?
        }

        log_verb!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        use self::ExtractRes::* ;
        match res {
          Trivial => {
            log_verb!("  => trivial") ;
            red_info += instance.force_false(pred) ?
          },
          SuccessTrue => {
            log_verb!("  => true") ;
            red_info += instance.force_true(pred) ? ;
          },
          SuccessFalse => {
            log_verb!("  => false") ;
            red_info += instance.force_false(pred) ? ;
          },
          Success( (qvars, tterms) ) => {
            if_debug! {
              log! { @debug
                "  {} quantified variables", qvars.len()
              }
              for (var, typ) in & qvars {
                log! {  @debug "  - v_{}: {}", var, typ }
              }
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log! { @debug "  => ({} {})", instance[* pred], args }
                }
              }
              for term in tterms.terms() {
                log! { @debug "  => {}", term }
              }
            }
            red_info += instance.force_pred_left(
              pred, qvars, tterms
            ) ? ;


            instance.check("after unfolding") ?
          },
          // Failed is caught before this match, and false is not possible for
          // the function generating `res`.
          Failed => unreachable!(),
        }

        debug_assert! { instance.is_known(pred) }

        red_info.preds += 1
      }
    }

    Ok( red_info )
  }
}





/// Tries to reduce predicates that appear as an antecedent in exactly one
/// clause.
///
/// For a predicate `p`, if the clause in question is
///
/// ```bash
/// lhs(v_1, ..., v_n) and p(v_1, ..., v_n) => rhs(v_1, ..., v_n)
/// ```
///
/// then `p` is reduced to
///
/// ```bash
/// (not lhs(v_1, ..., v_n)) or rhs(v_1, ..., v_n)
/// ```
///
/// **iff** `p` is the only predicate application in the clause, `lhs` is sat
/// and `(not rhs)` is sat.
///
/// If `lhs` or `(not rhs)` is unsat, then the clause is dropped and `p` is
/// reduced to `true` since it does not appear as an antecedent anywhere
/// anymore.
pub struct OneLhs {
  /// Predicates found to be equivalent to true, but not propagated yet.
  true_preds: PrdSet,
  /// Predicates found to be equivalent to false, but not propagated yet.
  false_preds: PrdSet,
  /// Predicates to propagate.
  preds: PrdHMap< Vec<TTerm> >,
}

impl RedStrat for OneLhs {
  fn name(& self) -> & 'static str { "one_lhs" }

  fn new(_: & Instance) -> Self {
    OneLhs {
      true_preds: PrdSet::with_capacity(7),
      false_preds: PrdSet::with_capacity(7),
      preds: PrdHMap::with_capacity(7),
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut red_info = RedInfo::new() ;

    for pred in instance.pred_indices() {
      conf.check_timeout() ? ;

      let clause_idx = {
        let mut lhs_clauses = instance.clauses_of(pred).0.iter() ;
        if let Some(clause) = lhs_clauses.next() {
          if lhs_clauses.next().is_none() {
            * clause
          } else {
            continue
          }
        } else {
          continue
        }
      } ;

      log_debug! {
        "looking at {} ({}, {})",
        instance[pred],
        instance.clauses_of(pred).0.len(),
        instance.clauses_of(pred).1.len(),
      }

      // Skip if the clause mentions this predicate more than once.
      if let Some( argss ) = instance[clause_idx].lhs_preds().get(& pred) {
        log_debug! { "skipping {}, more than one application", instance[pred] }
        if argss.len() > 1 { continue }
      }

      log_debug!{
        "trying to unfold {}", instance[pred]
      }

      let res = {
        let (extraction, instance) = instance.extraction() ;

        let clause = & instance[clause_idx] ;
        // log_debug!{
        //   "from {}", clause.to_string_info( instance.preds() ) ?
        // }
        let args = if let Some(argss) = clause.lhs_preds().get(& pred) {
          let mut iter = argss.iter() ;
          let res = iter.next().unwrap() ;
          // Guaranteed by the check before the `log_debug`.
          debug_assert!( iter.next().is_none() ) ;
          res
        } else {
          bail!("inconsistent instance state")
        } ;

        // Is the rhs an application of `pred`?
        match clause.rhs() {
          Some((p, _)) if p == pred => {
            ExtractRes::SuccessTrue
          },
          _ => extraction.terms_of_lhs_app(
            true, instance, clause.vars(),
            clause.lhs_terms(), clause.lhs_preds(), clause.rhs(),
            pred, args
          ) ?,
        }
      } ;

      if res.is_failed() { continue }

      log_debug!{
        "from {}",
        instance.clauses()[clause_idx].to_string_info( instance.preds() ) ?
      }

      // instance.forget_clause(clause_idx) ? ;
      // red_info.clauses_rmed += 1 ;

      // log_verb!{ "  instance:\n{}", instance.to_string_info( () ) ? }

      log_verb!{ "  unfolding {}", conf.emph(& instance[pred].name) }
      use self::ExtractRes::* ;
      match res {
        SuccessTrue => {
          log! { @verb "  => true" }
          red_info += instance.force_true(pred) ?
        },
        SuccessFalse => {
          log! { @verb "  => false" }
          red_info += instance.force_false(pred) ?
        },
        Trivial => {
          log! { @verb "  => trivial" }
          red_info += instance.force_true(pred) ?
        },
        Success((qvars, pred_app, tterms)) => {
          if_log! { @debug
            log! { @ debug "{} quantified variables", qvars.len() }
            for (var, typ) in & qvars {
              log! { @ debug "- v_{}: {}", var, typ }
            }
            log! { @ debug  "=> (or" }
            if let Some((pred, ref args)) = pred_app {
              let mut s = format!("({}", instance[pred]) ;
              for arg in args.iter() {
                s = format!("{} {}", s, arg)
              }
              log! { @ debug  "  {})", s }
            }
            log! { @ debug  "  (not" }
            log! { @ debug  "    (and" }
            for (pred, args) in tterms.preds() {
              let mut s = format!("({}", instance[* pred]) ;
              for arg in args {
                s = format!("{} {}", s, arg)
              }
              log! { @debug "      {})", s }
            }
            for term in tterms.terms() {
              log! { @debug "      {}", term }
            }
            log! { @debug "    )" }
            log! { @debug "  )" }
          }
          red_info += instance.force_pred_right(
            pred, qvars, pred_app, tterms
          ) ? ;

          instance.check("after unfolding") ?
        },
        // Failed is caught before this match.
        Failed => unreachable!(),
      }

      debug_assert! { instance.is_known(pred) }

      red_info.preds += 1 ;
    }

    Ok( red_info )
  }
}



/// Detects cycles and keeps a minimal set of predicates to infer.
pub struct CfgRed {
  /// Internal counter for log files.
  cnt: usize,
  /// Upper bound computed once at the beginning to avoid a progressive
  /// blow-up.
  upper_bound: usize,
  /// Graph, factored to avoid reallocation.
  graph: Graph,
}

impl RedStrat for CfgRed {
  fn name(& self) -> & 'static str { "cfg_red" }

  fn new(instance: & Instance) -> Self {
    CfgRed {
      cnt: 0,
      upper_bound: {
        let clause_count = instance.clauses().len() ;
        let adjusted = 50. * ( clause_count as f64 ).log(2.) ;
        ::std::cmp::min(
          clause_count, (
            adjusted
          ).round() as usize
        )
      },
      graph: Graph::new(instance),
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    // use std::time::Instant ;
    // use common::profiling::DurationExt ;

    let mut total_info = RedInfo::new() ;

    loop {

      let mut info = RedInfo::new() ;

      // let start = Instant::now() ;
      self.graph.setup(instance) ;
      // let setup_duration = Instant::now() - start ;
      // println!("setup time: {}", setup_duration.to_str()) ;

      self.graph.check(& instance) ? ;

      // let start = Instant::now() ;
      let mut to_keep = self.graph.break_cycles(instance) ? ;
      // let breaking_duration = Instant::now() - start ;
      // println!("breaking time: {}", breaking_duration.to_str()) ;

      self.graph.to_dot(
        & instance, format!("{}_pred_dep_b4", self.cnt), & to_keep
      ) ? ;

      let pred_defs = self.graph.inline(
        instance, & mut to_keep, self.upper_bound
      ) ? ;

      if pred_defs.is_empty() { break }

      info.preds += pred_defs.len() ;

      self.graph.check(& instance) ? ;
      if_log! { @verb
        log! { @verb "inlining {} predicates", pred_defs.len() }
        for (pred, _) in & pred_defs {
          log! { @verb "  {}", instance[* pred] }
        }
      }

      if pred_defs.len() == instance.active_pred_count() {
        let (is_sat, this_info) = instance.force_all_preds(pred_defs) ? ;
        info += this_info ;
        if ! is_sat {
          unsat!("by preprocessing (all predicates resolved but unsat)")
        } else {
          total_info += info ;
          break
        }
      }

      // Remove all clauses leading to the predicates we just inlined.
      for (pred, def) in pred_defs {
        if instance.is_known(pred) {
          continue
        }

        conf.check_timeout() ? ;
        info += instance.rm_rhs_clauses_of(pred) ? ;

        if_log! { @4
          let mut s = format!("{}(", instance[pred]) ;
          let mut is_first = true ;
          for (var, typ) in instance[pred].sig.index_iter() {
            if ! is_first {
              s.push_str(", ")
            } else {
              is_first = false
            }
            s.push_str( & var.default_str() ) ;
            s.push_str(& format!(": {}", typ)) ;
          }
          log! { @4 "{}) = (or", s }
          for & (ref qvars, ref conj) in & def {
            let (suff, pref) = if qvars.is_empty() { (None, "  ") } else {
              let mut s = "  (exists".to_string() ;
              for (var, typ) in qvars {
                s.push_str(" (") ;
                s.push_str( & var.default_str() ) ;
                s.push_str( & format!(" {})", typ) )
              }
              log! { @4 "{}", s }
              (Some("  )"), "    ")
            } ;
            log! { @4 "{}(and", pref }
            for term in conj.terms() {
              log! { @4 "{}  {}", pref, term }
            }
            for (pred, argss) in conj.preds() {
              for args in argss {
                log! { @4 "{}  ({} {})", pref, instance[* pred], args }
              }
            }
            log! { @4 "{})", pref }
            if let Some(suff) = suff {
              log! { @4 "{}", suff }
            }
          }
          log! { @4 ")" }
        }

        log! { @4 "  unfolding {}", instance[pred] }

        info += instance.force_dnf_left(pred, def) ? ;

        preproc_dump!(
          instance =>
            format!("after_force_dnf_left_on_{}", pred),
            "Instance after reaching preproc fixed-point."
        ) ? ;
      }

      if conf.preproc.dump_pred_dep {
        self.graph.setup(instance) ;
        self.graph.check(& instance) ? ;
        self.graph.to_dot(
          & instance, format!("{}_pred_dep_reduced", self.cnt), & to_keep
        ) ? ;
      }

      self.cnt += 1 ;

      if info.non_zero() {
        total_info += info
      } else {
        break
      }

    }

    Ok(total_info)
  }
}


/// Unrolls negative and positive constraints with a bias.
///
/// # TODO
///
/// - when creating new clauses for `p`, remember that `p` has new pos/neg
///   definitions ; then, only check clauses that mention new predicates (old
///   ones have already been tried)
pub struct BiasedUnroll {
  /// Predicates appearing in positive clauses.
  in_pos_clauses: PrdSet,
  /// Predicates appearing in negative clauses.
  in_neg_clauses: PrdSet,
  /// Predicates not appearing in positive clauses.
  not_in_pos_clauses: PrdSet,
  /// Predicates not appearing in negative clauses.
  not_in_neg_clauses: PrdSet,
  /// Positive definitions retrieved from positive clauses.
  pos_defs: PrdHMap< Vec<(Quantfed, TermSet)> >,
  /// Negative definitions retrieved from negative clauses.
  neg_defs: PrdHMap< Vec<(Quantfed, TermSet)> >,
  /// 
  pos_new_preds: PrdHMap<(PrdSet, PrdSet)>,
  neg_new_preds: PrdHMap<(PrdSet, PrdSet)>,
  /// Maximum number of new clauses we can create by predicate.
  max_new_clauses: usize,
}

impl BiasedUnroll {

  /// Adds a positive definition for something.
  fn add_pos_def_for(
    & mut self, pred: PrdIdx, def: (Quantfed, TermSet)
  ) {
    let defs = self.pos_defs.entry(pred).or_insert_with(|| vec![]) ;
    if defs.iter().all( |d| d != & def ) {
      defs.push(def)
    }
  }

  /// Adds a negative definition for something.
  fn add_neg_def_for(
    & mut self, pred: PrdIdx, def: (Quantfed, TermSet)
  ) {
    let defs = self.neg_defs.entry(pred).or_insert_with(|| vec![]) ;
    if defs.iter().all( |d| d != & def ) {
      defs.push(def)
    }
  }



  /// Prints itself.
  #[allow(dead_code)]
  fn print(& self, instance: & Instance) {
    println!("pos {{") ;
    for pred in & self.in_pos_clauses {
      println!("  + {}", instance[* pred])
    }
    for pred in & self.not_in_pos_clauses {
      println!("  - {}", instance[* pred])
    }
    println!("}}") ;
    println!("neg {{") ;
    for pred in & self.in_neg_clauses {
      println!("  + {}", instance[* pred])
    }
    for pred in & self.not_in_neg_clauses {
      println!("  - {}", instance[* pred])
    }
    println!("}}") ;

    for (pred, defs) in & self.pos_defs {
      if ! defs.is_empty() {
        println!("+ {} {{", instance[* pred]) ;
        for (qvars, terms) in defs {
          let (pref, end) = if qvars.is_empty() {
            ("", "")
          } else {
            print!("  (exists (") ;
            for (qvar, typ) in qvars {
              print!(" ({} {})", qvar.default_str(), typ)
            }
            println!(" )") ;
            ("  ", "  )\n")
          } ;
          print!("  {}(and", pref) ;
          for term in terms {
            print!(" {}", term)
          }
          println!(")") ;
          print!("{}", end)
        }
        println!("}}")
      }
    }

    for (pred, defs) in & self.neg_defs {
      if ! defs.is_empty() {
        println!("- {} {{", instance[* pred]) ;
        for (qvars, terms) in defs {
          let (pref, end) = if qvars.is_empty() {
            ("", "")
          } else {
            print!("  (forall (") ;
            for (qvar, typ) in qvars {
              print!(" ({} {})", qvar.default_str(), typ)
            }
            println!(" )") ;
            ("  ", "  )\n")
          } ;
          print!("  {}(not (and", pref) ;
          for term in terms {
            print!(" {}", term)
          }
          println!(") )") ;
          print!("{}", end)
        }
        println!("}}")
      }
    }

    println!("pos_new_preds {{") ;
    for (pred, (pos, neg)) in & self.pos_new_preds {
      print!("  {} +{{", instance[* pred]) ;
      for p in pos {
        print!(" {}", instance[* p])
      }
      print!(" }}, -{{") ;
      for p in neg {
        print!(" {}", instance[* p])
      }
      println!(" }}")
    }
    println!("}}") ;

    println!("neg_new_preds {{") ;
    for (pred, (pos, neg)) in & self.neg_new_preds {
      print!("  {} +{{", instance[* pred]) ;
      for p in pos {
        print!(" {}", instance[* p])
      }
      print!(" }}, -{{") ;
      for p in neg {
        print!(" {}", instance[* p])
      }
      println!(" }}")
    }
    println!("}}") ;
    println!() ;
    println!() ;
    println!() ;
  }


  /// Sets up the unroller by scanning the instance.
  ///
  /// Returns `true` if there's nothing to do.
  fn setup<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<bool> {
    self.max_new_clauses = ::std::cmp::min(
      10, instance.clauses().len() / 20
    ) ;

    for (pred, _) in instance.preds().index_iter() {
      if instance.is_known(pred) { continue }
      let (lhs_clauses, rhs_clauses) = instance.clauses_of(pred) ;

      let mut in_pos = false ;
      for clause in rhs_clauses {
        if instance[* clause].lhs_pred_apps_len() == 0 {
          in_pos = true ;
          break
        }
      }
      if in_pos {
        let is_new = self.in_pos_clauses.insert(pred) ;
        debug_assert! { is_new }
      } else {
        let is_new = self.not_in_pos_clauses.insert(pred) ;
        debug_assert! { is_new }
      }

      let mut in_neg = false ;
      for clause in lhs_clauses {
        if instance[* clause].rhs().is_none()
        && instance[* clause].lhs_pred_apps_len() == 1 {
          in_neg = true ;
          break
        }
      }
      if in_neg {
        let is_new = self.in_neg_clauses.insert(pred) ;
        debug_assert! { is_new }
      } else {
        let is_new = self.not_in_neg_clauses.insert(pred) ;
        debug_assert! { is_new }
      }
    }

    let do_nothing = self.not_in_pos_clauses.is_empty(
    ) && self.not_in_neg_clauses.is_empty() ;

    if ! do_nothing {
      let (extractor, instance) = instance.extraction() ;
      self.retrieve_all_pos_defs(instance, extractor) ? ;
      self.retrieve_all_neg_defs(instance, extractor) ? ;

      let pos_neg = (
        self.in_pos_clauses.clone(), self.in_neg_clauses.clone()
      ) ;

      for pred in & self.not_in_pos_clauses {
        self.pos_new_preds.entry(* pred).or_insert_with(
          || pos_neg.clone()
        ) ;
      }

      for pred in & self.not_in_neg_clauses {
        self.neg_new_preds.entry(* pred).or_insert_with(
          || pos_neg.clone()
        ) ;
      }
    }

    Ok(do_nothing)
  }


  /// Retrieves a predicate positive definition from some clause.
  ///
  /// The clause has to be positive.
  pub fn retrieve_pos_def(
    & mut self, instance: & Instance, extractor: & mut ExtractionCxt,
    pred: PrdIdx, clause: & Clause,
  ) -> Res<()> {
    // Check what we're asked to do makes sense.
    let args = if let Some((p, args)) = clause.rhs() {
      if p != pred {
        bail!(
          "trying to retrieve_pos for {} in clause with different rhs",
          instance[pred]
        )
      }
      args
    } else {
      bail!(
        "trying to retrieve_pos for {} in non-positive clause (rhs)",
        instance[pred]
      )
    } ;
    if ! clause.lhs_preds().is_empty() {
      bail!(
        "trying to retrieve_pos for {} in non-positive clause (lhs)",
        instance[pred]
      )
    }

    // println!(
    //   "from clause {}", clause.to_string_info(instance.preds()).unwrap()
    // ) ;

    match extractor.terms_of_rhs_app(
      true, instance, clause.vars(),
      clause.lhs_terms(), clause.lhs_preds(),
      pred, args
    ) ? {
      ExtractRes::Failed => bail!(
        "term extraction failed for {}", instance[pred]
      ),
      ExtractRes::Trivial |
      ExtractRes::SuccessTrue |
      ExtractRes::SuccessFalse => bail!(
        "unexpected result for term extraction for {} (false)",
        instance[pred]
      ),
      ExtractRes::Success((qvars, tterms)) => {
        let (terms, preds) = tterms.destroy() ;
        debug_assert! { preds.is_empty() }
        self.add_pos_def_for(pred, (qvars, terms))
      },
    }

    Ok(())
  }

  /// Retrieves all the partial positive definitions for some predicate.
  fn retrieve_pos_defs(
    & mut self, instance: & Instance, extractor: & mut ExtractionCxt,
    pred: PrdIdx,
  ) -> Res<usize> {
    log! {
      @verb "retrieving positive partial definitions for {}",
      conf.emph(& instance[pred].name)
    }
    let mut count = 0 ;
    for clause in instance.clauses_of(pred).1 {
      let clause = & instance[* clause] ;
      if clause.lhs_preds().is_empty() {
        self.retrieve_pos_def(instance, extractor, pred, clause) ? ;
        count += 1
      }
    }
    Ok(count)
  }

  /// Retrieves all partial positive definitions.
  fn retrieve_all_pos_defs(
    & mut self, instance: & Instance, extractor: & mut ExtractionCxt
  ) -> Res<()> {
    log! { @4 "retrieve all positive definitions" }
    for pred in self.in_pos_clauses.clone() {
      log! { @4 "-> {}", instance[pred] }
      let count = self.retrieve_pos_defs(instance, extractor, pred) ? ;
      if count == 0 {
        bail!("failed to retrieve positive definition for {}", instance[pred])
      }
    }
    Ok(())
  }


  /// Retrieves a predicate negative definition from some clause.
  ///
  /// The clause has to be strictly negative.
  pub fn retrieve_neg_def(
    & mut self, instance: & Instance, extractor: & mut ExtractionCxt,
    pred: PrdIdx, clause: & Clause
  ) -> Res<()> {
    // Check what we're asked to do makes sense.
    if clause.rhs().is_some() {
      bail! (
        "trying to retrieve_neg for {} in non-negative clause (rhs)",
        instance[pred]
      )
    }
    let args = {
      let mut preds = clause.lhs_preds().iter() ;
      let mut argss = if let Some((p, argss)) = preds.next() {
        debug_assert_eq! { p, & pred }
        if preds.next().is_some() {
          bail!(
            "trying to retrieve_neg for {} in a non-strict clause (preds)",
            instance[pred]
          )
        }
        argss.iter()
      } else {
        bail!(
          "trying to retrieve_neg for {} in empty clause",
          instance[pred]
        )
      } ;

      if let Some(args) = argss.next() {
        debug_assert! { argss.next().is_none() }
        args
      } else {
        bail!(
          "trying to retrieve_neg for {} in a non-strict clause (argss)"
        )
      }
    } ;

    // println!(
    //   "from clause {}", clause.to_string_info(instance.preds()).unwrap()
    // ) ;

    match extractor.terms_of_lhs_app(
      true, instance, clause.vars(),
      clause.lhs_terms(), clause.lhs_preds(),
      None,
      pred, args
    ) ? {
      ExtractRes::Failed => bail!(
        "term extraction failed for {}", instance[pred]
      ),
      ExtractRes::Trivial |
      ExtractRes::SuccessTrue |
      ExtractRes::SuccessFalse => bail!(
        "unexpected result for term extraction for {} (false)",
        instance[pred]
      ),
      ExtractRes::Success((qvars, rhs, tterms)) => {
        debug_assert! { rhs.is_none() }
        let (terms, preds) = tterms.destroy() ;
        debug_assert! { preds.is_empty() }
        let mut neg_terms = TermSet::new() ;
        for term in terms {
          neg_terms.insert(term) ;
        }
        self.add_neg_def_for(pred, (qvars, neg_terms))
      },
    }

    Ok(())
  }

  /// Retrieves all the partial negative definitions for some predicate.
  fn retrieve_neg_defs(
    & mut self, instance: & Instance, extractor: & mut ExtractionCxt,
    pred: PrdIdx,
  ) -> Res<usize> {
    log! {
      @verb "retrieving negative partial definitions for {}",
      conf.emph(& instance[pred].name)
    }
    let mut count = 0 ;
    for clause in instance.clauses_of(pred).0 {
      let clause = & instance[* clause] ;
      if clause.lhs_preds().len() == 1
      && clause.rhs().is_none()
      && clause.lhs_preds().iter().next().map(
        |(_, argss)| argss.len() == 1
      ).unwrap_or( false ) {
        self.retrieve_neg_def(instance, extractor, pred, clause) ? ;
        count += 1
      }
    }
    Ok(count)
  }

  /// Retrieves all partial negative definitions.
  fn retrieve_all_neg_defs(
    & mut self, instance: & Instance, extractor: & mut ExtractionCxt,
  ) -> Res<()> {
    for pred in self.in_neg_clauses.clone() {
      let count = self.retrieve_neg_defs(instance, extractor, pred) ? ;
      if count == 0 {
        bail!("failed to retrieve negative definition for {}", instance[pred])
      }
    }
    Ok(())
  }




  /// Forces some terms in a clause by inserting a predicate application.
  ///
  /// `terms` is understood as a conjunction.
  fn insert_terms(
    & self, clause: & mut Clause, args: & VarTerms,
    qvars: & Quantfed, terms: & TermSet,
  ) -> Res<()> {
    // Generate fresh variables for the clause if needed.
    let qual_map = clause.fresh_vars_for(qvars) ;

    for term in terms {
      if let Some((term, _)) = term.subst_total( & (args, & qual_map) ) {
        clause.insert_term(term) ;
      } else {
        bail!("error during total substitution in `insert_terms`")
      }
    }

    Ok(())
  }





  /// Tries to generate some positive clauses for a predicate.
  fn generate_pos_clauses_for<'a>(
    & mut self, pred: PrdIdx, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    let mut info = RedInfo::new() ;

    'all_clauses: for rhs_clause in instance.clauses_of(pred).1.clone() {
      let mut one_pred_is_new = false ;

      let mut estimation = 1 ;

      for (p, argss) in instance[rhs_clause].lhs_preds() {
        if let Some(defs) = self.pos_defs.get(p) {
          for _ in argss {
            estimation *= defs.len() ;
            if estimation > self.max_new_clauses {
              continue 'all_clauses
            }
          }
        } else {
          continue 'all_clauses
        }

        if let Some((pos, _)) = self.pos_new_preds.get(& pred) {
          if pos.contains(p) {
            one_pred_is_new = true
          }
        }
      }
      if ! one_pred_is_new {
        continue 'all_clauses
      }

      log! { @4
        "generating positive clause(s) for {} from {} ({})",
        instance[pred],
        instance[rhs_clause].to_string_info( instance.preds() ) ?,
        estimation
      }

      let mut nu_clauses = vec![] ;

      scoped! {

        let mut clause = instance[rhs_clause].clone() ;

        let mut lhs_preds: Vec<_> = clause.drain_lhs_preds().collect() ;
        let mut map = Vec::with_capacity( lhs_preds.len() ) ;

        for (pred, argss) in & lhs_preds {
          let mut arg_map = Vec::with_capacity( argss.len() ) ;

          if let Some(defs) = self.pos_defs.get(pred) {
            for args in argss {
              arg_map.push( (args, 0) )
            }

            map.push( (pred, defs, arg_map) )
          } else {
            bail!("no definition for {} (positive, lhs)", instance[* pred])
          }
        }

        macro_rules! map_inc {
          () => ({
            let mut done = true ;
            'all_apps: for & mut (_, defs, ref mut argss) in & mut map {
              for (_, ref mut index) in argss {
                * index += 1 ;
                if * index < defs.len() {
                  done = false ;
                  break 'all_apps
                } else {
                  * index = 0
                }
              }
            }
            done
          })
        }

        let mut done = false ;
        while ! done {
          let mut clause = clause.clone() ;

          for (_, defs, argss) in & map {
            for (args, index) in argss {
              self.insert_terms(
                & mut clause, args, & defs[* index].0, & defs[* index].1
              ) ?
            }
          }

          if let Some(trivial) = instance.is_this_clause_trivial(
            & mut clause
          ) ? {
            if ! trivial {
              nu_clauses.push(clause)
            }
          } else {
            unimplemented!("unsat in biased unrolling")
          }

          done = map_inc!()
        }

      }

      for mut clause in nu_clauses {
        clause.from_unrolling = true ;
        if let Some(index) = instance.push_clause(clause) ? {
          let (extractor, instance) = instance.extraction() ;
          self.retrieve_pos_def(
            instance, extractor, pred, & instance[index]
          ) ? ;
          info.clauses_added += 1
        }
      }
    }

    Ok(info)
  }





  /// Tries to generate a negative clause for a predicate.
  fn generate_neg_clauses_for<'a>(
    & mut self, pred: PrdIdx, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    // self.print(instance) ;

    let mut info = RedInfo::new() ;

    'all_clauses: for lhs_clause in instance.clauses_of(pred).0.clone() {
      let mut one_pred_is_new = false ;

      let mut estimation = 1 ;

      if let Some((p, _)) = instance[lhs_clause].rhs() {
        if let Some(defs) = self.neg_defs.get(& p) {
          estimation *= defs.len() ;
          if estimation > self.max_new_clauses {
            continue 'all_clauses
          }
        } else {
          continue 'all_clauses
        }
        if let Some((_, neg)) = self.neg_new_preds.get(& pred) {
          if neg.contains(& p) {
            one_pred_is_new = true
          }
        }
      }

      for (p, argss) in instance[lhs_clause].lhs_preds() {
        if * p == pred {
          if argss.len() == 1 {
            ()
          } else if let Some(defs) = self.pos_defs.get(p) {
            estimation *= defs.len() ;
            if estimation > self.max_new_clauses {
              continue 'all_clauses
            }
          } else {
            continue 'all_clauses
          }
        } else if let Some(defs) = self.pos_defs.get(p) {
          for _ in argss {
            estimation *= defs.len() ;
            if estimation > self.max_new_clauses {
              continue 'all_clauses
            }
          }
        } else {
          // log! { @6 "{} not in pos clauses", instance[* p] }
          continue 'all_clauses
        }

        if let Some((pos, _)) = self.neg_new_preds.get(& pred) {
          if pos.contains(p) {
            one_pred_is_new = true
          }
        }
      }

      // log! { @6 "one pred new: {}", one_pred_is_new }

      if ! one_pred_is_new {
        continue 'all_clauses
      }

      log! { @4
        "generating negative clause(s) for {} from {}",
        instance[pred],
        instance[lhs_clause].to_string_info( instance.preds() ) ?
      }

      let mut nu_clauses = vec![] ;

      scoped! {

        let mut clause = instance[lhs_clause].clone() ;

        let mut this_pred = None ;
        let mut lhs_preds: Vec<_> = clause.drain_lhs_preds().collect() ;
        let rhs_pred = clause.unset_rhs() ;

        let mut map = Vec::with_capacity(
          lhs_preds.len()
        ) ;

        for (p, argss) in lhs_preds {
          let mut arg_map = Vec::with_capacity( argss.len() ) ;

          if let Some(defs) = self.pos_defs.get(& p) {
            for args in argss {
              arg_map.push( (args, 0) )
            }

            if p == pred {
              this_pred = Some((defs, arg_map))
            } else {
              map.push( (p, defs, arg_map) )
            }
          } else if p == pred {
            debug_assert_eq! { argss.len(), 1 }
            let is_new = clause.insert_pred_app(
              pred, argss.into_iter().next().unwrap()
            ) ;
            debug_assert! { is_new }
          } else {
            bail!("no definition for {} (negative, lhs)", instance[p])
          }
        }

        if let Some((pred, args)) = rhs_pred {
          if let Some(defs) = self.neg_defs.get(& pred) {
            map.push( (pred, defs, vec![ (args, 0) ]) )
          } else {
            bail!("no definition for {} (negative, rhs)", instance[pred])
          }
        }

        let mut active_lhs_pred_app = 0 ;

        macro_rules! map_inc {
          () => ({
            let mut done = true ;
            for & mut (_, defs, ref mut argss) in & mut map {
              map_inc!(@argss done, defs, argss ; true) ;
              if ! done {
                break
              }
            }

            // println!("inc: {}", done) ;

            if done {
              if let Some(
                & mut (defs, ref mut argss)
              ) = this_pred.as_mut() {
                let argss_len = argss.len() ;
                if active_lhs_pred_app < argss_len {
                  let mut index = 0 ;
                  map_inc!(
                    @argss done, defs, argss ; {
                      let iff = index != active_lhs_pred_app ;
                      index += 1 ;
                      iff
                    }
                  )
                }

                if done {
                  active_lhs_pred_app += 1 ;
                  done = active_lhs_pred_app >= argss_len
                }
              }
            }

            done
          }) ;
          (@argss $done:ident, $defs:expr, $argss:expr ; $iff:expr) => (
            for (_, ref mut index) in $argss {
              if $iff {
                * index += 1 ;
                if * index < $defs.len() {
                  $done = false ;
                  break
                } else {
                  * index = 0
                }
              }
            }
          )
        }

        let mut done = false ;
        while ! done {
          // println!("running: {}", active_lhs_pred_app) ;

          let mut clause = clause.clone() ;
          if let Some((defs, argss)) = this_pred.as_ref() {
            let mut current = 0 ;

            while current < argss.len() {
              let (ref args, index) = argss[current] ;
              if current == active_lhs_pred_app {
                let is_new = clause.insert_pred_app(pred, args.clone()) ;
                debug_assert! { is_new }
              } else {
                self.insert_terms(
                  & mut clause, args, & defs[index].0, & defs[index].1
                ) ?
              }
              current += 1
            }

          }

          for (_, defs, argss) in & map {
            for (args, index) in argss {
              self.insert_terms(
                & mut clause, args, & defs[* index].0, & defs[* index].1
              ) ?
            }
          }

          // println!(
          //   "negative clause: {}",
          //   clause.to_string_info(instance.preds()).unwrap()
          // ) ;

          if let Some(trivial) = instance.is_this_clause_trivial(
            & mut clause
          ) ? {
            if ! trivial {
              // println!("non-trivial...") ;
              nu_clauses.push(clause)
            } else {
              // println!("trivial...")
            }
          } else {
            unimplemented!("unsat in biased unrolling")
          }

          done = map_inc!()
        }

      }

      for mut clause in nu_clauses {
        log! { @6
          "new clause: {}",
          clause.to_string_info( instance.preds() ) ?
        }

        clause.from_unrolling = true ;
        if let Some(index) = instance.push_clause(clause) ? {
          let (extractor, instance) = instance.extraction() ;
          self.retrieve_neg_def(
            instance, extractor, pred, & instance[index]
          ) ? ;
          info.clauses_added += 1
        }
      }
    }

    Ok(info)
  }

}

impl RedStrat for BiasedUnroll {
  fn name(& self) -> & 'static str { "biased_unroll" }

  fn new(_: & Instance) -> Self {
    let (
      in_pos_clauses, in_neg_clauses,
      not_in_pos_clauses, not_in_neg_clauses,
    ) = (
      PrdSet::new(), PrdSet::new(),
      PrdSet::new(), PrdSet::new(),
    ) ;

    BiasedUnroll {
      in_pos_clauses, in_neg_clauses,
      not_in_pos_clauses, not_in_neg_clauses,
      pos_defs: PrdHMap::new(),
      neg_defs: PrdHMap::new(),
      pos_new_preds: PrdHMap::new(),
      neg_new_preds: PrdHMap::new(),
      max_new_clauses: 0,
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    let mut info = RedInfo::new() ;

    let nothing_to_do = self.setup(instance) ? ;

    if nothing_to_do {
      return Ok(info)
    }

    // println!("done with setup") ;
    // self.print(instance) ;
    // println!() ;

    let mut new_stuff = true ;

    while new_stuff {
      new_stuff = false ;

      if conf.preproc.pos_unroll {

        for pred in self.not_in_pos_clauses.clone() {
          log! { @4
            "trying to generate positive clauses for {}", instance[pred]
          }
          // self.print(instance) ;

          if self.pos_new_preds.get(& pred).map(
            |(pos, _)| ! pos.is_empty()
          ).unwrap_or(false) {

            let this_info = self.generate_pos_clauses_for(pred, instance) ? ;
            if this_info.non_zero() {
              new_stuff = true ;

              let was_there = self.not_in_pos_clauses.remove(& pred) ;
              debug_assert! { was_there }

              let is_new = self.in_pos_clauses.insert(pred) ;
              debug_assert! { is_new }

              let prev = self.pos_new_preds.remove(& pred) ;
              debug_assert! { prev.is_some() }

              for (_, (pos, _)) in self.pos_new_preds.iter_mut().chain(
                self.neg_new_preds.iter_mut()
              ) {
                let is_new = pos.insert(pred) ;
                debug_assert! { is_new }
              }
              log! { @4 "-> success" }

              log! { @verb
                "generated {} positive clauses for {}",
                this_info.clauses_added, conf.emph(& instance[pred].name)
              }

            } else {
              if let Some((pos, neg)) = self.pos_new_preds.get_mut(& pred) {
                pos.clear() ;
                neg.clear()
              } else {
                bail!("inconsistent BiasedUnroll state")
              }
              log! { @4 "-> failure" }
            }
            info += this_info ;

          } else {
            log! { @4 "-> nothing new, skipping" }
          }
        }

      }

      if conf.preproc.neg_unroll {

        for pred in self.not_in_neg_clauses.clone() {
          log! { @4
            "trying to generate negative clauses for {}", instance[pred]
          }
          // self.print(instance) ;

          if self.neg_new_preds.get(& pred).map(
            |(pos, neg)| ! pos.is_empty() || ! neg.is_empty()
          ).unwrap_or(false) {

            let this_info = self.generate_neg_clauses_for(pred, instance) ? ;
            if this_info.non_zero() {
              new_stuff = true ;

              let was_there = self.not_in_neg_clauses.remove(& pred) ;
              debug_assert! { was_there }

              let is_new = self.in_neg_clauses.insert(pred) ;
              debug_assert! { is_new }

              let prev = self.neg_new_preds.remove(& pred) ;
              debug_assert! { prev.is_some() }

              for (_, (_, neg)) in self.pos_new_preds.iter_mut().chain(
                self.neg_new_preds.iter_mut()
              ) {
                let is_new = neg.insert(pred) ;
                debug_assert! { is_new }
              }
              log! { @4 "-> success" }

              log! { @verb
                "generated {} negative clauses for {}",
                this_info.clauses_added, conf.emph(& instance[pred].name)
              }

            } else {
              if let Some((pos, neg)) = self.neg_new_preds.get_mut(& pred) {
                pos.clear() ;
                neg.clear()
              } else {
                bail!("inconsistent BiasedUnroll state")
              }
              log! { @4 "-> failure" }
            }
            info += this_info ;

          } else {
            log! { @4 "-> nothing new, skipping" }
          }
        }

      }

    }

    info += instance.simplify_all() ? ;

    Ok(info)
  }
}



/// Unrolls positive constraints once.
pub struct Unroll {
  max_new_clauses: usize,
  ignore: PrdSet,
}

impl RedStrat for Unroll {
  fn name(& self) -> & 'static str { "unroll" }

  fn new(instance: & Instance) -> Self {
    Unroll {
      max_new_clauses: ::std::cmp::max(
        5, instance.preds().len() + instance.clauses().len() * 5 / 100
      ),
      ignore: PrdSet::new(),
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {

    let mut prd_map: PrdHMap<
      Vec<(Option<Quant>, TTermSet)>
    > = PrdHMap::with_capacity(17) ;

    scoped! {
      let mut insert = |
        pred: PrdIdx, q: Option<Quant>, ts: TTermSet
      | prd_map.entry(pred).or_insert_with(Vec::new).push((q, ts)) ;

      let (extractor, instance) = instance.extraction() ;

      'pos_clauses: for clause in instance.clauses() {

        if ! clause.lhs_preds().is_empty() {
          continue 'pos_clauses
        }

        conf.check_timeout() ? ;

        if let Some((pred, args)) = clause.rhs() {
          if self.ignore.contains(& pred) {
            continue 'pos_clauses
          }
          match extractor.terms_of_rhs_app(
            true, instance, & clause.vars,
            clause.lhs_terms(), clause.lhs_preds(),
            pred, args
          ) ? {
            ExtractRes::Success((q, ts)) => insert(
              pred, Quant::forall(q), ts
            ),
            ExtractRes::SuccessTrue => {
              let mut set = TTermSet::new() ;
              set.insert_term( term::tru() ) ;
              insert(
                pred, None, set
              )
            },
            ExtractRes::Failed => continue 'pos_clauses,
            ExtractRes::Trivial => bail!(
              "found a trivial clause during unrolling"
            ),
            ExtractRes::SuccessFalse => bail!(
              "found a predicate equivalent to false during unrolling"
            ),
          }
        }

      }
    }

    let mut info = RedInfo::new() ;
    for (pred, terms) in prd_map {
      // Anticipate blowup.
      let appearances = instance.clauses_of(pred).0.len() ;
      if terms.len() * appearances >= self.max_new_clauses {
        let is_new = self.ignore.insert(pred) ;
        debug_assert! { is_new }
        log! { @verb
          "not unrolling {}, {} variant(s), estimation: {} new clauses",
          conf.emph(& instance[pred].name),
          terms.len(),
          terms.len() * appearances
        }
      } else {
        log! { @verb
          "unrolling {}, {} variant(s)",
          conf.emph(& instance[pred].name),
          terms.len()
        }
        info += instance.unroll(pred, & terms) ?
      }
    }
    Ok(info)
  }
}



/// Reverse-unrolls negative constraints once.
pub struct RUnroll {
  max_new_clauses: usize,
  ignore: PrdSet,
}

impl RedStrat for RUnroll {
  fn name(& self) -> & 'static str { "runroll" }

  fn new(instance: & Instance) -> Self {
    RUnroll {
      max_new_clauses: ::std::cmp::max(
        5, instance.preds().len() + instance.clauses().len() * 5 / 100
      ),
      ignore: PrdSet::new(),
    }
  }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {

    let mut prd_map: PrdHMap<
      Vec<(Option<Quant>, TermSet)>
    > = PrdHMap::with_capacity(17) ;

    scoped! {
      let mut insert = |
        pred: PrdIdx, q: Option<Quant>, ts: TermSet
      | prd_map.entry(pred).or_insert_with(Vec::new).push((q, ts)) ;

      let (extractor, instance) = instance.extraction() ;

      'neg_clauses: for clause in instance.clauses() {

        if clause.rhs().is_some() { continue 'neg_clauses }

        conf.check_timeout() ? ;

        let mut apps = clause.lhs_preds().iter() ;

        if let Some((pred, argss)) = apps.next() {
          if self.ignore.contains(& pred) {
            continue 'neg_clauses
          }

          let pred = * pred ;
          let mut argss = argss.iter() ;
          let args = if let Some(args) = argss.next() {
            args
          } else {
            bail!("illegal clause, predicate application leads to nothing")
          } ;

          if argss.next().is_some()
          || apps.next().is_some() {
            continue 'neg_clauses
          }

          // Negative constraint with only one pred app, reverse-unrolling.
          match extractor.terms_of_lhs_app(
            true, instance, & clause.vars,
            clause.lhs_terms(), & PredApps::with_capacity(0),
            None, pred, args
          ) ? {

            ExtractRes::Success((q, apps, ts)) => {
              debug_assert! { apps.is_none() }
              let (terms, pred_apps) = ts.destroy() ;
              if_debug! {
                log!{ @debug
                  "from {}",
                  clause.to_string_info(
                    instance.preds()
                  ) ?
                }
                log! { @debug "terms {{" }
                for term in & terms {
                  log! { @debug "  {}", term }
                }
                log! { @debug "}}" }
                log! { @debug "pred apps {{" }
                for (pred, argss) in & pred_apps {
                  for args in argss {
                    let mut s = format!("({}", instance[* pred]) ;
                    for arg in args.iter() {
                      s = format!("{} {}", s, arg)
                    }
                    log! { @debug "  {})", s }
                  }
                }
                log! { @debug "}}" }
              }
              debug_assert! { pred_apps.is_empty() }
              insert( pred, Quant::exists(q), terms )
            },
            ExtractRes::SuccessFalse => {
              let mut set = TermSet::new() ;
              insert( pred, None, set )
            },
            ExtractRes::Failed => {
              log! { @debug "extraction failed, skipping" }
              continue 'neg_clauses
            },
            ExtractRes::Trivial => bail!(
              "found a trivial clause during unrolling"
            ),
            ExtractRes::SuccessTrue => bail!(
              "found a predicate equivalent to true during reverse-unrolling"
            ),

          }

        }

      }
    }

    let mut info = RedInfo::new() ;
    for (pred, terms) in prd_map {
      // Anticipate blowup.
      let appearances = instance.clauses_of(pred).0.len() ;
      if appearances >= self.max_new_clauses {
        let is_new = self.ignore.insert(pred) ;
        debug_assert! { is_new }
        log! { @verb
          "not r_unrolling {}, {} occurence(s), \
          estimation: {} new clauses (>= {})",
          conf.emph(& instance[pred].name),
          appearances,
          terms.len() * appearances,
          self.max_new_clauses,
        }
      } else {
        log! { @verb
          "r_unrolling {}, {} variant(s)",
          conf.emph(& instance[pred].name),
          terms.len()
        }
        info += instance.reverse_unroll(pred, & terms) ?
      }
    }
    Ok(info)
  }
}


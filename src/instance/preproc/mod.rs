//! Reduction strategies.
//!
//! The strategies are attached `struct`s so that they can be put in a vector
//! using single dispatch. That way, they can be combined however we want.

use common::* ;
use instance::* ;

pub mod utils ;
use self::utils::{ ExtractRes } ;
pub mod graph ;
pub mod args ;

use self::graph::Graph ;


/// Runs pre-processing
pub fn work(
  instance: & mut Instance, profiler: & Profiler
) -> Res<()> {

  profile!{ |profiler| tick "preproc" }
  log_info!{ "starting pre-processing" }

  let mut kid = ::rsmt2::Kid::new( conf.solver.conf() ).chain_err(
    || ErrorKind::Z3SpawnError
  ) ? ;
  let res = {
    let solver = ::rsmt2::solver(& mut kid, ()).chain_err(
      || "while constructing preprocessing's solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("preproc") ? {
      let mut reductor = Reductor::new( instance, solver.tee(log) ) ;
      reductor.run(profiler)
    } else {
      let mut reductor = Reductor::new( instance, solver ) ;
      reductor.run(profiler)
    }
  } ;
  profile!{ |profiler| mark "preproc" } ;

  kid.kill() ? ;

  // log_info!{
  //   "\n\ndone with pre-processing:\n{}\n\n", instance.to_string_info(()) ?
  // }
  match res {
    Err(ref e) if e.is_unsat() => {
      instance.set_unsat()
    },
    Err(e) => bail!(e),
    Ok(()) => ()
  }

  Ok(())
}




/// Stores and applies the reduction techniques.
pub struct Reductor<'a, S> {
  /// The pre-instance.
  instance: PreInstance<'a, S>,
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
  /// Optional unroller.
  unroll: Option<Unroll>,
  /// Optional reverse-unroller.
  runroll: Option<RUnroll>,
}
impl<'a, 'skid, S> Reductor<'a, S>
where S: Solver<'skid, ()> {
  /// Constructor.
  ///
  /// Checks the configuration to initialize the pre-processors.
  pub fn new(instance: & 'a mut Instance, solver: S) -> Self {
    let instance = PreInstance::new(instance, solver) ;

    macro_rules! some_new {
      ($red:ident if $flag:ident $(and $flags:ident )*) => (
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

    let unroll = some_new! { Unroll if unroll } ;
    let runroll = some_new! { RUnroll if unroll } ;

    Reductor {
      instance, simplify, arg_red,
      s_one_rhs, s_one_lhs, one_rhs, one_lhs,
      cfg_red, unroll, runroll
    }
  }

  /// Runs the full pre-processing.
  pub fn run(& mut self, _profiler: & Profiler) -> Res<()> {
    // Counter for preproc dumping.
    //
    // Starts at `1`, `0` is reserved for the fixed point.
    let mut count = 1 ;

    // Runs and profiles a pre-processor.
    //
    // Returns `true` if the pre-processor did something.
    macro_rules! run {
      ($preproc:ident) => (
        if let Some(preproc) = self.$preproc.as_mut() {
          profile! {
            |_profiler| tick "preproc", preproc.name()
          }
          log_info! { "running {}", conf.emph( preproc.name() ) }
          let red_info = preproc.apply( & mut self.instance ) ? ;
          profile! {
            |_profiler| mark "preproc", preproc.name()
          }
          if red_info.non_zero() {
            count += 1 ;
            preproc_dump!(
              self.instance =>
              format!("preproc_{:0>4}_{}", count, preproc.name()),
              format!("Instance after running `{}`.", preproc.name())
            ) ? ;
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
            log_info! { "{}: {}", conf.emph( preproc.name() ), red_info }
            conf.check_timeout() ? ;
            true
          } else {
            log_info! { "{}: did nothing", conf.emph( preproc.name() ) }
            false
          }
        } else {
          false
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
        "pred count original" => add self.instance.preds().len()
    }
    profile!{
      |_profiler|
        "arg count original" => add {
          let mut args = 0 ;
          for info in self.instance.preds() {
            args += info.sig.len()
          }
          args
        }
    }

    run! { simplify } ;

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

    run ! { unroll } ;
    run ! { runroll } ;

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
            args += info.sig.len()
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
  #[inline]
  fn name(& self) -> & 'static str ;

  /// Constructor.
  fn new(& Instance) -> Self ;

  /// Applies the reduction strategy. Returns the number of predicates reduced
  /// and the number of clauses forgotten.
  fn apply<'a, 'skid, S: Solver<'skid, ()>>(
    & mut self, & mut PreInstance<'a, S>
  ) -> Res<RedInfo> ;
}


/// Calls `PredInstance::simplify_all`.
pub struct Simplify ;

impl RedStrat for Simplify {
  fn name(& self) -> & 'static str { "simplify" }

  fn new(_: & Instance) -> Self { Simplify }

  fn apply<'a, 'skid, S>(
    & mut self, instance:& mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {
    instance.simplify_all()
  }
}


/// Calls [`Instance::arg_reduce`][arg_reduce].
///
/// [arg_reduce]: ../instance/struct.Instance.html#method.arg_reduce
/// (Instance's arg_reduce method)
pub struct ArgRed ;

impl RedStrat for ArgRed {
  fn name(& self) -> & 'static str { "arg_reduce" }

  fn new(_: & Instance) -> Self { ArgRed }

  fn apply<'a, 'skid, S>(
    & mut self, instance:& mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {
    instance.arg_reduce()
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

  fn apply<'a, 'skid, S>(
    & mut self, instance: & mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut red_info = RedInfo::new() ;

    for pred in instance.pred_indices() {
      conf.check_timeout() ? ;

      if instance.clauses_of(pred).1.len() == 1 {
        log_debug! {
          "  looking at {} ({}, {})",
          instance[pred],
          instance.clauses_of(pred).0.len(),
          instance.clauses_of(pred).1.len(),
        }

        let clause = * instance.clauses_of(
          pred
        ).1.iter().next().unwrap() ;
        log_debug! {
          "trying to unfold {}", instance[pred]
        }

        let res = if let Some((_this_pred, args)) = instance[clause].rhs() {
          debug_assert_eq!( pred, _this_pred ) ;

          // Does `pred` appear in the lhs?
          match instance[clause].lhs_preds().get(& pred) {
            Some(apps) if ! apps.is_empty() => {
              ExtractRes::SuccessFalse
            },
            _ => utils::terms_of_rhs_app(
              false, instance, instance[clause].vars(),
              instance[clause].lhs_terms(), instance[clause].lhs_preds(),
              pred, args
            ) ?,
          }
        } else {
          bail!("inconsistent instance state")
        } ;

        if res.is_failed() { continue }
        
        log_debug!{
          "from {}",
          instance.clauses()[clause].to_string_info( instance.preds() ) ?
        }

        log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        use self::ExtractRes::* ;
        match res {
          Trivial => {
            log_info!("  => trivial") ;
            red_info += instance.force_false(pred) ?
          },
          SuccessTrue => {
            log_info!("  => true") ;
            red_info += instance.force_true(pred) ?
          },
          SuccessFalse => {
            log_info!("  => false") ;
            red_info += instance.force_false(pred) ?
          },
          Success( (qvars, tterms) ) => {
            debug_assert! { qvars.is_empty() } ;
            if_not_bench! {
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log_debug! { "  => ({} {})", instance[* pred], args }
                }
              }
              for term in tterms.terms() {
                log_debug!("  => {}", term ) ;
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

  fn apply<'a, 'skid, S>(
    & mut self, instance: & mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {
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
        "  looking at {} ({}, {})",
        instance[pred],
        instance.clauses_of(pred).0.len(),
        instance.clauses_of(pred).1.len(),
      }

      // Skip if the clause mentions this predicate more than once.
      if let Some( argss ) = instance[clause_idx].lhs_preds().get(& pred) {
        if argss.len() > 1 { continue }
      }

      log_debug!{
        "trying to unfold {}", instance[pred]
      }

      let res = {
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
          _ => utils::terms_of_lhs_app(
            false, instance, clause.vars(),
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

      // log_info!{ "  instance:\n{}", instance.to_string_info( () ) ? }

      log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
      use self::ExtractRes::* ;
      match res {
        SuccessTrue => {
          log_info!("  => true") ;
          red_info += instance.force_true(pred) ?
        },
        SuccessFalse => {
          log_info!("  => false") ;
          red_info += instance.force_false(pred) ?
        },
        Trivial => {
          log_info! { "  => trivial" }
          red_info += instance.force_true(pred) ?
        },
        Success((qualfed, pred_app, tterms)) => {
          debug_assert! { qualfed.is_empty() }
          if pred_app.is_none() && tterms.is_empty() {
            log_info!("  => false") ;
            red_info += instance.force_false(pred) ?
          } else {
            if_not_bench!{
              log_debug!{ "  => (or" }
              if let Some((pred, ref args)) = pred_app {
                let mut s = format!("({}", instance[pred]) ;
                for arg in args.iter() {
                  s = format!("{} {}", s, arg)
                }
                log_debug!{ "    {})", s }
              }
              log_debug!{ "    (not" }
              log_debug!{ "      (and" }
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log_debug!{ "        ({} {})", instance[* pred], args}
                }
              }
              for term in tterms.terms() {
                log_debug!{ "        {}", term }
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

  fn apply<'a, 'skid, S>(
    & mut self, instance: & mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {
    debug_assert!( self.new_vars.is_empty() ) ;
    let mut red_info = RedInfo::new() ;

    'all_preds: for pred in instance.pred_indices() {
      conf.check_timeout() ? ;

      if instance.clauses_of(pred).1.len() == 1 {
        log_debug! {
          "  looking at {} ({}, {})",
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

        log_debug!{
          "trying to unfold {}", instance[pred]
        }

        let res = if let Some((_this_pred, args)) = instance[clause].rhs() {
          debug_assert_eq!( pred, _this_pred ) ;

          // Does `pred` appear in the lhs?
          match instance[clause].lhs_preds().get(& pred) {
            Some(apps) if ! apps.is_empty() => {
              ExtractRes::SuccessFalse
            },
            _ => utils::terms_of_rhs_app(
              true, instance, instance[clause].vars(),
              instance[clause].lhs_terms(), instance[clause].lhs_preds(),
              pred, args
            ) ?,
          }
        } else {
          bail!("inconsistent instance state")
        } ;

        if res.is_failed() {
          log_debug!{ "  skipping" }
          continue
        }

        log_debug!{
          "from {}",
          instance.clauses()[clause].to_string_info( instance.preds() ) ?
        }

        log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        use self::ExtractRes::* ;
        match res {
          Trivial => {
            log_info!("  => trivial") ;
            red_info += instance.force_false(pred) ?
          },
          SuccessTrue => {
            log_info!("  => true") ;
            red_info += instance.force_true(pred) ? ;
          },
          SuccessFalse => {
            log_info!("  => false") ;
            red_info += instance.force_false(pred) ? ;
          },
          Success( (qvars, tterms) ) => {
            if_not_bench! {
              log_debug!("  {} quantified variables", qvars.len()) ;
              for (var, typ) in & qvars {
                log_debug!("  - v_{}: {}", var, typ)
              }
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log_debug! { "  => ({} {})", instance[* pred], args }
                }
              }
              for term in tterms.terms() {
                log_debug!("  => {}", term ) ;
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

  fn apply<'a, 'skid, S>(
    & mut self, instance: & mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {
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
        "  looking at {} ({}, {})",
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
          _ => utils::terms_of_lhs_app(
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

      // log_info!{ "  instance:\n{}", instance.to_string_info( () ) ? }

      log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
      use self::ExtractRes::* ;
      match res {
        SuccessTrue => {
          log_info!("  => true") ;
          red_info += instance.force_true(pred) ?
        },
        SuccessFalse => {
          log_info!("  => false") ;
          red_info += instance.force_false(pred) ?
        },
        Trivial => {
          log_info!("  => trivial") ;
          red_info += instance.force_true(pred) ?
        },
        Success((qvars, pred_app, tterms)) => {
          if_not_bench!{
            log_debug!("  {} quantified variables", qvars.len()) ;
            for (var, typ) in & qvars {
              log_debug!("  - v_{}: {}", var, typ)
            }
            log_debug!{ "  => (or" }
            if let Some((pred, ref args)) = pred_app {
              let mut s = format!("({}", instance[pred]) ;
              for arg in args.iter() {
                s = format!("{} {}", s, arg)
              }
              log_debug!{ "    {})", s }
            }
            log_debug!{ "    (not" }
            log_debug!{ "      (and" }
            for (pred, args) in tterms.preds() {
              let mut s = format!("({}", instance[* pred]) ;
              for arg in args {
                s = format!("{} {}", s, arg)
              }
              log_debug!{ "        {})", s }
            }
            for term in tterms.terms() {
              log_debug!{ "        {}", term }
            }
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
  upper_bound: Option<usize>,
  /// Graph, factored to avoid reallocation.
  graph: Graph,
}

impl RedStrat for CfgRed {
  fn name(& self) -> & 'static str { "cfg_red" }

  fn new(instance: & Instance) -> Self {
    CfgRed {
      cnt: 0,
      upper_bound: None,
      graph: Graph::new(instance),
    }
  }

  fn apply<'a, 'skid, S>(
    & mut self, instance: & mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {
    // use std::time::Instant ;
    // use common::profiling::DurationExt ;

    let upper_bound = if let Some(upper_bound) = self.upper_bound {
      upper_bound
    } else {
      let clause_count = instance.clauses().len() ;
      let upper_bound = if clause_count <= 10 {
        clause_count * 25
      } else if clause_count <= 100 {
        clause_count * 15
      } else if clause_count <= 500 {
        clause_count * 10
      } else {
        clause_count * 5
      } ;
      self.upper_bound = Some(upper_bound) ;
      upper_bound
    } ;

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
        instance, & mut to_keep, upper_bound
      ) ? ;

      if pred_defs.len() == 0 { return Ok(info) }

      info.preds += pred_defs.len() ;

      self.graph.check(& instance) ? ;
      log_info! { "inlining {} predicates", pred_defs.len() }

      if pred_defs.len() == instance.active_pred_count() {
        let (is_sat, this_info) = instance.force_all_preds(pred_defs) ? ;
        info += this_info ;
        if ! is_sat {
          bail!( ErrorKind::Unsat )
        } else {
          return Ok(info)
        }
      }

      // Remove all clauses leading to the predicates we just inlined.
      for (pred, def) in pred_defs {
        conf.check_timeout() ? ;
        info += instance.rm_rhs_clauses_of(pred) ? ;

        if_verb! {
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
          log_debug! { "{}) = (or", s }
          for & (ref qvars, ref conj) in & def {
            let (suff, pref) = if qvars.is_empty() { (None, "  ") } else {
              let mut s = format!("  (exists") ;
              for (var, typ) in qvars {
                s.push_str(" (") ;
                s.push_str( & var.default_str() ) ;
                s.push_str( & format!(" {})", typ) )
              }
              log_debug! { "{}", s }
              (Some("  )"), "    ")
            } ;
            log_debug! { "{}(and", pref }
            for term in conj.terms() {
              log_debug! { "{}  {}", pref, term }
            }
            for (pred, argss) in conj.preds() {
              for args in argss {
                log_debug! { "{}  ({} {})", pref, instance[* pred], args }
              }
            }
            log_debug! { "{})", pref }
            if let Some(suff) = suff {
              log_debug! { "{}", suff }
            }
          }
          log_debug! { ")" }
        }

        info += instance.force_dnf_left(pred, def) ? ;
      }

      info += instance.force_trivial() ? ;

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



/// Unrolls positive constraints once.
pub struct Unroll {}

impl RedStrat for Unroll {
  fn name(& self) -> & 'static str { "unroll" }

  fn new(_: & Instance) -> Self {
    Unroll {}
  }

  fn apply<'a, 'skid, S>(
    & mut self, instance: & mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {

    let mut prd_map: PrdHMap<
      Vec<(Option<Quant>, TTermSet)>
    > = PrdHMap::with_capacity(17) ;

    scoped! {
      let mut insert = |
        pred: PrdIdx, q: Option<Quant>, ts: TTermSet
      | prd_map.entry(pred).or_insert_with(
        || Vec::new()
      ).push((q, ts)) ;

      'all_clauses: for clause in instance.clause_indices() {
        conf.check_timeout() ? ;
        let clause = & instance[clause] ;

        if clause.lhs_preds().is_empty() {
          if let Some((pred, args)) = clause.rhs() {
            match utils::terms_of_rhs_app(
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
              ExtractRes::Failed => continue 'all_clauses,
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
    }

    let mut info = RedInfo::new() ;
    for (pred, terms) in prd_map {
      log_info! {
        "unrolling {}, {} term(s)",
        conf.emph(& instance[pred].name),
        terms.len()
      }
      info += instance.unroll(pred, terms) ?
    }
    Ok(info)
  }
}



/// Reverse-unrolls negative constraints once.
pub struct RUnroll {}

impl RedStrat for RUnroll {
  fn name(& self) -> & 'static str { "runroll" }

  fn new(_: & Instance) -> Self {
    RUnroll {}
  }

  fn apply<'a, 'skid, S>(
    & mut self, instance: & mut PreInstance<'a, S>
  ) -> Res<RedInfo>
  where S: Solver<'skid, ()> {

    let mut prd_map: PrdHMap<
      Vec<(Option<Quant>, HConSet<Term>)>
    > = PrdHMap::with_capacity(17) ;

    scoped! {
      let mut insert = |
        pred: PrdIdx, q: Option<Quant>, ts: HConSet<Term>
      | prd_map.entry(pred).or_insert_with(
        || Vec::new()
      ).push((q, ts)) ;

      'all_clauses: for clause in instance.clause_indices() {
        conf.check_timeout() ? ;
        let clause = & instance[clause] ;

        if clause.rhs().is_none() {
          let mut apps = clause.lhs_preds().iter() ;

          if let Some((pred, argss)) = apps.next() {
            let pred = * pred ;
            let mut argss = argss.iter() ;
            let args = if let Some(args) = argss.next() {
              args
            } else {
              bail!("illegal clause, predicate application leads to nothing")
            } ;

            if argss.next().is_some() || apps.next().is_some() {
              continue 'all_clauses
            }

            // Negative constraint with only one pred app, reverse-unrolling.
            match utils::terms_of_lhs_app(
              true, instance, & clause.vars,
              clause.lhs_terms(), & PredApps::with_capacity(0),
              None, pred, args
            ) ? {

              ExtractRes::Success((q, apps, ts)) => {
                debug_assert! { apps.is_none() }
                let (terms, pred_apps) = ts.destroy() ;
                if_verb! {
                  log_debug!{
                    "from {}",
                    clause.to_string_info(
                      instance.preds()
                    ) ?
                  }
                  log_debug! { "terms {{" }
                  for term in & terms {
                    log_debug! { "  {}", term }
                  }
                  log_debug! { "}}" }
                  log_debug! { "pred apps {{" }
                  for (pred, argss) in & pred_apps {
                    for args in argss {
                      let mut s = format!("({}", instance[* pred]) ;
                      for arg in args.iter() {
                        s = format!("{} {}", s, arg)
                      }
                      log_debug! { "  {})", s }
                    }
                  }
                  log_debug! { "}}" }
                }
                debug_assert! { pred_apps.is_empty() }
                insert( pred, Quant::exists(q), terms )
              },
              ExtractRes::SuccessFalse => {
                let mut set = HConSet::<Term>::new() ;
                insert( pred, None, set )
              },
              ExtractRes::Failed => continue 'all_clauses,
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
    }

    let mut info = RedInfo::new() ;
    for (pred, terms) in prd_map {
      log_info! {
        "reverse unrolling {}, {} unrolling(s)",
        conf.emph(& instance[pred].name),
        terms.len()
      }
      info += instance.reverse_unroll(pred, terms) ?
    }
    Ok(info)
  }
}


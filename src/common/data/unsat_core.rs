//! Unsat-core-related types and helpers.

use common::* ;
use data::Args ;



/// The origin of a sample is a clause and some samples for activating the rhs.
type Origin = (ClsIdx, PrdHMap< Vec<Args> >) ;


/// An unsat source.
pub type UnsatSource = Vec<(PrdIdx, Args)> ;

/// An unsat result.
pub type UnsatRes = Option<(SampleGraph, UnsatSource)> ;

/// An unsat core.
pub type UnsatCore = Vec<(ClsIdx, VarHMap<Val>)> ;


/// Stores the graph of dependency between samples.
///
/// Remembers where each sample comes from.
///
/// # TODO
///
/// - there's no need to clone the sample graph currently, but still the
///   teacher will do it when communicating data to the learner(s)
#[derive(Clone, Debug)]
pub struct SampleGraph {
  /// Maps samples to the clause and the samples for this clause they come
  /// from.
  graph: PrdHMap< HConMap<Args, Vec<Origin>> >,
  /// Negative samples.
  neg: PrdHMap<HConMap<Args, Vec<Origin>>>
}

impl SampleGraph {
  /// Creates a new sample graph.
  pub fn new() -> Self {
    SampleGraph { graph: PrdHMap::new(), neg: PrdHMap::new() }
  }


  /// Adds traceability for a sample.
  pub fn add(
    & mut self, prd: PrdIdx, args: Args,
    cls: ClsIdx, samples: PrdHMap<Vec<Args>>,
  ) -> Res<()> {
    if_log! { @3
      log! { @3
        "adding origin for ({} {})", prd, args ;
        "from clause #{} {{", cls
      }
      for (pred, samples) in & samples {
        log! { @3 "  from predicate {}:", pred }
        for sample in samples {
          log! { @3 "    {}", sample }
        }
      }
      log! { @3 "}}" }
    }
    self.graph.entry(prd).or_insert_with(
      || HConMap::new()
    ).entry(args).or_insert_with(
      || vec![]
    ).push( (cls, samples) ) ;

    Ok(())
  }

  /// Adds traceability for a negative sample.
  pub fn add_neg(
    & mut self, prd: PrdIdx, args: Args,
    cls: ClsIdx, samples: PrdHMap<Vec<Args>>
  ) -> Res<()> {
    self.neg.entry(prd).or_insert_with(
      || HConMap::new()
    ).entry(args).or_insert_with(
      || vec![]
    ).push( (cls, samples) ) ;

    Ok(())
  }

  /// Returns the set of positive samples (transitively) from the graph.
  ///
  /// This operation is quite expensive...
  pub fn positive_samples(& self) -> PrdHMap<ArgsSet> {
    let mut res = PrdHMap::new() ;
    let mut changed = true ;

    while changed {
      changed = false ;

      for (pred, arg_map) in & self.graph {

        'current_pred: for (args, origins) in arg_map {

          // Skip if current sample is known to be true.
          if res.get(pred).map(
            |set: & ArgsSet| set.contains(args)
          ).unwrap_or(false) {
            continue 'current_pred
          }

          // Check all origins.
          for (_clause_idx, origin) in origins {

            // Check all samples in the origin are known to be true.
            for (o_pred, o_argss) in origin {
              for o_args in o_argss {

                if res.get(o_pred).map(
                  |set: & ArgsSet| ! set.contains(o_args)
                ).unwrap_or(true) {
                  continue 'current_pred
                }

              }
            }

            // Only reachable if all samples in this origin are true.
            let is_new = res.entry(* pred).or_insert_with(
              || ArgsSet::new()
            ).insert(args.clone()) ;

            debug_assert! { is_new }

            changed = true ;
            // No need to check other origins, move on to the next sample.
            continue 'current_pred
          }
        }

      }

    }

    res
  }

  /// Trace the origin of a sample.
  pub fn trace(& self, samples: & Vec<(PrdIdx, Args)>) -> Res<
    Vec<(ClsIdx, PrdIdx, Args, PrdHMap< Vec<Args> >)>
  > {
    // Retrieve the set of positive samples to chose the right origins.
    let pos_samples = self.positive_samples() ;
    macro_rules! is_all_positive {
      ($origin:expr) => ({
        let mut all_positive = true ;
        for (pred, argss) in $origin {
          if ! all_positive { break }
          for args in argss {
            if pos_samples.get(pred).map(
              |set| ! set.contains(args)
            ).unwrap_or(false) {
              all_positive = false ;
              break
            }
          }
        }
        all_positive
      })
    }

    let mut known = PrdHMap::new() ;
    for pred in self.graph.keys() {
      known.insert(* pred, HConSet::<Args>::new()) ;
    }

    macro_rules! known {
      (? $prd:expr, $args:expr) => (
        known.get(& $prd).unwrap().contains($args)
      ) ;
      (add $prd:expr, $args:expr) => (
        known.get_mut(& $prd).unwrap().insert($args)
      ) ;
    }

    let mut to_find: Vec<_> = samples.iter().map(
      |& (pred, ref args)| (pred, args)
    ).collect() ;
    let mut trace = Vec::new() ;

    while let Some((pred, args)) = to_find.pop() {
      let is_new = known!(add pred, args.clone()) ;
      if ! is_new { continue }

      let mut found_it = false ;

      if let Some(origins) = self.graph.get(& pred).and_then(
        |map| map.get(& args)
      ) {
        for & (clause, ref samples) in origins {
          if is_all_positive!(samples) {
            found_it = true ;
            for (pred, argss) in samples {
              let pred = * pred ;
              for args in argss {
                if ! known!(? pred, args) {
                  to_find.push((pred, args))
                }
              }
            }
            trace.push( (clause, pred, args.clone(), samples.clone()) )
          }
        }
      }

      if let Some(origins) = self.neg.get(& pred).and_then(
        |map| map.get(& args)
      ) {
        for & (clause, ref samples) in origins {
          if is_all_positive!(samples) {
            found_it = true ;
            for (pred, argss) in samples {
              let pred = * pred ;
              for args in argss {
                if ! known!(? pred, args) {
                  to_find.push((pred, args))
                }
              }
            }
            trace.push( (clause, pred, args.clone(), samples.clone()) )
          }
        }
      }

      if ! found_it {
        bail!("inconsistent sample graph state...")
      }
    }

    Ok(trace)
  }

  /// Checks that the sample graph is legal.
  ///
  /// Only active in debug.
  #[cfg(debug_assertions)]
  pub fn check(& self) -> Res<()> {
    for args in self.graph.values() {
      for origins in args.values() {
        for & (_, ref samples) in origins {
          for (pred, argss) in samples {
            for args in argss {
              if self.graph.get(pred).and_then(
                |map| map.get(args)
              ).is_none() {
                bail!("inconsistent sample graph state...")
              }
            }
          }
        }
      }
    }
    Ok(())
  }
  /// Checks that the sample graph is legal.
  ///
  /// Only active in debug.
  #[cfg(not(debug_assertions))]
  pub fn check(& self) -> Res<()> {
    Ok(())
  }



  /// Writes the sample graph with a prefix.
  pub fn write_graph<W: Write>(
    & self, w: & mut W, pref: & str, instance: & Instance
  ) -> IoRes<()> {
    writeln!(w, "{}sample graph {{", pref) ? ;

    for (pred, map) in & self.graph {
      writeln!(w, "{}  {}:", pref, instance[* pred]) ? ;
      for (args, origins) in map {
        for & (clause, ref apps) in origins {
          write!(w, "{}    {}  <=#{}=", pref, args, clause) ? ;
          if apps.is_empty() {
            write!(w, "  true") ?
          } else {
            for (pred, argss) in apps {
              for args in argss {
                write!(w, "  ({} {})", instance[* pred], args) ?
              }
            }
          }
          writeln!(w, "") ?
        }
      }
    }

    for (pred, map) in & self.neg {
      writeln!(w, "{}  {}:", pref, instance[* pred]) ? ;
      for (args, origins) in map {
        for & (clause, ref apps) in origins {
          write!(w, "{}    {}: false  <=#{}=", pref, args, clause) ? ;
          if apps.is_empty() {
            write!(w, "  true") ?
          } else {
            for (pred, argss) in apps {
              for args in argss {
                write!(w, "  ({} {})", instance[* pred], args) ?
              }
            }
          }
          writeln!(w, "") ?
        }
      }
    }

    writeln!(w, "{}}}", pref)
  }



  /// Writes an unsat core.
  pub fn write_core<W: Write>(
    & self, w: & mut W, instance: & Instance, source: & UnsatSource
  ) -> Res<()> {
    log! { @debug "retrieving core..." }
    let core = self.unsat_core_for(instance, source) ? ;

    log! { @debug "retrieving definitions..." }
    let empty_candidates = PrdHMap::with_capacity( instance.preds().len() ) ;
    let definitions = instance.extend_model(empty_candidates) ? ;

    writeln!(w, "(") ? ;

    // Write definitions.
    writeln!(w, "  ( ; Predicate definitions, obtained by pre-processing.") ? ;
    instance.write_definitions(w, "    ", & definitions) ? ;
    writeln!(w, "  )") ? ;

    // Write the core itself.
    writeln!(w, "  ( ; Trace of clauses explaining the contradiction.") ? ;
    for (clause, vals) in core {
      let original_clause = instance[clause].from() ;
      if let Some(name) = instance.name_of_old_clause(original_clause) {
        writeln!(w, "    ({} (", name) ? ;
        for (var, val) in vals {
          writeln!(
            w, "      (define-fun {} () {} {})",
            instance[clause][var], instance[clause][var].name, val
          ) ?
        }
        writeln!(w, "    ) )") ?
      }
    }
    writeln!(w, "  )") ? ;

    writeln!(w, ")") ? ;

    Ok(())
  }



  /// Retrieves an unsat core from a sample expected to be false.
  pub fn unsat_core_for(
    & self, instance: & Instance, samples: & Vec<(PrdIdx, Args)>
  ) -> Res<UnsatCore> {
    use common::smt::{
      FullParser as Parser, SmtConj, EqConj
    } ;

    log! { @4 "retrieving trace..." }
    let trace = self.trace(samples) ? ;

    let mut core = Vec::with_capacity( trace.len() ) ;

    let mut solver = conf.solver.spawn(
      "core_extraction", Parser, & instance
    ) ? ;

    log! { @4 "extracting quantified variables' values..." }

    for (clause_idx, pred, rhs_sample, lhs) in trace {
      log! { @4 "working on clause #{}", clause_idx }
      let clause = & instance[clause_idx] ;
      solver.comment(
        & format!("Working on clause #{}", clause_idx)
      ) ? ;

      solver.push(1) ? ;

      clause.declare(& mut solver) ? ;

      let conj = SmtConj::new(clause.lhs_terms()) ;

      solver.assert(& conj) ? ;

      debug_assert_eq! { clause.lhs_preds().len(), lhs.len() }

      for (
        (pred, argss), (other_pred, samples)
      ) in clause.lhs_preds().iter().zip( lhs.iter() ) {
        debug_assert_eq! { pred, other_pred }
        debug_assert_eq! { argss.len(), samples.len() }
        for (args, sample) in argss.iter().zip( samples.iter() ) {
          let eq_conj = EqConj::new(args, sample) ;
          solver.assert(& eq_conj) ?
        }
      }

      if let Some((rhs_pred, rhs_args)) = clause.rhs() {
        debug_assert_eq! { pred, rhs_pred }
        debug_assert_eq! { rhs_sample.len(), rhs_args.len() }
        let eq_conj = EqConj::new(rhs_args, & rhs_sample) ;
        solver.assert(& eq_conj) ?
      }

      if ! solver.check_sat() ? {
        bail!("error retrieving unsat core, trace is not feasible")
      }

      let model = solver.get_model() ? ;

      solver.pop(1) ? ;

      let mut map = VarHMap::with_capacity(model.len()) ;
      for (var, _, _, val) in model {
        let prev = map.insert(var, val) ;
        debug_assert_eq! { prev, None }
      }

      core.push((clause_idx, map))
    }

    Ok(core)
  }

}
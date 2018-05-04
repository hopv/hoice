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
  graph: PrdHMap< HConMap<Args, Origin> >,
  /// Negative samples.
  neg: PrdHMap<HConMap<Args, Origin>>
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
    let prev = self.graph.entry(prd).or_insert_with(
      || HConMap::new()
    ).insert(
      args, (cls, samples)
    ) ;
    if prev.is_some() {
      bail!("trying to redefine origin of a sample")
    }
    Ok(())
  }

  /// Adds traceability for a negative sample.
  pub fn add_neg(
    & mut self, prd: PrdIdx, args: Args,
    cls: ClsIdx, samples: PrdHMap<Vec<Args>>
  ) -> Res<()> {
    let prev = self.neg.entry(prd).or_insert_with(
      || HConMap::new()
    ).insert(
      args, (cls, samples)
    ) ;
    if prev.is_some() {
      bail!("trying to redefine origin of a sample")
    }
    Ok(())
  }

  /// Trace the origin of a sample.
  pub fn trace(& self, samples: & Vec<(PrdIdx, Args)>) -> Res<
    Vec<(ClsIdx, PrdIdx, Args, PrdHMap< Vec<Args> >)>
  > {
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

      if let Some(& (clause, ref samples)) = self.graph.get(& pred).and_then(
        |map| map.get(& args)
      ) {
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

      if let Some(& (clause, ref samples)) = self.neg.get(& pred).and_then(
        |map| map.get(& args)
      ) {
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
      for & (_, ref samples) in args.values() {
        for (pred, argss) in samples {
          for args in argss {
            if self.graph.get(pred).and_then( |map| map.get(args) ).is_none() {
              bail!("inconsistent sample graph state...")
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
  pub fn write<W: Write>(
    & self, w: & mut W, pref: & str, instance: & Instance
  ) -> IoRes<()> {
    writeln!(w, "{}sample graph {{", pref) ? ;

    for (pred, map) in & self.graph {
      writeln!(w, "{}  {}:", pref, instance[* pred]) ? ;
      for (args, & (clause, ref apps)) in map {
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

    for (pred, map) in & self.neg {
      writeln!(w, "{}  {}:", pref, instance[* pred]) ? ;
      for (args, & (clause, ref apps)) in map {
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

    writeln!(w, "{}}}", pref)
  }



  /// Retrieves an unsat core from a sample expected to be false.
  pub fn unsat_core_for(
    & self, instance: & Instance, samples: & Vec<(PrdIdx, Args)>
  ) -> Res<UnsatCore> {
    use common::smt::{
      FullParser as Parser, SmtConj, EqConj
    } ;

    let trace = self.trace(samples) ? ;

    let mut core = Vec::with_capacity( trace.len() ) ;

    let mut solver = conf.solver.spawn(
      "core_extraction", Parser, & instance
    ) ? ;

    for (clause_idx, pred, rhs_sample, lhs) in trace {
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
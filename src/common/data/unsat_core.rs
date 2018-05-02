//! Unsat-core-related types and helpers.

use common::* ;
use data::Args ;



/// The origin of a sample is a clause and some samples for activating the rhs.
type Origin = (ClsIdx, PrdHMap<Vec<Args>>) ;



/// Stores the graph of dependency between samples.
///
/// Remembers where each sample comes from.
pub struct SampleGraph {
  /// Maps samples to the clause and the samples for this clause they come
  /// from.
  graph: PrdHMap< HConMap<Args, Origin> >
}

impl SampleGraph {
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

  /// Trace the origin of a sample.
  pub fn trace(& self, prd: PrdIdx, args: Args) -> Res<
    Vec<Origin>
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

    let mut to_find = vec![ (prd, & args) ] ;
    let mut trace = Vec::new() ;

    while let Some((pred, args)) = to_find.pop() {
      let is_new = known!(add pred, args.clone()) ;
      debug_assert! { is_new }
      if let Some(& (clause, ref samples)) = self.graph.get(& pred).and_then(
        |map| map.get(& args)
      ) {
        for (pred, argss) in samples {
          let pred = * pred ;
          for args in argss {
            if ! known!(? pred, args) {
              to_find.push((pred, args))
            }
          }
        }
        trace.push( (clause, samples.clone()) )
      } else {
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

}
//! Handles example propagation.

use common::* ;
use common::data::{ Data, Sample } ;

/// Propagates examples, tries to break implication constraints.
pub struct Assistant {}

impl Assistant {

  /// Constructor.
  pub fn new() -> Self {
    Assistant {}
  }

  /// Breaks implications.
  pub fn break_implications(
    & self, data: & Data,
  ) -> Res<()> {

    for cstr in CstrRange::zero_to( data.constraints.len() ) {
      if ! data.constraints[cstr].is_tautology() {
        continue
      }

      // Any of the lhs positive?
      for sample in & data.constraints[cstr].lhs {
        if let Some(sample) = self.make_positive(data, sample) ? {
          unimplemented!()
        }
      }

    }

    Ok(())
  }

  /// Checks if a sample can be forced positive.
  ///
  /// If it can, returns a sample which, when forced positive, will force the
  /// input sample to be classified positive.
  pub fn make_positive(
    & self, data: & Data, & Sample { pred, ref args }: & Sample
  ) -> Res< Option<Sample> > {


    bail!("unimplemented")
  }

}
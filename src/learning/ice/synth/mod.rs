//! Qualifier synthesis modulo theory.
//!
//! # TO DO
//!
//! - document the workflow

use common::* ;
use common::data::HSample ;

pub mod int ;

pub type TermVals = HConMap<Term, Val> ;

/// A theory synthesizer.
///
/// A `TheoSynth` synthezises qualifiers given some arguments for a predicate
/// and some additional term/value pair, that typically come from other
/// theories. These pairs are the result of projecting/casting/... an argument
/// of a different theory to this one.
///
/// It is iterable. Each version generates qualifiers more complex than the
/// previous one, making synthesis more expressive with each call to `next`.
pub trait TheoSynth {
  /// Returns `true` if the synthesizer is done (will not produce new
  /// qualifiers).
  fn is_done(& self) -> bool ;
  /// Restarts the synthesizer.
  fn restart(& mut self) ;
  /// Synthesizes qualifiers.
  fn synth<F>(& mut self, F, & HSample, & mut TermVals) -> Res<bool>
  where F: FnMut(Term) -> Res<bool> ;
  /// Generates some [`TermVal`][term val]s for some other type.
  ///
  /// Adds them to the input term to value map.
  ///
  /// [term val]: struct.TermVal.html
  /// (TermVal struct)
  fn project(& self, & HSample, Typ, & mut TermVals) -> Res<()> ;
}
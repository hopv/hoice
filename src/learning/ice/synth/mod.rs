//! Qualifier synthesis modulo theory.
//!
//! # TO DO
//!
//! - document the workflow

use common::* ;
use common::data::HSample ;

#[macro_use]
pub mod helpers ;
pub mod int ;
pub mod real ;

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
  /// Type of values supported by this synthesizer.
  fn typ(& self) -> & Typ ;
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
  fn project(& self, & HSample, & Typ, & mut TermVals) -> Res<()> ;
}

use self::int::IntSynth ;
use self::real::RealSynth ;

/// Manages theory synthesizers.
pub struct SynthSys {
  int: Option<IntSynth>,
  real: Option<RealSynth>,
  cross_synth: HConMap<Term, Val>,
}
impl SynthSys {
  /// Constructor.
  pub fn new(sig: & Sig) -> Self {
    let mut int = false ;
    let mut real = false ;
    for typ in sig {
      match * typ {
        Typ::Int => int = true,
        Typ::Real => real = true,
        _ => (),
      }
    }

    SynthSys {
      int: if int { Some( IntSynth::new() ) } else { None },
      real: if real { Some(RealSynth::new() ) } else { None },
      cross_synth: HConMap::new(),
    }
  }



  /// Synthesizes qualifiers for a sample, stops if input function returns
  /// `true`.
  ///
  /// Returns `true` iff `f` returned true at some point.
  pub fn sample_synth<F>(
    & mut self, sample: & HSample, mut f: F, _profiler: & Profiler
  ) -> Res<bool>
  where F: FnMut(Term) -> Res<bool> {

    loop {
      let mut done = true ;

      if let Some(int_synth) = self.int.as_mut() {
        if ! int_synth.is_done() {
          done = false ;
          debug_assert! { self.cross_synth.is_empty() }
          if let Some(real_synth) = self.real.as_mut() {
            profile!{
              |_profiler| tick "learning", "qual", "synthesis", "int project"
            }
            real_synth.project(
              sample, int_synth.typ(), & mut self.cross_synth
            ) ? ;
            profile!{
              |_profiler| mark "learning", "qual", "synthesis", "int project"
            }
          }
          profile!{ |_profiler| tick "learning", "qual", "synthesis", "int" }
          let done = int_synth.synth(
            & mut f, sample, & mut self.cross_synth
          ) ? ;
          profile!{ |_profiler| mark "learning", "qual", "synthesis", "int" }
          if done { return Ok(true) }
        }
      }

      if let Some(real_synth) = self.real.as_mut() {
        if ! real_synth.is_done() {
          done = false ;
          debug_assert! { self.cross_synth.is_empty() }
          if let Some(int_synth) = self.int.as_mut() {
            profile!{
              |_profiler| tick "learning", "qual", "synthesis", "real project"
            }
            int_synth.project(
              sample, real_synth.typ(), & mut self.cross_synth
            ) ? ;
            profile!{
              |_profiler| mark "learning", "qual", "synthesis", "real project"
            }
          }
          profile!{ |_profiler| tick "learning", "qual", "synthesis", "real" }
          let done = real_synth.synth(
            & mut f, sample, & mut self.cross_synth
          ) ? ;
          profile!{ |_profiler| mark "learning", "qual", "synthesis", "real" }
          if done { return Ok(true) }
        }
      }

      if done { break }
    }

    Ok(false)
  }
}
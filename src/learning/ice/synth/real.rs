//! Qualifier synthesis in the theory of reals.

use common::* ;
use common::data::HSample ;

use super::{ TermVals, TheoSynth } ;


/// Real qualifier synthesizer.
pub struct RealSynth {
  /// Expressivity level.
  expressivity: usize,
  /// The real type.
  typ: Typ,
}
impl RealSynth {
  /// Creates a new integer synthesizer.
  pub fn new() -> Self {
    RealSynth {
      expressivity: 0,
      typ: Typ::Real
    }
  }
}
impl TheoSynth for RealSynth {
  fn typ(& self) -> & Typ { & self.typ }
  fn is_done(& self) -> bool {
    self.expressivity > 0
  }
  fn restart(& mut self) {
    * self = Self::new()
  }
  fn synth<F>(
    & mut self, f: F, sample: & HSample, others: & mut TermVals
  ) -> Res<bool>
  where F: FnMut(Term) -> Res<bool> {
    match self.expressivity {
      0 => {
        self.expressivity += 1 ;
        simple_real_synth(sample, others, f)
      },
      _ => Ok(false),
    }
  }

  /// Only generates ints for now (using `to_int`).
  fn project(
    & self, sample: & HSample, typ: & Typ, map: & mut TermVals
  ) -> Res<()> {
    match * typ {
      Typ::Int => for (var, val) in sample.index_iter() {
        match * val {
          Val::R(ref r) => {
            let val = Op::ToInt.eval( vec![ Val::R( r.clone() ) ] ) ? ;
            let prev = map.insert(
              term::to_int( term::var(var) ), val
            ) ;
            debug_assert_eq!( prev, None )
          },
          _ => (),
        }
      },
      _ => (),
    }
    Ok(())
  }
}


/// Lowest level of real synthesis.
///
/// All `v*` are variables. Synthesizes qualifiers of the form
///
/// - `v = n`, `v <= n`, `v >= n`,
/// - `v_1 = v_2`, `v_1 = - v_2`,
/// - `v_1 + v_2 >= n`, `v_1 + v_2 <= n`,
/// - `v_1 - v_2 >= n`, `v_1 - v_2 <= n`,
pub fn simple_real_synth<F>(
  sample: & HSample, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_real: Vec<(Term, Rat)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match * val {
      Val::R(ref val) => {
        let var = term::var(var_idx) ;
        simple_arith_synth! { previous_real, f, real | var = ( val.clone() ) }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val {
      Val::R(val) => {
        simple_arith_synth! { previous_real, f, real | term = val }
      }
      val => bail!(
        "real synthesis expects projected reals, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}
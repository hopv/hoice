//! Qualifier synthesis in the theory of integers.

use common::* ;
use common::data::HSample ;

use super::{ TermVals, TheoSynth } ;


/// Integer qualifier synthesizer.
pub struct IntSynth {
  /// Expressivity level.
  expressivity: usize,
  /// The int type.
  typ: Typ,
}
impl IntSynth {
  /// Creates a new integer synthesizer.
  pub fn new() -> Self {
    IntSynth {
      expressivity: 0,
      typ: Typ::Int,
    }
  }
}
impl TheoSynth for IntSynth {
  fn typ(& self) -> & Typ { & self.typ }

  fn is_done(& self) -> bool {
    self.expressivity > 1
  }

  fn restart(& mut self) {
    * self = Self::new()
  }

  fn increment(& mut self) {
    self.expressivity += 1
  }

  fn synth<F>(
    & mut self, f: F, sample: & HSample, others: & mut TermVals
  ) -> Res<bool>
  where F: FnMut(Term) -> Res<bool> {
    match self.expressivity {
      0 => simple_int_synth(sample, others, f),
      1 => int_synth_1(sample, others, f),
      _ => Ok(false),
    }
  }

  /// Only generates reals for now (using `to_real`).
  fn project(
    & self, sample: & HSample, typ: & Typ, map: & mut TermVals
  ) -> Res<()> {
    match * typ {
      Typ::Real => for (var, val) in sample.index_iter() {
        match * val {
          Val::I(ref i) => {
            let val = Op::ToReal.eval( vec![ Val::I( i.clone() ) ] ) ? ;
            let prev = map.insert(
              term::to_real( term::var(var) ), val
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


/// Lowest level of int synthesis.
///
/// All `v*` are variables. Synthesizes qualifiers of the form
///
/// - `v = n`, `v <= n`, `v >= n`,
/// - `v_1 = v_2`, `v_1 = - v_2`,
/// - `v_1 + v_2 >= n`, `v_1 + v_2 <= n`,
/// - `v_1 - v_2 >= n`, `v_1 - v_2 <= n`,
pub fn simple_int_synth<F>(
  sample: & HSample, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_int: Vec<(Term, Int)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match * val {
      Val::I(ref val) => {
        let var = term::var(var_idx) ;
        simple_arith_synth! { previous_int, f, int | var = ( val.clone() ) }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val {
      Val::I(val) => {
        simple_arith_synth! { previous_int, f, int | term = val }
      }
      val => bail!(
        "int synthesis expects projected integers, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}


/// Level 1 for int synthesis.
pub fn int_synth_1<F>(
  sample: & HSample, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_int: Vec<(Term, Int)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match * val {
      Val::I(ref val) => {
        let var = term::var(var_idx) ;
        arith_synth_1! { previous_int, f, int | var = ( val.clone() ) }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val {
      Val::I(val) => {
        arith_synth_1! { previous_int, f, int | term = val }
      }
      val => bail!(
        "int synthesis expects projected integers, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}
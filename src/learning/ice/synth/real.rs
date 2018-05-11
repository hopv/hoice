//! Qualifier synthesis in the theory of reals.

use common::* ;

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
      typ: typ::real(),
    }
  }
}
impl TheoSynth for RealSynth {
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
    & mut self, f: F, sample: & Args, others: & mut TermVals,
    _profiler: & Profiler
  ) -> Res<bool>
  where F: FnMut(Term) -> Res<bool> {
    match self.expressivity {
      0 => profile!(
        |_profiler| wrap {
          simple_real_synth(sample, others, f)
        } "learning", "qual", "synthesis", "real", "level 0"
      ),
      1 => profile!(
        |_profiler| wrap {
          real_synth_1(sample, others, f)
        } "learning", "qual", "synthesis", "real", "level 1"
      ),
      _ => Ok(false),
    }
  }

  /// Only generates ints for now (using `to_int`).
  fn project(
    & self, sample: & Args, typ: & Typ, map: & mut TermVals
  ) -> Res<()> {
    match ** typ {
      typ::RTyp::Int => for (var, val) in sample.index_iter() {
        match val.get() {
          & val::RVal::R(ref r) => {
            let val = Op::ToInt.eval( vec![ val::rat( r.clone() ) ] ) ? ;
            let prev = map.insert(
              term::to_int( term::var(var, typ::int()) ), val
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
  sample: & Args, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_real: Vec<(Term, Rat)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match val.get() {
      & val::RVal::R(ref val) => {
        let var = term::var(var_idx, typ::real()) ;
        simple_arith_synth! { previous_real, f, real | var = val }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val.get() {
      & val::RVal::R(ref val) => {
        simple_arith_synth! { previous_real, f, real | term = val }
      }
      val => bail!(
        "real synthesis expects projected reals, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}


/// Level 1 for real synthesis.
pub fn real_synth_1<F>(
  sample: & Args, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_real: Vec<(Term, Int)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match val.get() {
      & val::RVal::I(ref val) => {
        let var = term::var(var_idx, typ::real()) ;
        arith_synth_three_terms! {
          previous_real, f, real | var = ( val.clone() )
        }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val.get() {
      & val::RVal::I(ref val) => {
        arith_synth_three_terms! {
          previous_real, f, real | term = val
        }
      }
      val => bail!(
        "real synthesis expects projected integers, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}


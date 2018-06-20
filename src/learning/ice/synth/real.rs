//! Qualifier synthesis in the theory of reals.

use common::* ;

// use super::helpers::n_term_arith_synth ;
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
    self.expressivity > 2
  }

  fn restart(& mut self) {
    * self = Self::new()
  }

  fn increment(& mut self) {
    self.expressivity += 1
  }

  fn synth<F>(
    & mut self, f: F, sample: & VarVals, others: & mut TermVals,
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
      2 => profile!(
        |_profiler| wrap {
          real_synth_2(sample, others, f)
        } "learning", "qual", "synthesis", "real", "level 2"
      ),
      _ => Ok(false),

      // 0 => profile!(
      //   |_profiler| wrap {
      //     n_term_arith_synth(sample, others, & self.typ, 1, f)
      //   } "learning", "qual", "synthesis", "real", "level 0"
      // ),
      // 1 => profile!(
      //   |_profiler| wrap {
      //     n_term_arith_synth(sample, others, & self.typ, 1, f)
      //   } "learning", "qual", "synthesis", "real", "level 1"
      // ),
      // 2 => profile!(
      //   |_profiler| wrap {
      //     n_term_arith_synth(sample, others, & self.typ, 2, f)
      //   } "learning", "qual", "synthesis", "real", "level 2"
      // ),
      // 3 => profile!(
      //   |_profiler| wrap {
      //     n_term_arith_synth(sample, others, & self.typ, 3, f)
      //   } "learning", "qual", "synthesis", "real", "level 3"
      // ),
      // _ => Ok(false),
    }
  }

  /// Only generates ints for now (using `to_int`).
  fn project(
    & self, sample: & VarVals, typ: & Typ, map: & mut TermVals
  ) -> Res<()> {
    match ** typ {
      typ::RTyp::Int => for (var, val) in sample.index_iter() {
        match val.get() {
          & val::RVal::R(ref r) => {
            let val = Op::ToInt.eval( vec![ val::real( r.clone() ) ] ) ? ;
            let prev = map.insert(
              term::to_int( term::var(var, typ::real()) ), val
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
/// All `v_*` are variables. Synthesizes qualifiers of the form
///
/// - `v = n`, `v <= n`, `v >= n`,
/// - `v_1 = v_2`, `v_1 = - v_2`,
/// - `v_1 + v_2 >= n`, `v_1 + v_2 <= n`,
/// - `v_1 - v_2 >= n`, `v_1 - v_2 <= n`,
pub fn simple_real_synth<F>(
  sample: & VarVals, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_real: Vec<(Term, Rat)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match * val.get() {
      val::RVal::R(ref r) => {
        let var = term::var(var_idx, val.typ().clone()) ;
        simple_arith_synth! { previous_real, f, real | var = ( r.clone() ) }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val.get() {
      val::RVal::R(ref r) => {
        simple_arith_synth! { previous_real, f, real | term = r.clone() }
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
  sample: & VarVals, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_real: Vec<(Term, Rat)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match * val.get() {
      val::RVal::R(ref r) => {
        let var = term::var(var_idx, val.typ().clone()) ;
        arith_synth_non_lin! {
          previous_real, f, real | var = ( r.clone() )
        }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val.get() {
      & val::RVal::R(ref r) => {
        arith_synth_non_lin! {
          previous_real, f, real | term = r.clone()
        }
      }
      val => bail!(
        "real synthesis expects projected reals, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}


/// Level 2 for real synthesis.
pub fn real_synth_2<F>(
  sample: & VarVals, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_real: Vec<(Term, Rat)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match * val.get() {
      val::RVal::R(ref r) => {
        let var = term::var(var_idx, val.typ().clone()) ;
        arith_synth_three_terms! {
          previous_real, f, real | var = ( r.clone() )
        }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val.get() {
      & val::RVal::R(ref r) => {
        arith_synth_three_terms! {
          previous_real, f, real | term = r.clone()
        }
      }
      val => bail!(
        "real synthesis expects projected reals, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}

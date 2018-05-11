//! Qualifier synthesis in the theory of integers.

use common::* ;

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
      typ: typ::int(),
    }
  }
}
impl TheoSynth for IntSynth {
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
    & mut self, f: F, sample: & Args, others: & mut TermVals,
    _profiler: & Profiler
  ) -> Res<bool>
  where F: FnMut(Term) -> Res<bool> {
    match self.expressivity {
      0 => profile!(
        |_profiler| wrap {
          simple_int_synth(sample, others, f)
        } "learning", "qual", "synthesis", "int", "level 0"
      ),
      1 => profile!(
        |_profiler| wrap {
          int_synth_1(sample, others, f)
        } "learning", "qual", "synthesis", "int", "level 1"
      ),
      2 => profile!(
        |_profiler| wrap {
          int_synth_2(sample, others, f)
        } "learning", "qual", "synthesis", "int", "level 2"
      ),
      _ => Ok(false),
    }
  }

  /// Only generates reals for now (using `to_real`).
  fn project(
    & self, sample: & Args, typ: & Typ, map: & mut TermVals
  ) -> Res<()> {
    match ** typ {
      typ::RTyp::Real => for (var, val) in sample.index_iter() {
        match val.get() {
          & val::RVal::I(_) => {
            let val = Op::ToReal.eval( vec![ val.clone() ] ) ? ;
            let prev = map.insert(
              term::to_real( term::var(var, typ::real()) ), val
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
  sample: & Args, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_int: Vec<(Term, Int)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match val.get() {
      & val::RVal::I(ref val) => {
        let var = term::var(var_idx, typ::int()) ;
        simple_arith_synth! { previous_int, f, int | var = val }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val.get() {
      & val::RVal::I(ref val) => {
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
  sample: & Args, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_int: Vec<(Term, Int)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match val.get() {
      & val::RVal::I(ref val) => {
        let var = term::var(var_idx, typ::int()) ;
        arith_synth_non_lin! {
          previous_int, f, int | var = ( val.clone() )
        }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val.get() {
      & val::RVal::I(ref val) => {
        arith_synth_non_lin! {
          previous_int, f, int | term = ( val.clone() )
        }
      }
      val => bail!(
        "int synthesis expects projected integers, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}


/// Level 2 for int synthesis.
pub fn int_synth_2<F>(
  sample: & Args, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_int: Vec<(Term, Int)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match val.get() {
      & val::RVal::I(ref val) => {
        let var = term::var(var_idx, typ::int()) ;
        arith_synth_three_terms! {
          previous_int, f, int | var = ( val.clone() )
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
          previous_int, f, int | term = val
        }
      }
      val => bail!(
        "int synthesis expects projected integers, got {} for {}", val, term
      )
    }
  }

  Ok(false)
}



//! Qualifier synthesis in the theory of integers.

use common::* ;

use super::helpers::n_term_arith_synth ;
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
    self.expressivity > 3
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
          n_term_arith_synth(sample, others, & self.typ, 1, f)
        } "learning", "qual", "synthesis", "int", "level 0"
      ),
      1 => profile!(
        |_profiler| wrap {
          non_lin_int_synth(sample, others, f)
        } "learning", "qual", "synthesis", "int", "level 1"
      ),
      2 => profile!(
        |_profiler| wrap {
          n_term_arith_synth(sample, others, & self.typ, 2, f)
        } "learning", "qual", "synthesis", "int", "level 2"
      ),
      3 => profile!(
        |_profiler| wrap {
          n_term_arith_synth(sample, others, & self.typ, 3, f)
        } "learning", "qual", "synthesis", "int", "level 3"
      ),
      4 => profile!(
        |_profiler| wrap {
          n_term_arith_synth(sample, others, & self.typ, 4, f)
        } "learning", "qual", "synthesis", "int", "level 4"
      ),
      _ => Ok(false),
    }
  }

  /// Only generates reals for now (using `to_real`).
  fn project(
    & self, sample: & VarVals, typ: & Typ, map: & mut TermVals
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


/// Non-linear int synthesis.
pub fn non_lin_int_synth<F>(
  sample: & VarVals, others: & mut TermVals, mut f: F
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

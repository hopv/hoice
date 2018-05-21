//! Qualifier synthesis in the theory of reals.

use common::* ;

use super::helpers::n_term_arith_synth ;
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
          n_term_arith_synth(sample, others, & self.typ, 1, f)
        } "learning", "qual", "synthesis", "real", "level 0"
      ),
      1 => profile!(
        |_profiler| wrap {
          n_term_arith_synth(sample, others, & self.typ, 1, f)
        } "learning", "qual", "synthesis", "real", "level 1"
      ),
      2 => profile!(
        |_profiler| wrap {
          n_term_arith_synth(sample, others, & self.typ, 2, f)
        } "learning", "qual", "synthesis", "real", "level 2"
      ),
      3 => profile!(
        |_profiler| wrap {
          n_term_arith_synth(sample, others, & self.typ, 3, f)
        } "learning", "qual", "synthesis", "real", "level 3"
      ),
      _ => Ok(false),
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

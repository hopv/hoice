//! Qualifier synthesis in the theory of reals.

use super::{helpers::n_term_arith_synth, TermVals, TheoSynth};
use crate::common::*;

/// Real qualifier synthesizer.
pub struct RealSynth {
    /// Expressivity level.
    expressivity: usize,
    /// The real type.
    typ: Typ,
    /// True if the synth is done.
    done: bool,
}
impl Default for RealSynth {
    fn default() -> Self {
        Self::new()
    }
}

impl RealSynth {
    /// Creates a new integer synthesizer.
    pub fn new() -> Self {
        RealSynth {
            expressivity: 0,
            typ: typ::real(),
            done: false,
        }
    }
}
impl TheoSynth for RealSynth {
    fn typ(&self) -> &Typ {
        &self.typ
    }

    fn is_done(&self) -> bool {
        self.done
    }

    fn restart(&mut self) {
        self.done = false;
        self.expressivity = 0
    }

    fn increment(&mut self) {
        self.expressivity += 1
    }

    fn synth<F>(
        &mut self,
        mut f: F,
        sample: &VarVals,
        others: &mut TermVals,
        _profiler: &Profiler,
    ) -> Res<bool>
    where
        F: FnMut(Term) -> Res<bool>,
    {
        self.done = false;
        match self.expressivity {
            0 => profile!(
              |_profiler| wrap {
                let done = n_term_arith_synth(
                  sample, others, & self.typ, 1, & mut f
                ) ? ;
                if ! done {
                  n_term_arith_synth(sample, others, & self.typ, 2, f)
                } else {
                  Ok(true)
                }
              } "learning", "qual", "synthesis", "real", "level 0"
            ),

            1 => profile!(
              |_profiler| wrap {
                non_lin_real_synth(sample, others, f)
              } "learning", "qual", "synthesis", "real", "level 1"
            ),

            n if n < 3 => profile!(
              |_profiler| wrap {
                n_term_arith_synth(sample, others, & self.typ, n + 1, f)
              } "learning", "qual", "synthesis", "real", "level n > 1"
            ),

            _ => {
                self.done = true;
                Ok(false)
            }
        }
    }

    /// Only generates ints for now (using `to_int`).
    fn project(&self, sample: &VarVals, typ: &Typ, map: &mut TermVals) -> Res<()> {
        if let typ::RTyp::Int = **typ {
            for (var, val) in sample.index_iter() {
                if let val::RVal::R(ref r) = val.get() {
                    let val = Op::ToInt.eval(vec![val::real(r.clone())])?;
                    let prev = map.insert(term::to_int(term::var(var, typ::real())), val);
                    debug_assert_eq!(prev, None)
                }
            }
        }
        Ok(())
    }
}

/// Level 1 for real synthesis.
pub fn non_lin_real_synth<F>(sample: &VarVals, others: &mut TermVals, mut f: F) -> Res<bool>
where
    F: FnMut(Term) -> Res<bool>,
{
    let mut previous_real: BTreeSet<(Term, Rat)> = BTreeSet::new();

    // Iterate over the sample.
    for (var_idx, val) in sample.index_iter() {
        if let val::RVal::R(ref r) = val.get() {
            let var = term::var(var_idx, val.typ().clone());
            arith_synth_non_lin! {
              previous_real, f, real | var = ( r.clone() )
            }
        }
    }

    // Iterate over the cross-theory terms.
    for (term, val) in others.drain() {
        if let val::RVal::R(ref r) = val.get() {
            arith_synth_non_lin! {
              previous_real, f, real | term = r.clone()
            }
        } else {
            bail!(
                "real synthesis expects projected reals, got {} for {}",
                val,
                term
            )
        }
    }

    Ok(false)
}

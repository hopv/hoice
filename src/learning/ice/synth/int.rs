//! Qualifier synthesis in the theory of integers.

use super::{helpers::n_term_arith_synth, TermVals, TheoSynth};
use crate::common::*;

/// Integer qualifier synthesizer.
pub struct IntSynth {
    /// Expressivity level.
    expressivity: usize,
    /// The int type.
    typ: Typ,
    /// True if the synth is done.
    done: bool,
}
impl Default for IntSynth {
    fn default() -> Self {
        Self::new()
    }
}

impl IntSynth {
    /// Creates a new integer synthesizer.
    pub fn new() -> Self {
        IntSynth {
            expressivity: 0,
            typ: typ::int(),
            done: false,
        }
    }
}
impl TheoSynth for IntSynth {
    fn typ(&self) -> &Typ {
        &self.typ
    }

    fn is_done(&self) -> bool {
        self.done
    }

    fn restart(&mut self) {
        self.done = false;
        self.expressivity = 0;
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
              } "learning", "qual", "synthesis", "int", "level 0"
            ),

            1 => profile!(
              |_profiler| wrap {
                non_lin_int_synth(sample, others, f)
              } "learning", "qual", "synthesis", "int", "level 1"
            ),

            n if n < sample.len() => profile!(
              |_profiler| wrap {
                n_term_arith_synth(sample, others, & self.typ, n + 1, f)
              } "learning", "qual", "synthesis", "int", "level n > 1"
            ),

            _ => {
                self.done = true;
                Ok(false)
            }
        }
    }

    /// Only generates reals for now (using `to_real`).
    fn project(&self, sample: &VarVals, typ: &Typ, map: &mut TermVals) -> Res<()> {
        if typ.is_real() {
            for (var, val) in sample.index_iter() {
                if let val::RVal::I(_) = val.get() {
                    let val = Op::ToReal.eval(vec![val.clone()])?;
                    let prev = map.insert(term::to_real(term::var(var, typ::int())), val);
                    debug_assert_eq!(prev, None)
                }
            }
        }
        Ok(())
    }
}

/// Non-linear int synthesis.
pub fn non_lin_int_synth<F>(sample: &VarVals, others: &mut TermVals, mut f: F) -> Res<bool>
where
    F: FnMut(Term) -> Res<bool>,
{
    let mut previous_int: BTreeSet<(Term, Int)> = BTreeSet::new();

    // Iterate over the sample.
    for (var_idx, val) in sample.index_iter() {
        if let val::RVal::I(ref val) = val.get() {
            let var = term::var(var_idx, typ::int());
            arith_synth_non_lin! {
              previous_int, f, int | var = ( val.clone() )
            }
        }
    }

    // Iterate over the cross-theory terms.
    for (term, val) in others.drain() {
        match val.get() {
            &val::RVal::I(ref val) => {
                arith_synth_non_lin! {
                  previous_int, f, int | term = ( val.clone() )
                }
            }
            val => bail!(
                "int synthesis expects projected integers (1), \
                 got {} for {}",
                val,
                term
            ),
        }
    }

    Ok(false)
}

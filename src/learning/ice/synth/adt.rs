//! ADT qualifier synthesis.

use crate::{common::*, fun::Functions};

use super::{TermVals, TheoSynth};

#[derive(Clone, Debug)]
pub struct AdtSynth {
    /// Expressivity level.
    expressivity: usize,
    /// Type this synthesizer handles.
    typ: Typ,
    /// Functions relevant for this type.
    pub funs: Functions,
}
impl PartialEq for AdtSynth {
    fn eq(&self, other: &Self) -> bool {
        self.typ == other.typ
    }
}
impl Eq for AdtSynth {}

impl ::std::hash::Hash for AdtSynth {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: ::std::hash::Hasher,
    {
        self.typ.hash(hasher)
    }
}

impl PartialOrd for AdtSynth {
    fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
        self.typ.partial_cmp(&other.typ)
    }
}
impl Ord for AdtSynth {
    fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
        self.typ.cmp(&other.typ)
    }
}

impl AdtSynth {
    /// Bails by saying the internal is inconsistent.
    #[inline]
    fn typ_problem(&self) -> Error {
        "inconsistent type for ADT synth".into()
    }
    /// Retrieves the content of an option or bails.
    #[inline]
    fn get_opt<T>(&self, opt: Option<T>) -> Res<T> {
        if let Some(t) = opt {
            Ok(t)
        } else {
            bail!(self.typ_problem())
        }
    }

    /// Projects a single value.
    fn project_val(&self, typ: &Typ, var: VarIdx, val: &Val, map: &mut TermVals) -> Res<()> {
        if !val.is_known() || val.typ() != self.typ {
            return Ok(());
        }

        let var = term::var(var, self.typ.clone());

        // Apply unary functions from `self.typ` to `typ`.
        for fun in &self.funs.from_typ {
            if &fun.typ != typ {
                continue;
            }

            let input: VarMap<_> = vec![val.clone()].into();

            let val = fun
                .def
                .eval(&input)
                .chain_err(|| format!("while evaluating ({} {})", fun.name, val))?;

            let term = term::fun(fun.name.clone(), vec![var.clone()]);

            let prev = map.insert(term, val);
            debug_assert! { prev.is_none() }
        }

        // Retrieve this value's constructor.
        let (val_typ, val_cons, val_args) = self.get_opt(val.dtyp_inspect())?;
        debug_assert_eq! { val_typ, & self.typ }

        // Apply selectors from the variant of `val` to `typ`.
        let (val_dtyp, _) = self.get_opt(val_typ.dtyp_inspect())?;

        let selectors = self.get_opt(val_dtyp.news.get(val_cons))?;

        debug_assert_eq! { selectors.len(), val_args.len() }

        for ((slc, _), val_arg) in selectors.iter().zip(val_args.iter()) {
            if &val_arg.typ() == typ {
                let term = term::dtyp_slc(typ.clone(), slc.clone(), var.clone());
                let prev = map.insert(term, val_arg.clone());
                debug_assert! { prev.is_none() }
            }
        }

        Ok(())
    }
}

impl TheoSynth for AdtSynth {
    fn typ(&self) -> &Typ {
        &self.typ
    }

    fn is_done(&self) -> bool {
        self.expressivity > 0
    }

    fn restart(&mut self) {
        self.expressivity = 0
    }

    fn increment(&mut self) {
        self.expressivity += 1
    }

    fn synth<F>(
        &mut self,
        f: F,
        sample: &VarVals,
        others: &mut TermVals,
        _profiler: &Profiler,
    ) -> Res<bool>
    where
        F: FnMut(Term) -> Res<bool>,
    {
        match self.expressivity {
            0 => self.eq_synth(f, sample, others),

            _ => Ok(false),
        }
    }

    fn project(&self, sample: &VarVals, typ: &Typ, map: &mut TermVals) -> Res<()> {
        for (var, val) in sample.index_iter() {
            self.project_val(typ, var, val, map)?
        }

        Ok(())
    }
}

impl AdtSynth {
    /// Constructor.
    pub fn new(typ: Typ) -> Self {
        let funs = Functions::new(typ.clone());
        AdtSynth {
            expressivity: 0,
            typ,
            funs,
        }
    }

    /// True if the synthesizer can project values to int.
    pub fn can_project_to_int(&self) -> bool {
        for fun in &self.funs.from_typ {
            if fun.typ.is_int() {
                return true;
            }
        }
        false
    }

    /// True if the synthesizer can project values to real.
    pub fn can_project_to_real(&self) -> bool {
        for fun in &self.funs.from_typ {
            if fun.typ.is_real() {
                return true;
            }
        }
        false
    }

    /// Generates equalities between variables of some ADT.
    fn eq_synth<F>(&self, mut f: F, sample: &VarVals, others: &mut TermVals) -> Res<bool>
    where
        F: FnMut(Term) -> Res<bool>,
    {
        let mut previous: BTreeSet<(Term, Val)> = BTreeSet::new();

        for (var, val) in sample.index_iter() {
            if val.is_known() && val.typ() == self.typ {
                let var = term::var(var, self.typ.clone());

                let mut extended = Vec::with_capacity(self.funs.from_to_typ.len() + 1);

                if f(term::eq(var.clone(), term::cst(val.clone())))? {
                    return Ok(true);
                }

                let mut input: Option<VarMap<Val>> = None;

                for fun in &self.funs.from_to_typ {
                    let input = input.get_or_insert_with(|| vec![val.clone()].into());

                    let val = fun
                        .def
                        .eval(input)
                        .chain_err(|| format!("while evaluating ({} {})", fun.name, val))?;

                    extended.push((term::fun(fun.name.clone(), vec![var.clone()]), val))
                }

                extended.push((var, val.clone()));

                for (t_1, v_1) in extended {
                    for (t_2, _) in previous.iter().map(|(t, v)| (t, v)).chain(others.iter()) {
                        if f(term::eq(t_1.clone(), t_2.clone()))? {
                            return Ok(true);
                        }
                    }

                    previous.insert((t_1, v_1));
                }
            }
        }

        Ok(false)
    }
}

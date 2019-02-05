use crate::{common::*, var_to::vals::VarValsSet};

use super::Sample;

/// Constraints using hashconsed samples.
///
/// - `None` means false, for lhs and rhs.
/// - empty lhs means true
///
/// A constraint is a tautology iff `lhs.is_none()` and `rhs.is_none()`.
///
/// # Invariants
///
/// - `lhs.is_none() => rhs.is_none()`
/// - constraints cannot contain partial samples
/// - `lhs` cannot map to an empty `VarValsSet` (Hence, do not access `lhs`
///   directly for sample removal. Use [`lhs_rm`][lhs rm].)
/// - `lhs` cannot contain a sample that subsumes `rhs`.
///
/// [lhs rm]: #method.lhs_rm (lhs_rm function)
#[derive(Clone, Debug)]
pub struct Constraint {
    /// Left-hand side.
    lhs: Option<PrdHMap<VarValsSet>>,
    /// Right-hand side.
    rhs: Option<Sample>,
}

impl Constraint {
    /// Constructor.
    ///
    /// None if the constraint is a tautology:
    ///
    /// - `lhs.is_empty` and `rhs.is_empty()`
    pub fn new(lhs: PrdHMap<VarValsSet>, rhs: Option<Sample>) -> Constraint {
        Constraint {
            lhs: Some(lhs),
            rhs,
        }
    }

    /// Checks itself.
    ///
    /// See `Constraint`'s documentation for the list of invariant.
    #[cfg(not(debug_assertions))]
    pub fn check(&self) -> Res<()> {
        Ok(())
    }
    /// Checks itself.
    ///
    /// See `Constraint`'s documentation for the list of invariant.
    #[cfg(debug_assertions)]
    pub fn check(&self) -> Res<()> {
        if self.lhs.is_none() && self.rhs.is_some() {
            bail!("lhs is empty but rhs is not none")
        }
        if let Some(lhs) = self.lhs() {
            for (_, argss) in lhs {
                if argss.is_empty() {
                    bail!("lhs maps a predicate to nothing")
                }
                for args in argss {
                    if args.is_partial() {
                        bail!("partial arguments in constraint ({})", args)
                    }
                }
            }
        }
        if let Some(Sample { ref args, .. }) = self.rhs {
            if args.is_partial() {
                bail!("partial arguments in constraint ({})", args)
            }
        }
        if let Some(Sample { pred, ref args }) = self.rhs {
            if let Some(argss) = self.lhs.as_ref().and_then(|map| map.get(&pred)) {
                if args.set_subsumed(argss) {
                    bail!("rhs is subsumed by lhs")
                }
            }
        }

        Ok(())
    }

    /// Number of samples in the lhs.
    pub fn lhs_len(&self) -> usize {
        let mut count = 0;
        if let Some(lhs) = self.lhs.as_ref() {
            for samples in lhs.values() {
                count += samples.len()
            }
        }
        count
    }

    /// Lhs accessor.
    pub fn lhs(&self) -> Option<&PrdHMap<VarValsSet>> {
        self.lhs.as_ref()
    }
    /// Rhs accessor.
    pub fn rhs(&self) -> Option<&Sample> {
        self.rhs.as_ref()
    }

    /// Removes samples subsumed by a sample from the lhs.
    ///
    /// Returns the number of sample removed.
    ///
    /// This function guarantees that `lhs` does not map to an empty `VarValsSet`,
    /// so please use this. Do not access `lhs` directly for sample removal.
    fn lhs_rm(&mut self, pred: PrdIdx, args: &VarVals) -> usize {
        self.lhs
            .as_mut()
            .map(|lhs| {
                let (pred_rm, rmed) = if let Some(argss) = lhs.get_mut(&pred) {
                    let mut rmed = if argss.remove(args) { 1 } else { 0 };
                    if conf.teacher.partial && args.is_partial() {
                        let (subsumed, nu_rmed) = args.set_subsumed_rm(argss);
                        debug_assert! { ! subsumed }
                        rmed += nu_rmed
                    }
                    (argss.is_empty(), rmed)
                } else {
                    (false, 0)
                };
                if pred_rm {
                    let prev = lhs.remove(&pred);
                    debug_assert! { prev.is_some() }
                }
                rmed
            })
            .unwrap_or(0)
    }

    /// Transforms a constraint in a tautology.
    ///
    /// Applies `f` to all samples.
    pub fn tautologize<F>(&mut self, mut f: F) -> Res<()>
    where
        F: FnMut(PrdIdx, VarVals) -> Res<()>,
    {
        let rhs = ::std::mem::replace(&mut self.rhs, None);
        if let Some(Sample { pred, args }) = rhs {
            f(pred, args)?
        }

        if let Some(lhs) = self.lhs.as_mut() {
            for (pred, argss) in lhs.drain() {
                for args in argss {
                    f(pred, args)?
                }
            }
        }
        self.lhs = None;
        Ok(())
    }

    /// Checks whether the lhs of the constraint is empty.
    pub fn is_tautology(&self) -> bool {
        if self.lhs.is_none() {
            debug_assert!(self.rhs.is_none());
            true
        } else {
            false
        }
    }

    /// Constraint comparison.
    ///
    /// Returns `Greater` if both
    ///
    /// - `None` if one of the constraints is a tautology
    /// - `Greater` if `self.rhs == other.rhs` and `self.lhs` is a subset of
    ///   `other.rhs`
    /// - `Less` in the dual case from above
    /// - `None` otherwise
    ///
    /// So `c >= c'` means `c` has a lhs strictly more generic than `c'`, so `c'`
    /// is redundant.
    ///
    /// Error if `self` or `other` is a tautology.
    pub fn compare(&self, other: &Constraint) -> Res<Option<::std::cmp::Ordering>> {
        use std::cmp::Ordering;

        if self.is_tautology() {
            bail!("self is tautology")
        } else if other.is_tautology() {
            bail!("other is tautology")
        }

        if self.rhs != other.rhs {
            Ok(None)
        } else {
            let (reversed, c_1, c_2) = match self.lhs_len().cmp(&other.lhs_len()) {
                Ordering::Less => (false, self, other),
                Ordering::Equal => {
                    if self == other {
                        return Ok(Some(Ordering::Equal));
                    } else {
                        return Ok(None);
                    }
                }
                Ordering::Greater => (true, other, self),
            };

            match (c_1.lhs.as_ref(), c_2.lhs.as_ref()) {
                (Some(lhs_1), Some(lhs_2)) => {
                    for (pred, samples_1) in lhs_1 {
                        if let Some(samples_2) = lhs_2.get(pred) {
                            if !samples_1.is_subset(samples_2) {
                                return Ok(None);
                            }
                        } else {
                            return Ok(None);
                        }
                    }
                }
                // Should be unreachable.
                (None, _) | (_, None) => unreachable!(),
            }

            if reversed {
                Ok(Some(Ordering::Less))
            } else {
                Ok(Some(Ordering::Greater))
            }
        }
    }

    /// Sets a sample in the constraint.
    ///
    /// Returns true if the constraint became a tautology. In this case,
    /// `self.tautologize(if_tautology)` is called **after** removing the
    /// specified sample.
    ///
    /// Error if the sample was not there.
    pub fn force_sample<F>(
        &mut self,
        pred: PrdIdx,
        args: &VarVals,
        pos: bool,
        if_tautology: F,
    ) -> Res<bool>
    where
        F: FnMut(PrdIdx, VarVals) -> Res<()>,
    {
        let rmed = self.lhs_rm(pred, args);
        let was_in_lhs = rmed > 0;

        let is_in_rhs = if let Some(Sample {
            pred: rhs_pred,
            args: ref mut rhs_args,
        }) = self.rhs
        {
            rhs_pred == pred && args.subsumes(rhs_args)
        } else {
            false
        };

        let was_in_rhs = if is_in_rhs {
            self.rhs = None;
            true
        } else {
            false
        };

        if (was_in_lhs && !pos) || (was_in_rhs && pos) {
            self.tautologize(if_tautology)?;
            return Ok(true);
        }

        if !was_in_rhs && !was_in_lhs {
            bail!("asked to remove sample from a clause where it wasn't")
        }

        Ok(false)
    }

    /// Forces all samples of a predicate to `pos`.
    ///
    /// Returns `true` iff the constraint became a tautology. In this case,
    /// `self.tautologize(if_tautology)` is called **after** removing all
    /// applications of `pred`.
    pub fn force<F>(&mut self, pred: PrdIdx, pos: bool, if_tautology: F) -> Res<bool>
    where
        F: FnMut(PrdIdx, VarVals) -> Res<()>,
    {
        let mut tautology = false;
        if self
            .rhs
            .as_ref()
            .map(|&Sample { pred: p, .. }| p == pred)
            .unwrap_or(false)
        {
            self.rhs = None;
            if pos {
                tautology = true
            }
        }
        if let Some(ref mut lhs) = self.lhs {
            if lhs.remove(&pred).is_some() && !pos {
                tautology = true
            }
        }
        if tautology {
            self.tautologize(if_tautology)?
        }
        Ok(tautology)
    }

    /// Checks if the constraint is trivial.
    ///
    /// - `Left(sample, true)` if the constraint is `true => sample` (`sample`
    ///   needs to be true)
    /// - `Left(sample, false)` if the constraint is `sample => false` (`sample`
    ///   needs to be false)
    /// - `Right(true)` if the constraint is a contradiction `true => false`
    /// - `Right(false)` otherwise.
    ///
    /// If the result isn't `Right(_)`, the sample returned has been removed and
    /// the constraint is now a tautology.
    pub fn try_trivial(&mut self) -> Either<(Sample, bool), bool> {
        if self.lhs().map(|lhs| lhs.is_empty()).unwrap_or(false) {
            let mut rhs = None;
            ::std::mem::swap(&mut rhs, &mut self.rhs);
            let mut lhs = None;
            ::std::mem::swap(&mut lhs, &mut self.lhs);

            if let Some(s) = rhs {
                Either::Left((s, true))
            } else {
                // true => false
                return Either::Right(true);
            }
        } else if self.rhs.is_none() {
            if let Some(lhs) = self.lhs() {
                let mut first = true;
                for (_, argss) in lhs.iter() {
                    for _ in argss {
                        if first {
                            first = false
                        } else {
                            return Either::Right(false);
                        }
                    }
                }
            } else {
                return Either::Right(false);
            }

            let mut old_lhs = None;
            ::std::mem::swap(&mut self.lhs, &mut old_lhs);

            // Only reachable if there's one pred app in lhs.
            let (pred, argss) = old_lhs.unwrap().into_iter().next().unwrap();
            let args = argss.into_iter().next().unwrap();
            Either::Left((Sample { pred, args }, false))
        } else {
            Either::Right(false)
        }
    }
}

impl<'a> PebcakFmt<'a> for Constraint {
    type Info = &'a Preds;
    fn pebcak_err(&self) -> ErrorKind {
        "during constraint pebcak formatting".into()
    }
    fn pebcak_io_fmt<W: Write>(&self, w: &mut W, map: &'a Preds) -> IoRes<()> {
        if let Some(ref lhs) = self.lhs {
            if lhs.is_empty() {
                write!(w, "true ")?
            }
            for (pred, samples) in lhs {
                for sample in samples {
                    write!(w, "({} {}) ", map[*pred], sample)?
                }
            }
        } else {
            write!(w, "false ")?
        }
        write!(w, "=> ")?;
        if let Some(ref rhs) = self.rhs {
            rhs.pebcak_io_fmt(w, map)
        } else {
            write!(w, "false")
        }
    }
}

mylib::impl_fmt! {
    Constraint(self, fmt) {
        if let Some(ref lhs) = self.lhs {
            if lhs.is_empty() {
                write!(fmt, "true ") ?
            }
            for (pred, samples) in lhs {
                for sample in samples {
                    write!(fmt, "(p_{} {}) ", pred, sample) ?
                }
            }
        } else {
            write!(fmt, "false ") ?
        }
        write!(fmt, "=> ") ? ;
        if let Some(ref rhs) = self.rhs {
            write!(fmt, "{}", rhs)
        } else {
            write!(fmt, "false")
        }
    }
}

impl Eq for Constraint {}
impl PartialEq for Constraint {
    fn eq(&self, other: &Constraint) -> bool {
        if self.rhs == other.rhs {
            match (self.lhs.as_ref(), other.lhs.as_ref()) {
                (Some(lhs_1), Some(lhs_2)) => {
                    for ((lhs_pred, lhs_samples), (rhs_pred, rhs_samples)) in
                        lhs_1.iter().zip(lhs_2.iter())
                    {
                        if lhs_pred == rhs_pred && lhs_samples.len() == rhs_samples.len() {
                            for (lhs_sample, rhs_sample) in
                                lhs_samples.iter().zip(rhs_samples.iter())
                            {
                                if lhs_sample != rhs_sample {
                                    return false;
                                }
                            }
                        } else {
                            return false;
                        }
                    }
                    true
                }
                (None, None) => true,
                (None, Some(_)) | (Some(_), None) => false,
            }
        } else {
            false
        }
    }
}

//! Hashconsed maps from variables to terms.

use std::cmp::Ordering;

use hashconsing::{HConsed, HashConsign};

use crate::common::*;

hashconsing::consign! {
    /// Term factory.
    let factory = consign(conf.instance.term_capa) for RVarVals ;
}

/// Creates hashconsed arguments.
pub fn new<RA: Into<RVarVals>>(args: RA) -> VarVals {
    factory.mk(args.into())
}
/// Creates hashconsed arguments, returns `true` if the arguments are actually
/// new.
pub fn new_is_new<RA: Into<RVarVals>>(args: RA) -> (VarVals, bool) {
    factory.mk_is_new(args.into())
}
/// Creates hashconsed arguments from iterators.
pub fn of<V: Into<Val>, A: IntoIterator<Item = V>>(args: A) -> VarVals {
    let mut map = VarMap::new();
    for val in args {
        map.push(val.into())
    }
    new(map)
}

/// Mapping from variables to values, used for learning data.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct RVarVals {
    /// Internal map.
    map: VarMap<Val>,
}

mylib::impl_fmt! {
    RVarVals(self, fmt) {
        self.map.fmt(fmt)
    }
}
impl ::std::ops::Deref for RVarVals {
    type Target = VarMap<Val>;
    fn deref(&self) -> &VarMap<Val> {
        &self.map
    }
}
impl ::std::ops::DerefMut for RVarVals {
    fn deref_mut(&mut self) -> &mut VarMap<Val> {
        &mut self.map
    }
}
impl From<VarMap<Val>> for RVarVals {
    fn from(map: VarMap<Val>) -> Self {
        RVarVals { map }
    }
}
impl From<Vec<Val>> for RVarVals {
    fn from(map: Vec<Val>) -> Self {
        RVarVals { map: map.into() }
    }
}
impl Evaluator for RVarVals {
    #[inline]
    fn get(&self, var: VarIdx) -> &Val {
        &self.map[var]
    }
    #[inline]
    fn len(&self) -> usize {
        VarMap::len(&self.map)
    }
    fn print(&self) {
        println!("varvals@");
        self.map.print();
    }
}

impl RVarVals {
    /// Constructor with some capacity.
    pub fn with_capacity(capa: usize) -> Self {
        Self {
            map: VarMap::with_capacity(capa),
        }
    }

    /// True if at least one value is `Val::N`.
    pub fn is_partial(&self) -> bool {
        self.iter().any(|v| !v.is_known())
    }

    /// True if the two args are semantically the same.
    ///
    /// "Semantically" here means that `Val::N` is not equal to itself.
    pub fn equal(&self, other: &Self) -> bool {
        for (v_1, v_2) in self.map.iter().zip(other.map.iter()) {
            if !v_1.equal(v_2) {
                return false;
            }
        }
        true
    }

    /// Constructor from a model.
    pub fn of_model<T>(
        info: &VarMap<crate::info::VarInfo>,
        model: Vec<(VarIdx, T, Val)>,
        partial: bool,
    ) -> Res<Self> {
        let mut slf = RVarVals {
            map: info
                .iter()
                .map(|info| {
                    if partial {
                        val::none(info.typ.clone())
                    } else {
                        info.typ.default_val()
                    }
                })
                .collect(),
        };
        for (var, _, val) in model {
            slf[var] = val.cast(&info[var].typ)?;
        }
        Ok(slf)
    }

    /// Constructor from a model for a predicate.
    pub fn of_pred_model<T>(sig: &Sig, model: Vec<(VarIdx, T, Val)>, partial: bool) -> Res<Self> {
        let mut slf = RVarVals {
            map: sig
                .iter()
                .map(|typ| {
                    if partial {
                        val::none(typ.clone())
                    } else {
                        typ.default_val()
                    }
                })
                .collect(),
        };
        for (var, _, val) in model {
            slf[var] = val.cast(&sig[var])?;
        }
        Ok(slf)
    }

    /// Evaluates some arguments and yields the resulting `VarMap`.
    pub fn apply_to(&self, args: &VarMap<Term>) -> Res<Self> {
        let mut res = Self::with_capacity(args.len());
        for arg in args {
            res.push(arg.eval(self)?)
        }
        Ok(res)
    }
}

/// Hash consed arguments.
pub type VarVals = HConsed<RVarVals>;

/// A set of hashconsed arguments.
pub type VarValsSet = HConSet<VarVals>;

/// A map from hashconsed arguments to something.
pub type VarValsMap<T> = HConMap<VarVals, T>;

/// Helper functions for `VarVals`.
pub trait SubsumeExt {
    /// Type of the sets we want to check for subsumption.
    type Set;

    /// Compares two arguments w.r.t. subsumption.
    ///
    /// Returns
    ///
    /// - `Some(Greater)` if `self` subsumes `other`,
    /// - `Some(Equal)` if `self` is equal to `other`,
    /// - `Some(Less)` if `other` subsumes `self`,
    /// - `None` if `self` and `other` cannot be compared.
    ///
    /// Returns an error if `self` and `other` do not have the same length.
    fn compare(&self, other: &Self) -> Option<Ordering>;

    /// True if two samples are complementary.
    ///
    /// Two samples are complementary iff for all `i`
    ///
    /// - `v_i` is a non-value, or
    /// - `v'_i` is a non-value, or
    /// - `v_1 == v'_i`.
    fn is_complementary(&self, other: &Self) -> bool;

    /// Returns true if the two samples are related.
    ///
    /// Two samples are related if they're equal or one subsumes the other.
    fn is_related_to(&self, other: &Self) -> bool {
        self.compare(other).is_some()
    }

    /// True iff `self` subsumes or is equal to `other`.
    fn subsumes(&self, other: &Self) -> bool {
        match self.compare(other) {
            Some(Ordering::Greater) | Some(Ordering::Equal) => true,
            _ => false,
        }
    }
    /// True iff `other` subsumes or is equal to `self`.
    fn subsumed(&self, other: &Self) -> bool {
        other.subsumes(self)
    }

    /// Checks whether `self` is subsumed by anything in the set.
    ///
    /// Returns `(b, n)`:
    ///
    /// - `b` indicates whether `self` is subsumed
    /// - `n` is the number of elements removed because they were subsumed
    ///   by `self`
    ///
    /// Generally speaking, it is expected that `n > 0 => ! b`. In particular, if
    /// `self` is in the set the expected output is `(true, 0)`.
    fn set_subsumed_rm(&self, set: &mut Self::Set) -> (bool, usize);

    /// Checks whether `self` is subsumed by anything in the set.
    ///
    /// Same as `set_subsumed_rm`, but does remove anything.
    fn set_subsumed(&self, set: &Self::Set) -> bool;
}
impl SubsumeExt for VarVals {
    type Set = VarValsSet;

    fn is_complementary(&self, other: &Self) -> bool {
        for (val, other_val) in self.iter().zip(other.iter()) {
            if val.is_known() && other_val.is_known() && val != other_val {
                return false;
            }
        }
        true
    }

    fn compare(&self, other: &Self) -> Option<Ordering> {
        debug_assert_eq! { self.len(), other.len() }

        if self == other {
            return Some(Ordering::Equal);
        }

        if !conf.teacher.partial {
            None
        } else {
            let (mut less, mut greater) = (true, true);

            for (val, other_val) in self.iter().zip(other.iter()) {
                greater = greater && (!val.is_known() || val == other_val);
                less = less && (!other_val.is_known() || val == other_val);
            }

            match (less, greater) {
                (false, false) => None,
                (true, false) => Some(Ordering::Less),
                (false, true) => Some(Ordering::Greater),
                (true, true) => fail_with!("Fatal error in sample hashconsing"),
            }
        }
    }

    fn set_subsumed(&self, set: &Self::Set) -> bool {
        if !conf.teacher.partial {
            set.contains(self)
        } else {
            for elem in set.iter() {
                if elem.subsumes(self) {
                    return true;
                }
            }
            false
        }
    }

    fn set_subsumed_rm(&self, set: &mut VarValsSet) -> (bool, usize) {
        if !conf.teacher.partial {
            (set.contains(self), 0)
        } else if !self.is_partial() {
            for elem in set.iter() {
                if elem.subsumes(self) {
                    return (true, 0);
                }
            }
            (false, 0)
        } else {
            let mut subsumed = false;
            let mut count = 0;
            set.retain(|other| match self.compare(other) {
                Some(Ordering::Equal) => {
                    subsumed = true;
                    true
                }
                Some(Ordering::Greater) => {
                    count += 1;
                    false
                }
                Some(Ordering::Less) => {
                    subsumed = true;
                    true
                }
                None => true,
            });
            (subsumed, count)
        }
    }
}

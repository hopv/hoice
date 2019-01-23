//! Zero-cost wrappers for safe indexing.

use std::fmt;
use std::io::Write;

use mylib::wrap_usize;
use rsmt2::print::*;

use crate::{
    common::{var_to, SmtRes, VarIndexed, VarTerms},
    term::Term,
};

wrap_usize! {
    #[doc = "Predicate indices."]
    PrdIdx
    #[doc = "Range over predicates."]
    range: PrdRange
    #[doc = "Set of predicates."]
    set: PrdSet
    #[doc = "Hash map from predicates to something."]
    hash map: PrdHMap
    #[doc = "Total map from predicates to something."]
    map: PrdMap with iter: PrdMapIter
}

wrap_usize! {
    #[doc = "Variable indices."]
    VarIdx
    #[doc = "Range over variables."]
    range: VarRange
    #[doc = "Set of variables."]
    set: VarSet
    #[doc = "Hash map from variables to something."]
    hash map: VarHMap
    #[doc = "Total map from variables to something."]
    map: VarMap with iter: VarMapIter
}
impl VarIdx {
    /// Default way to write variables: `v_<idx>`.
    pub fn default_write<W>(self, w: &mut W) -> ::std::io::Result<()>
    where
        W: Write,
    {
        write!(w, "v_{}", self)
    }
    /// Default string representation of a variable.
    pub fn default_str(self) -> String {
        let mut s = vec![];
        self.default_write(&mut s).unwrap();
        ::std::str::from_utf8(&s).unwrap().into()
    }

    /// Default way to write variables: `v_<idx>`.
    pub fn write<W>(w: &mut W, var: Self) -> ::std::io::Result<()>
    where
        W: Write,
    {
        var.default_write(w)
    }
}

impl Into<VarTerms> for VarMap<Term> {
    fn into(self) -> VarTerms {
        var_to::terms::new(self)
    }
}

impl VarMap<Term> {
    /// Removes the arguments of indices **not** in the set. Preserves the order.
    ///
    /// This is used when useless arguments are detected, to slice predicate
    /// applications.
    pub fn remove(&self, to_keep: &VarSet) -> VarTerms {
        debug_assert! { self.len() >= to_keep.len() }
        debug_assert! {{
          let mut okay = true ;
          for var in to_keep {
            if * var >= self.len() {
              okay = false ; break
            }
          }
          okay
        }}
        let mut nu_args = VarMap::with_capacity(self.len());
        for (var, term) in self.index_iter() {
            if to_keep.contains(&var) {
                nu_args.push(term.clone())
            }
        }
        nu_args.into()
    }

    /// Variable substitution.
    pub fn subst<Map: VarIndexed<Term>>(&self, map: &Map) -> Self {
        let mut var_map = VarMap::with_capacity(self.len());
        for term in self.iter() {
            let (term, _) = term.subst(map);
            var_map.push(term)
        }
        var_map
    }

    /// True if all terms are different variables.
    pub fn are_diff_vars(&self) -> bool {
        let mut iter = self.iter();
        while let Some(term) = iter.next() {
            if term.var_idx().is_some() {
                for other in iter.clone() {
                    if term == other {
                        return false;
                    }
                }
            } else {
                // Not a var.
                return false;
            }
        }
        true
    }
}

impl<T: fmt::Display> fmt::Display for VarMap<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        mylib::for_first! {
          self.iter() => {
            |fst| write!(fmt, "{}", fst) ?,
            then |nxt| write!(fmt, " {}", nxt) ?
          }
        }
        Ok(())
    }
}

impl<T: Copy> Sym2Smt<T> for VarIdx {
    fn sym_to_smt2<Writer>(&self, w: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: Write,
    {
        self.default_write(w)?;
        Ok(())
    }
}

impl<T: Copy> Expr2Smt<T> for VarIdx {
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: Write,
    {
        self.sym_to_smt2(w, &())
    }
}

wrap_usize! {
    #[doc = "Arity."]
    Arity
    #[doc = "Range over arity."]
    range: ArityRange
    #[doc = "Total map from Arity to something."]
    map: ArityMap with iter: ArityMapIter
}

wrap_usize! {
    #[doc = "Clause indices."]
    ClsIdx
    #[doc = "Range over clauses."]
    range: ClsRange
    #[doc = "Set of clauses."]
    set: ClsSet
    #[doc = "Hash map from clauses to something."]
    hash map: ClsHMap
    #[doc = "Total map from clauses to something."]
    map: ClsMap with iter: ClsMapIter
}

wrap_usize! {
    #[doc = "Clause cluster indices."]
    CtrIdx
    #[doc = "Ranger over clusters."]
    range: CtrRange
    #[doc = "Set of clusters."]
    set: CtrSet
    #[doc = "Hash map from clusters to something."]
    hash map: CtrHMap
    #[doc = "Total map from clusters to something."]
    map: CtrMap with iter: CtrMapIter
}

wrap_usize! {
    #[doc = "Constraint index."]
    CstrIdx
    #[doc = "Range over constraint indices."]
    range: CstrRange
    #[doc = "Constraint set."]
    set: CstrSet
    #[doc = "Constraint total map."]
    map: CstrMap with iter: CstrMapIter
}

wrap_usize! {
    #[doc = "Learner index."]
    LrnIdx
    #[doc = "Map of learners"]
    hash map: LrnHMap
    #[doc = "Total map from learners to something."]
    map: LrnMap with iter: LrnMapIter
}
unsafe impl Send for LrnIdx {}

wrap_usize! {
    #[doc = "Teacher Assistant index."]
    TAsIdx
    #[doc = "Map of TAs."]
    hash map: TAsHMap
    #[doc = "Total map from TAs to something."]
    map: TAsMap with iter: TAsMapIter
}
unsafe impl Send for TAsIdx {}

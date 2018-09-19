//! Types to store information about predicates and clause/function variables.

use rsmt2::print::{Sort2Smt, Sym2Smt};

use common::*;

/// Variable info for clauses or function definitions.
#[derive(Clone, Debug)]
pub struct VarInfo {
    /// Variable's name.
    pub name: String,
    /// Variable's type.
    pub typ: Typ,
    /// Variable's index.
    pub idx: VarIdx,
    /// Is the variable active?
    pub active: bool,
}
impl VarInfo {
    /// Constructor.
    pub fn new(name: String, typ: Typ, idx: VarIdx) -> Self {
        VarInfo {
            name,
            typ,
            idx,
            active: true,
        }
    }
    /// Name of the variable as bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.name.as_bytes()
    }
}
impl Sym2Smt<()> for VarInfo {
    fn sym_to_smt2<Writer>(&self, w: &mut Writer, _: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        write!(w, "v{}", self.idx)?;
        Ok(())
    }
}
impl Sort2Smt for VarInfo {
    fn sort_to_smt2<Writer>(&self, w: &mut Writer) -> SmtRes<()>
    where
        Writer: Write,
    {
        self.typ.get().sort_to_smt2(w)
    }
}
impl_fmt!{
  VarInfo(self, fmt) {
    fmt.write_str(& self.name)
  }
}

/// Stores information about a predicate.
#[derive(Debug, Clone)]
pub struct Pred {
    /// Name of the predicate. Should never be changed.
    pub name: String,
    /// Index of the predicate. Should never be changed.
    pub idx: PrdIdx,
    /// Current signature of the predicate.
    pub sig: VarMap<Typ>,
    /// Original signature of a predicate, as it was declared. This is important when preprocessing
    /// discovers that some arguments are irrelevant and removes them. This goes hand in hand with
    /// the following `original_sig_map`.
    original_sig: Sig,
    /// Map from variables of the **current** signature to the original one. Used when
    /// reconstructing a model.
    ///
    /// We should always have `self.original_sig.len() == self.original_sig_map.len()`.
    original_sig_map: VarMap<VarIdx>,
    /// Definition, if any. Set by preprocessing.
    pub tterm: Option<TTerms>,
    /// Strengthener, if any. Currently, this comes from strict negative clauses. It means the
    /// predicate has to be false when this term is false. So, given a candidate `cand` for this
    /// predicate, the candidate should be strengthened to `cand /\ strength`.
    pub strength: Option<Term>,
    /// Companion functions. Function that were created specifically for this predicate, and must
    /// be given to the user before giving the definition for this predicate.
    pub funs: Vec<Fun>,
}

impl Pred {
    /// Constructor.
    pub fn new(name: String, idx: PrdIdx, sig: VarMap<Typ>) -> Self {
        let original_sig = sig.clone();
        let original_sig_map: VarMap<_> = VarRange::zero_to(sig.len()).collect::<Vec<_>>().into();
        Pred {
            name,
            idx,
            sig,
            original_sig,
            original_sig_map,
            tterm: None,
            strength: None,
            funs: vec![],
        }
    }

    /// The original signature of the predicate, as it was declared.
    pub fn original_sig(&self) -> &Sig {
        &self.original_sig
    }
    /// Map from variables of the **current** signature to the original one.
    pub fn original_sig_map(&self) -> &VarMap<VarIdx> {
        &self.original_sig_map
    }

    /// A variable that does not appear in the **original** signature of the predicate.
    pub fn fresh_var_idx(&self) -> VarIdx {
        self.original_sig.next_index()
    }

    /// Registers a new signature for the predicate.
    ///
    /// The `map` maps variables of the **new** signature to the original one from
    /// `self.original_sig()`.
    ///
    /// In `debug`, checks that `map` is type-safe: forall `i`, `new_sig[i] ==
    /// self.original_sig[map[i]]`. Also checks that `new_sig` and `map` have the same length.
    pub fn set_sig(&mut self, new_sig: Sig, map: VarMap<VarIdx>) {
        self.sig = new_sig;
        self.original_sig_map = map;
        self.check().unwrap_or_else(|e| {
            print_err(&e);
            panic!(
                "illegal signature / map pair update for predicate {}",
                self.name,
            )
        })
    }

    /// Checks its invariant hold. Inactive in release.
    #[cfg(debug_assertions)]
    pub fn check(&self) -> Res<()> {
        if self.sig.len() != self.original_sig_map.len() {
            bail!(
                "signature and map to original signature differ in length for {}",
                self
            )
        }
        if !self
            .original_sig_map
            .index_iter()
            .all(|(src, tgt)| self.sig[src] == self.original_sig[*tgt])
        {
            bail!(
                "signature and map to original signature do not type check for {}",
                self
            )
        }
        Ok(())
    }
    /// Checks its invariant hold. Inactive in release.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub fn check(&self) -> Res<()> {
        Ok(())
    }
}

use std::fmt;
impl fmt::Display for Pred {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", self.name)
    }
}

//! Types to store information about predicates and clause/function variables.

use std::fmt;

use rsmt2::print::{Sort2Smt, Sym2Smt};

use crate::common::*;

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
    pub fn new<S>(name: S, typ: Typ, idx: VarIdx) -> Self
    where
        S: Into<String>,
    {
        let name = name.into();
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
mylib::impl_fmt! {
    VarInfo(self, fmt) {
        fmt.write_str(& self.name)
    }
}

/// Stores information about a predicate.
///
/// In particular, and perhaps most importantly, stores the link between the current signature and
/// the original signature of a predicate, so that going from one to the other is possible (easy).
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
    /// Same as `original_sig_map` but maps to the term corresponding to the old variable index.
    ///
    /// Populated by finalize.
    original_sig_term_map: Option<VarMap<Term>>,
    /// Definition, if any. Set by preprocessing.
    def: Option<TTerms>,
    /// Strengthener, if any. Currently, this comes from strict negative clauses. It means the
    /// predicate has to be false when this term is false. So, given a candidate `cand` for this
    /// predicate, the candidate should be strengthened to `cand /\ strength`.
    strength: Option<Term>,
    /// Companion functions. Function that were created specifically for this predicate, and must
    /// be given to the user before giving the definition for this predicate.
    funs: Vec<Fun>,
}

impl Pred {
    /// Constructor.
    pub fn new<S: Into<String>>(name: S, idx: PrdIdx, sig: VarMap<Typ>) -> Self {
        let name = name.into();
        let original_sig = sig.clone();
        let original_sig_map: VarMap<_> = VarRange::zero_to(sig.len()).collect::<Vec<_>>().into();
        Pred {
            name,
            idx,
            sig,
            original_sig,
            original_sig_map,
            original_sig_term_map: None,
            def: None,
            strength: None,
            funs: vec![],
        }
    }

    /// The current signature of the predicate.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert_eq! { & sig, pred.sig() }
    /// ```
    pub fn sig(&self) -> &Sig {
        &self.sig
    }

    /// The original signature of the predicate, as it was declared.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert_eq! { & sig, pred.original_sig() }
    /// ```
    pub fn original_sig(&self) -> &Sig {
        &self.original_sig
    }

    /// Map from variables of the **current** signature to the original one.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let pred = Pred::new("pred", 0.into(), sig.clone());
    /// let map: VarMap<VarIdx> = pred.sig().index_iter().map(|(idx, _)| idx).collect();
    /// assert_eq! { & map, pred.original_sig_map() }
    /// ```
    pub fn original_sig_map(&self) -> &VarMap<VarIdx> {
        &self.original_sig_map
    }

    /// Maps variables of the current signature to the term for the variables of the original
    /// signature.
    ///
    /// This function is only legal to call after [`finalize`] has been called.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// pred.finalize().unwrap();
    /// let map: VarMap<_> = pred.sig().index_iter().map(
    ///     |(idx, typ)| term::var(idx, typ.clone())
    /// ).collect();
    /// assert_eq! { & map, pred.original_sig_term_map().unwrap() }
    /// ```
    ///
    /// [`finalize`]: struct.Pred.html#method.finalize (finalize function)
    pub fn original_sig_term_map(&self) -> Res<&VarMap<Term>> {
        if let Some(map) = &self.original_sig_term_map {
            Ok(map)
        } else {
            bail!(
                "illegal call to {} before finalization on {}",
                conf.bad(&"original_sig_term_map"),
                conf.sad(&self.name)
            )
        }
    }

    /// Definition for this predicate, if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert! { pred.def().is_none() }
    /// let def = TTerms::True;
    /// pred.set_def(def.clone()).unwrap();
    /// assert_eq! { Some(& def), pred.def() }
    /// ```
    pub fn def(&self) -> Option<&TTerms> {
        self.def.as_ref()
    }

    /// True if the predicate has a definition.
    ///
    /// Equivalent to `self.def().is_some()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert! { !pred.is_defined() }
    /// let def = TTerms::True;
    /// pred.set_def(def.clone()).unwrap();
    /// assert! { pred.is_defined() }
    /// ```
    pub fn is_defined(&self) -> bool {
        self.def().is_some()
    }

    /// Strengthener for this predicate.
    ///
    /// Used by the teacher to force a predicate to be at least as false as it needs to.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert! { pred.strength().is_none() }
    /// let str = term::bool_var(1);
    /// pred.set_strength(str.clone()).unwrap();
    /// assert_eq! { Some(&str), pred.strength() }
    /// ```
    pub fn strength(&self) -> Option<&Term> {
        self.strength.as_ref()
    }

    /// Companion functions.
    ///
    /// Function that were created specifically for this predicate, and must be given to the user
    /// before giving the definition for this predicate.
    pub fn funs(&self) -> &[Fun] {
        &self.funs
    }

    /// A variable that does not appear in the **original** signature of the predicate.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let pred = Pred::new("pred", 0.into(), sig.clone());
    /// let fresh = pred.fresh_var_idx();
    /// debug_assert_ne! { fresh.get(), 0 }
    /// debug_assert_ne! { fresh.get(), 1 }
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// // New signature drops the first argument of the original signature.
    /// let nu_sig: VarMap<_> = vec![ typ::bool() ].into();
    /// // First variable of the new signature maps to the second (index 1) variable of the
    /// // original signature.
    /// let map: VarMap<VarIdx> = vec![ 1.into() ].into();
    /// pred.set_sig(nu_sig, map);
    /// ```
    ///
    /// Ill-typed.
    ///
    /// ```rust, should_panic
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// // New signature drops the first argument of the original signature.
    /// let nu_sig: VarMap<_> = vec![ typ::bool() ].into();
    /// // First variable of the new signature maps to the first (index 0) variable of the
    /// // original signature.
    /// let map: VarMap<VarIdx> = vec![ 0.into() ].into();
    /// // Panic: ill-typed
    /// pred.set_sig(nu_sig, map);
    /// ```
    ///
    /// Arity mismatch (map is too long).
    ///
    /// ```rust, should_panic
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// // New signature drops the first argument of the original signature.
    /// let nu_sig: VarMap<_> = vec![ typ::bool() ].into();
    /// // Map to original signature is too long compared to new signature.
    /// let map: VarMap<VarIdx> = vec![ 0.into(), 1.into() ].into();
    /// // Panic: arity mismatch
    /// pred.set_sig(nu_sig, map);
    /// ```
    ///
    /// Arity mismatch (map is too short).
    ///
    /// ```rust, should_panic
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// let nu_sig: VarMap<_> = vec![ typ::bool() ].into();
    /// // Map to original signature is too short compared to new signature.
    /// let map: VarMap<VarIdx> = vec![].into();
    /// // Panic: arity mismatch
    /// pred.set_sig(nu_sig, map);
    /// ```
    ///
    /// Arity mismatch (new signature is longer).
    ///
    /// ```rust, should_panic
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// let nu_sig: VarMap<_> = vec![ typ::int(), typ::bool(), typ::int() ].into();
    /// let map: VarMap<VarIdx> = vec![ 0.into(), 1.into(), 0.into() ].into();
    /// // Panic: new signature is too long
    /// pred.set_sig(nu_sig, map);
    /// ```
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

    /// Sets the predicate's definition.
    ///
    /// Only legal if the predicate has no definition.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// let def = TTerms::True;
    /// pred.set_def(def.clone()).unwrap();
    /// assert! { pred.is_defined() }
    /// assert! { pred.set_def(def).is_err() }
    /// ```
    pub fn set_def(&mut self, def: TTerms) -> Res<()> {
        let prev = ::std::mem::replace(&mut self.def, Some(def));
        if prev.is_some() {
            bail!(
                "trying to set the definition for {} twice",
                conf.bad(&self.name)
            )
        } else {
            Ok(())
        }
    }

    /// Removes the predicate's definition.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert_eq! { pred.unset_def(), None }
    /// let def = TTerms::True;
    /// pred.set_def(def.clone()).unwrap();
    /// assert_eq! { pred.unset_def(), Some(def) }
    /// ```
    pub fn unset_def(&mut self) -> Option<TTerms> {
        ::std::mem::replace(&mut self.def, None)
    }

    /// Sets the strengthener for this predicate.
    ///
    /// Only legal if the predicate has not strengthener.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert! { pred.strength().is_none() }
    /// let str = term::bool_var(1);
    /// pred.set_strength(str.clone()).unwrap();
    /// assert_eq! { Some(&str), pred.strength() }
    /// ```
    pub fn set_strength(&mut self, strength: Term) -> Res<()> {
        let prev = ::std::mem::replace(&mut self.strength, Some(strength));
        if prev.is_some() {
            bail!(
                "trying to set the strengthener for {} twice",
                conf.bad(&self.name)
            )
        } else {
            Ok(())
        }
    }

    /// Removes the predicate's strengthener.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert! { pred.unset_strength().is_none() }
    /// let str = term::bool_var(1);
    /// pred.set_strength(str.clone()).unwrap();
    /// assert_eq! { Some(str), pred.unset_strength() }
    /// ```
    pub fn unset_strength(&mut self) -> Option<Term> {
        ::std::mem::replace(&mut self.strength, None)
    }

    /// Adds a companion function.
    pub fn add_fun(&mut self, fun: Fun) {
        self.funs.push(fun)
    }

    /// Finalizes the predicate information.
    ///
    /// After finalization, calls to [`original_sig_term_map`] will always succeed.
    ///
    /// Fails if this is the second time `finalize` is called.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ common::*, info::Pred };
    /// let sig: VarMap<_> = vec![ typ::int(), typ::bool() ].into();
    /// let mut pred = Pred::new("pred", 0.into(), sig.clone());
    /// assert! { pred.finalize().is_ok() }
    /// assert! { pred.finalize().is_err() }
    /// ```
    ///
    /// [`original_sig_term_map`]: struct.Pred.html#method.original_sig_term_map
    /// (original_sig_term_map function)
    pub fn finalize(&mut self) -> Res<()> {
        if self.original_sig_term_map.is_some() {
            bail!(
                "cannot finalize information for {} more than once",
                conf.bad(&self.name)
            )
        }

        let sig_term_map: VarMap<_> = self
            .original_sig_map
            .iter()
            .map(|old_var| term::var(*old_var, self.original_sig[*old_var].clone()))
            .collect();
        self.original_sig_term_map = Some(sig_term_map);

        Ok(())
    }

    /// Checks its invariant hold. Inactive in release.
    ///
    /// Generally speaking, the invariants checked by this function should be respected by
    /// construction. In fact, this function runs after most non-trivial changes to values of this
    /// type.
    #[cfg(debug_assertions)]
    pub fn check(&self) -> Res<()> {
        if self.sig.len() > self.original_sig.len() {
            bail!(
                "current signature is longer than original signature for {}",
                conf.bad(&self.name)
            )
        }
        if self.sig.len() != self.original_sig_map.len() {
            bail!(
                "signature and sig map to original signature differ in length for {}",
                conf.bad(&self.name)
            )
        }
        for (src, tgt) in self.original_sig_map.index_iter() {
            if self.sig[src] != self.original_sig[*tgt] {
                bail!(
                    "signature and sig map to original signature do not type check on \
                     {} -> {} for {}",
                    src.default_str(),
                    tgt.default_str(),
                    conf.bad(&self.name)
                )
            }
        }

        if let Some(map) = &self.original_sig_term_map {
            if self.sig.len() != map.len() {
                bail!(
                    "signature and term map to original signature differ in length for {}",
                    conf.bad(&self.name)
                )
            }

            for (src, tgt) in map.index_iter() {
                if let Some(tgt) = tgt.var_idx() {
                    if self.sig[src] != self.original_sig[tgt] {
                        bail!(
                            "signature and term map to original signature do not type check on \
                             {} -> {} for {}",
                            src.default_str(),
                            tgt.default_str(),
                            conf.bad(&self.name)
                        )
                    }
                } else {
                    bail!(
                        "illegal term for {}: maps {} to non-variable term {}",
                        conf.bad(&self.name),
                        src.default_str(),
                        tgt
                    )
                }
            }
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

impl fmt::Display for Pred {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", self.name)
    }
}

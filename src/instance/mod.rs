//! Actual instance structure.

use crate::{common::*, data::Data, info::*, var_to::terms::VarTermsSet};

mod clause;
mod pre_instance;

pub use self::clause::Clause;
pub use self::pre_instance::PreInstance;

/// Stores the instance: the clauses, the factory and so on.
///
/// Clause indices can vary during instance building, because of the
/// simplifications that can remove clauses.
///
/// So, `pred_to_clauses` has to be carefully maintained, the easiest way to do this is to never
/// access the fields of an instance directly from the outside. This is why all of them are
/// private.
///
/// Instance mutation should only happen at two points: [parsing] (creation) and [preprocessing].
/// (A minor exception is model reconstruction.)
///
/// # Finalization
///
/// Instance finalization is crucial. A lot of instance functions do not make sense unless the
/// instance is finalized. This is currently done at the end of preprocessing with the [`finalize`]
/// function.
///
/// Functions that do not make sense before finalization include:
///
/// - [`pos_clauses`]
/// - [`strict_neg_clauses`]
/// - [`neg_clauses`]
/// - [`non_strict_neg_clauses`]
/// - [`imp_clauses`]
/// - [`model_of`]
/// - [`extend_model`]
/// - [`sorted_forced_terms`]
/// - [`simplify_pred_defs`]
///
/// [parsing]: ../parse/index.html (parse module)
/// [preprocessing]: ../preproc/index.html (preproc module)
/// [`finalize`]: struct.Instance.html#method.finalize
/// [`pos_clauses`]: struct.Instance.html#method.strict_neg_clauses
/// (Instance's pos_clauses function)
/// [`strict_neg_clauses`]: struct.Instance.html#method.strict_neg_clauses
/// (strict_neg_clauses function)
/// [`neg_clauses`]: struct.Instance.html#method.neg_clauses
/// (neg_clauses function)
/// [`non_strict_neg_clauses`]: struct.Instance.html#method.non_strict_neg_clauses
/// (non_strict_neg_clauses function)
/// [`imp_clauses`]: struct.Instance.html#method.imp_clauses
/// (imp_clauses function)
/// [`model_of`]: struct.Instance.html#method.model_of
/// (model_of function)
/// [`extend_model`]: struct.Instance.html#method.extend_model
/// (extend_model function)
/// [`sorted_forced_terms`]: struct.Instance.html#method.sorted_forced_terms
/// (sorted_forced_terms function)
/// [`simplify_pred_defs`]: struct.Instance.html#method.simplify_pred_defs
/// (simplify_pred_defs function)
#[derive(Clone)]
pub struct Instance {
    /// Predicates.
    preds: Preds,

    /// Predicates defined in `pred_terms`, sorted by predicate dependencies.
    ///
    /// Populated by the `finalize` function.
    sorted_pred_terms: Vec<PrdIdx>,

    /// Side-clauses.
    ///
    /// A side clause
    /// - does not mention any predicate
    /// - mentions a user-defined function
    ///
    /// It will be asserted when the instance is asked to initialize a solver. A
    /// side-clause is viewed as additional information provided by the user, a
    /// kind of lemma for the actual clauses.
    side_clauses: Vec<Clause>,

    /// Clauses.
    clauses: ClsMap<Clause>,
    /// Maps predicates to the clauses where they appear in the lhs and rhs
    /// respectively.
    pred_to_clauses: PrdMap<(ClsSet, ClsSet)>,
    /// Unsat flag.
    is_unsat: bool,
    /// Set of positive clauses.
    ///
    /// Only available after finalize.
    pos_clauses: ClsSet,
    /// Set of strictly negative clauses.
    ///
    /// A clause is strictly negative if it has strictly one predicate
    /// application, and it's in the clause's body. Only available after
    /// finalize.
    strict_neg_clauses: ClsSet,
    /// Set of non-strictly negative clauses.
    ///
    /// A clause is strictly negative if it has strictly one predicate
    /// application, and it's in the clause's body. Only available after
    /// finalize.
    non_strict_neg_clauses: ClsSet,
    /// Set of (non-strictly) negative clauses.
    ///
    /// Super set of strictly negative clauses. Only available after finalize.
    neg_clauses: ClsSet,
    /// Set of implication clauses.
    ///
    /// Only available after finalize.
    imp_clauses: ClsSet,
    /// True if finalized already ran.
    is_finalized: bool,
    /// If this instance is the result of a split, contains the index of the
    /// clause of the original instance that the split was on.
    ///
    /// The constructor sets this to `None`. Function `clone_with_clauses`
    /// automatically sets it to the clause kept.
    split: Option<ClsIdx>,

    /// Define-funs parsed.
    define_funs: BTreeMap<String, (VarInfos, crate::parse::PTTerms)>,

    /// Maps **original** clause indexes to their optional name.
    old_names: ClsHMap<String>,

    /// Print success.
    ///
    /// Can only be set by `(set-option :print-success true)`.
    print_success: bool,
    /// Unsat core production.
    ///
    /// Can only be set by `(set-option :produce-unsat-cores true)`.
    unsat_cores: bool,
    /// Unsat core production.
    ///
    /// Can only be set by `(set-option :produce-proofs true)`.
    proofs: bool,
}

impl Default for Instance {
    fn default() -> Self {
        Self::new()
    }
}

impl Instance {
    /// Instance constructor.
    pub fn new() -> Instance {
        let pred_capa = conf.instance.pred_capa;
        let clause_capa = conf.instance.clause_capa;
        Instance {
            preds: Preds::with_capacity(pred_capa),

            sorted_pred_terms: Vec::with_capacity(pred_capa),

            side_clauses: Vec::with_capacity(7),
            clauses: ClsMap::with_capacity(clause_capa),
            // clusters: CtrMap::with_capacity( clause_capa / 3 ),
            pred_to_clauses: PrdMap::with_capacity(pred_capa),
            is_unsat: false,
            pos_clauses: ClsSet::new(),
            strict_neg_clauses: ClsSet::new(),
            non_strict_neg_clauses: ClsSet::new(),
            neg_clauses: ClsSet::new(),
            imp_clauses: ClsSet::new(),
            is_finalized: false,
            split: None,
            define_funs: BTreeMap::new(),
            old_names: ClsHMap::with_capacity(clause_capa),
            print_success: false,
            unsat_cores: false,
            proofs: false,
        }
    }

    /// Clones itself.
    ///
    /// This is only used when splitting. `clause` will be remembered as the
    /// clause the split is on.
    ///
    /// Fails (in debug) if `clause` is not a negative clause of `self` or if
    /// `self` is not finalized.
    pub fn clone_with_clauses(&self, clause: ClsIdx) -> Self {
        debug_assert! { self.neg_clauses.contains(& clause) }
        debug_assert! { self.is_finalized }

        Instance {
            preds: self.preds.clone(),

            sorted_pred_terms: Vec::with_capacity(self.preds.len()),

            side_clauses: self.side_clauses.clone(),
            clauses: self.clauses.clone(),
            pred_to_clauses: self.pred_to_clauses.clone(),
            is_unsat: false,
            pos_clauses: ClsSet::new(),
            strict_neg_clauses: ClsSet::new(),
            non_strict_neg_clauses: ClsSet::new(),
            neg_clauses: ClsSet::new(),
            imp_clauses: ClsSet::new(),
            is_finalized: false,
            split: Some(clause),
            define_funs: self.define_funs.clone(),
            old_names: self.old_names.clone(),
            print_success: false,
            unsat_cores: false,
            proofs: false,
        }
    }

    /// Set of positive clauses.
    ///
    /// Only available after finalize.
    pub fn pos_clauses(&self) -> &ClsSet {
        &self.pos_clauses
    }
    /// Set of negative clauses with exactly one predicate application.
    ///
    /// Only available after finalize.
    pub fn strict_neg_clauses(&self) -> &ClsSet {
        &self.strict_neg_clauses
    }
    /// Set of negative clauses.
    ///
    /// Only available after finalize.
    pub fn neg_clauses(&self) -> &ClsSet {
        &self.neg_clauses
    }
    /// Set of non-strict negative clauses.
    ///
    /// Only available after finalize.
    pub fn non_strict_neg_clauses(&self) -> &ClsSet {
        &self.non_strict_neg_clauses
    }
    /// Set of implication clauses ad negative clausesh.
    ///
    /// Only available after finalize.
    pub fn imp_clauses(&self) -> &ClsSet {
        &self.imp_clauses
    }

    /// Number of active (not forced) predicates.
    pub fn active_pred_count(&self) -> usize {
        let mut count = 0;
        for pred in self.pred_indices() {
            if !self[pred].is_defined() {
                count += 1
            }
        }
        count
    }

    /// Returns true if the instance is already solved.
    pub fn is_solved(&self) -> bool {
        if self.is_unsat {
            return true;
        }
        for pred in &self.preds {
            if pred.def().is_none() {
                return false;
            }
        }
        true
    }

    /// Map from the original signature of a predicate.
    pub fn map_from_original_sig_of(&self, pred: PrdIdx) -> VarHMap<Term> {
        let mut res = VarHMap::with_capacity(self[pred].original_sig().len());

        for (tgt, src) in self[pred].original_sig_map().index_iter() {
            res.insert(
                *src,
                term::var(tgt, self[pred].original_sig()[*src].clone()),
            );
        }

        res
    }

    /// If this instance is the result of a split, returns the index of the
    /// clause of the original instance that the split was on.
    ///
    /// Used mainly to create different folders for log files when splitting.
    pub fn split(&self) -> Option<ClsIdx> {
        self.split
    }

    /// True if the unsat flag is set.
    pub fn is_unsat(&self) -> bool {
        self.is_unsat
    }

    /// Sets the unsat flag in the instance.
    pub fn set_unsat(&mut self) {
        self.is_unsat = true
    }

    /// Adds a define fun.
    pub fn add_define_fun<S: Into<String>>(
        &mut self,
        name: S,
        sig: VarInfos,
        body: crate::parse::PTTerms,
    ) -> Option<(VarInfos, crate::parse::PTTerms)> {
        self.define_funs.insert(name.into(), (sig, body))
    }
    /// Retrieves a define fun.
    pub fn get_define_fun(&self, name: &str) -> Option<&(VarInfos, crate::parse::PTTerms)> {
        self.define_funs.get(name)
    }

    /// Returns the model corresponding to the input predicates and the forced
    /// predicates.
    ///
    /// The model is sorted in topological order.
    pub fn model_of(&self, candidates: Candidates) -> Res<Model> {
        let mut model = Model::with_capacity(self.preds.len());
        for (pred, tterms_opt) in candidates.into_index_iter() {
            if let Some(term) = tterms_opt {
                let (term, _) = term.subst(self[pred].original_sig_term_map()?);
                model.push((pred, TTerms::of_term(None, term)))
            }
        }

        for pred in &self.sorted_pred_terms {
            let pred = *pred;
            if let Some(tterms) = self[pred].def() {
                model.push((pred, tterms.subst(self[pred].original_sig_term_map()?)))
            } else {
                bail!("inconsistency in sorted forced predicates")
            }
        }

        Ok(model)
    }

    /// Returns the model corresponding to the input predicates and the forced
    /// predicates.
    ///
    /// The model is sorted in topological order.
    pub fn extend_model(&self, candidates: ConjCandidates) -> Res<ConjModel> {
        let mut model = ConjModel::with_capacity(self.preds.len());
        let mut known_preds = PrdSet::new();
        let mut tmp: Vec<_> = candidates
            .into_iter()
            .map(|(pred, conj)| {
                let mut preds = PrdSet::new();
                for tterms in &conj {
                    preds.extend(tterms.preds())
                }
                (pred, preds, conj)
            })
            .collect();
        let mut cnt;
        let mut changed;
        while !tmp.is_empty() {
            cnt = 0;
            changed = false;
            while cnt < tmp.len() {
                if tmp[cnt].1.iter().all(|pred| known_preds.contains(pred)) {
                    changed = true;
                    let (pred, _, dnf) = tmp.swap_remove(cnt);
                    let is_new = known_preds.insert(pred);
                    debug_assert! { is_new }
                    model.push(vec![(pred, dnf)])
                } else {
                    cnt += 1
                }
            }
            if !changed {
                break;
            }
        }
        if !tmp.is_empty() {
            model.push(tmp.into_iter().map(|(pred, _, dnf)| (pred, dnf)).collect())
        }

        for pred in &self.sorted_pred_terms {
            let pred = *pred;
            if let Some(tterms) = self[pred].def() {
                let tterms = tterms.subst(self[pred].original_sig_term_map()?);
                model.push(vec![(pred, vec![tterms])])
            } else {
                bail!("inconsistency in sorted forced predicates")
            }
        }
        Ok(model)
    }

    /// True if the instance is sat, false if unsat.
    fn is_trivial(&self) -> Option<bool> {
        if self.is_unsat {
            Some(false)
        } else if self.preds.iter().all(|pred| pred.is_defined()) {
            Some(true)
        } else {
            None
        }
    }

    /// Returns a model for the instance when all the predicates have terms
    /// assigned to them.
    pub fn is_trivial_conj(&self) -> Res<Option<MaybeModel<ConjModel>>> {
        match self.is_trivial() {
            None => Ok(None),
            Some(false) => Ok(Some(MaybeModel::Unsat)),
            Some(true) => self
                .extend_model(PrdHMap::new())
                .map(|res| Some(MaybeModel::Model(res))),
        }
    }

    /// Returns a model for the instance when all the predicates have terms
    /// assigned to them.
    pub fn is_trivial_model(&self) -> Res<Option<MaybeModel<Model>>> {
        match self.is_trivial() {
            None => Ok(None),
            Some(false) => Ok(Some(MaybeModel::Unsat)),
            Some(true) => self
                .model_of(PrdMap::new())
                .map(|res| Some(MaybeModel::Model(res))),
        }
    }

    /// Lhs and rhs predicates of a clause.
    #[inline]
    pub fn preds_of_clause(&self, clause: ClsIdx) -> (&PredApps, Option<PrdIdx>) {
        (
            self[clause].lhs_preds(),
            self[clause].rhs().map(|(prd, _)| prd),
        )
    }

    /// Prints some top terms as a model.
    ///
    /// Meaning variables are printed with default printing: `<var_idx>` is printed as
    /// `v_<var_idx>`.
    pub fn print_tterms_as_model<W: Write>(&self, w: &mut W, tterms: &TTerms) -> IoRes<()> {
        tterms.write(
            w,
            |w, var| var.default_write(w),
            |w, pred, args| {
                let pred = &self[pred];
                write!(w, "({}", pred)?;
                let mut prev: VarIdx = 0.into();
                for (var, arg) in args.index_iter() {
                    let old_var = pred.original_sig_map()[var];
                    for var in VarRange::new(prev, old_var) {
                        write!(w, " {}", pred.original_sig()[var].default_val())?
                    }
                    prev = old_var;
                    prev.inc();
                    write!(w, " {}", arg)?
                }
                for var in VarRange::new(prev, pred.original_sig().next_index()) {
                    write!(w, " {}", pred.original_sig()[var].default_val())?
                }
                write!(w, ")")
            },
        )
    }

    /// Finalizes instance creation.
    ///
    /// - shrinks all collections
    /// - sorts forced predicates by dependencies
    ///
    /// # TO DO
    ///
    /// - optimize sorting of forced preds by dependencies (low priority)
    pub fn finalize(&mut self) -> Res<()> {
        if self.is_finalized {
            return Ok(());
        }
        self.is_finalized = true;

        self.sorted_pred_terms.clear();
        self.preds.shrink_to_fit();
        self.clauses.shrink_to_fit();

        let mut tmp: Vec<(PrdIdx, PrdSet)> = Vec::with_capacity(self.preds.len());

        for (idx, clause) in self.clauses.index_iter_mut() {
            if clause.rhs().is_none() {
                if clause.lhs_pred_apps_len() == 1 {
                    let is_new = self.strict_neg_clauses.insert(idx);
                    debug_assert! { is_new }
                } else {
                    let is_new = self.non_strict_neg_clauses.insert(idx);
                    debug_assert! { is_new }
                }
                let is_new = self.neg_clauses.insert(idx);
                debug_assert! { is_new }
            } else if clause.lhs_preds().is_empty() {
                if !(self.is_unsat || clause.rhs().is_some()) {
                    bail!(
                        "{}\nfound a clause with no predicate during finalization",
                        clause.to_string_info(&self.preds).unwrap()
                    )
                }
                let is_new = self.pos_clauses.insert(idx);
                debug_assert! { is_new }
            } else {
                let is_new = self.imp_clauses.insert(idx);
                debug_assert! { is_new }
            }
        }

        // Populate `tmp`.
        let mut known_preds = PrdSet::with_capacity(self.preds.len());

        for pred in self.pred_indices() {
            if let Some(tterms) = self[pred].def() {
                tmp.push((pred, tterms.preds()))
            } else {
                known_preds.insert(pred);
            }
        }
        // Sort by dependencies.
        while !tmp.is_empty() {
            let mut cnt = 0; // Will use swap remove.
            'find_preds: while cnt < tmp.len() {
                for pred in &tmp[cnt].1 {
                    if !known_preds.contains(pred) {
                        // Don't know this predicate, keep going in `tmp`.
                        cnt += 1;
                        continue 'find_preds;
                    }
                }
                // Reachable only we already have all of the current pred's
                // dependencies.
                let (pred, _) = tmp.swap_remove(cnt);
                self.sorted_pred_terms.push(pred);
                known_preds.insert(pred);
                () // No `cnt` increment after swap remove.
            }
        }

        for pred in &mut self.preds {
            pred.finalize()?
        }

        self.sorted_pred_terms.shrink_to_fit();

        Ok(())
    }

    /// If the input predicate is forced to a constant boolean, returns its
    /// value.
    pub fn bool_value_of(&self, pred: PrdIdx) -> Option<bool> {
        self[pred].def().and_then(|terms| terms.bool())
    }

    /// Forced predicates in topological order.
    #[inline]
    pub fn sorted_forced_terms(&self) -> &Vec<PrdIdx> {
        &self.sorted_pred_terms
    }

    /// Returns the clauses in which the predicate appears in the lhs and rhs
    /// respectively.
    #[inline]
    pub fn clauses_of(&self, pred: PrdIdx) -> (&ClsSet, &ClsSet) {
        (&self.pred_to_clauses[pred].0, &self.pred_to_clauses[pred].1)
    }
    /// Returns the clauses in which `pred` appears in the lhs.
    #[inline]
    pub fn lhs_clauses_of(&self, pred: PrdIdx) -> &ClsSet {
        &self.pred_to_clauses[pred].0
    }
    /// Returns the clauses in which `pred` appears in the rhs.
    #[inline]
    pub fn rhs_clauses_of(&self, pred: PrdIdx) -> &ClsSet {
        &self.pred_to_clauses[pred].1
    }

    /// Adds a predicate application to a clause's lhs.
    pub fn clause_add_lhs_pred(&mut self, clause: ClsIdx, pred: PrdIdx, args: VarMap<Term>) {
        self.pred_to_clauses[pred].0.insert(clause);
        self.clauses[clause].insert_pred_app(pred, args.into());
    }

    /// Adds a term to a clause's lhs.
    pub fn clause_add_lhs_term(&mut self, clause: ClsIdx, term: Term) {
        self.clauses[clause].insert_term(term);
    }

    /// Forces the rhs of a clause to a predicate application.
    pub fn clause_force_rhs(
        &mut self,
        clause: ClsIdx,
        pred: PrdIdx,
        args: VarMap<Term>,
    ) -> Res<()> {
        self.pred_to_clauses[pred].1.insert(clause);
        self.clauses[clause].set_rhs(pred, args.into())
    }

    /// Adds some terms to the lhs of a clause.
    ///
    /// Updates `pred_to_clauses`.
    pub fn clause_lhs_extend<I: IntoIterator<Item = TTerm>>(
        &mut self,
        clause_idx: ClsIdx,
        tterms: I,
    ) {
        let clause = &mut self.clauses[clause_idx];
        for tterm in tterms {
            match tterm {
                TTerm::P { pred, args } => {
                    self.pred_to_clauses[pred].0.insert(clause_idx);
                    clause.insert_pred_app(pred, args);
                }
                TTerm::T(term) => {
                    clause.insert_term(term);
                }
            }
        }
    }

    /// Replaces the rhs of a clause.
    ///
    /// Updates `pred_to_clauses` for the term it inserts but **not** the one it
    /// removes.
    pub fn clause_rhs_force(&mut self, clause_idx: ClsIdx, tterm: TTerm) -> Res<()> {
        let clause = &mut self.clauses[clause_idx];
        match tterm {
            TTerm::P { pred, args } => {
                clause.set_rhs(pred, args)?;
                let is_new = self.pred_to_clauses[pred].1.insert(clause_idx);
                debug_assert!(is_new)
            }
            TTerm::T(term) => {
                if term.bool() != Some(false) {
                    clause.insert_term(term::not(term));
                }
                clause.unset_rhs();
            }
        }
        Ok(())
    }

    /// Range over the predicate indices.
    pub fn pred_indices(&self) -> PrdRange {
        PrdRange::zero_to(self.preds.len())
    }
    /// Range over the clause indices.
    pub fn clause_indices(&self) -> ClsRange {
        ClsRange::zero_to(self.clauses.len())
    }

    /// Predicate accessor.
    pub fn preds(&self) -> &Preds {
        &self.preds
    }

    /// Clause accessor.
    pub fn clauses(&self) -> &ClsMap<Clause> {
        &self.clauses
    }

    /// Pushes a new predicate and returns its index.
    pub fn push_pred<S: Into<String>>(&mut self, name: S, sig: Sig) -> PrdIdx {
        let idx = self.preds.next_index();
        let name = name.into();

        self.preds.push(Pred::new(name, idx, sig));

        self.pred_to_clauses
            .push((ClsSet::with_capacity(17), ClsSet::with_capacity(17)));
        idx
    }

    /// Removes and returns the indices of the clauses `pred` appears in the lhs
    /// of from `self.pred_to_clauses`.
    fn unlink_pred_lhs<LHS>(&mut self, pred: PrdIdx, lhs: &mut LHS)
    where
        LHS: ::std::iter::Extend<ClsIdx>,
    {
        lhs.extend(self.pred_to_clauses[pred].0.drain())
    }

    /// Removes and returns the indices of the clauses `pred` appears in the rhs
    /// of from `self.pred_to_clauses`.
    fn unlink_pred_rhs<RHS>(&mut self, pred: PrdIdx, rhs: &mut RHS)
    where
        RHS: ::std::iter::Extend<ClsIdx>,
    {
        rhs.extend(self.pred_to_clauses[pred].1.drain())
    }

    /// Goes trough the predicates in `from`, and updates `pred_to_clauses` so
    /// that they point to `to` instead.
    fn relink_preds_to_clauses(&mut self, from: ClsIdx, to: ClsIdx) -> Res<()> {
        for pred in self.clauses[from].lhs_preds().keys() {
            let pred = *pred;
            let was_there = self.pred_to_clauses[pred].0.remove(&from);
            let _ = self.pred_to_clauses[pred].0.insert(to);
            debug_assert!(was_there)
        }
        if let Some((pred, _)) = self.clauses[from].rhs() {
            let was_there = self.pred_to_clauses[pred].1.remove(&from);
            let _ = self.pred_to_clauses[pred].1.insert(to);
            debug_assert!(was_there)
        }
        Ok(())
    }

    /// Forget some clauses.
    ///
    /// Duplicates are handled as if there was only one.
    pub fn forget_clauses(&mut self, clauses: &mut Vec<ClsIdx>) -> Res<()> {
        // Forgetting is done by swap remove, we sort in DESCENDING order so that
        // indices always make sense.
        clauses.sort_unstable_by(|c_1, c_2| c_2.cmp(c_1));
        let mut prev = None;
        for clause in clauses.drain(0..) {
            log! { @6 "forgetting {}", self[clause].to_string_info(&self.preds).unwrap() }
            if prev == Some(clause) {
                continue;
            }
            prev = Some(clause);
            let _ = self.forget_clause(clause)?;
        }
        Ok(())
    }

    /// Forget a clause. **Does not preserve the order of the clauses.**
    ///
    /// After calling this function, clause indices kept outside of the instance
    /// will in general refer to clauses different from the ones they pointed to
    /// before the call.
    ///
    /// Also unlinks predicates from `pred_to_clauses`.
    pub fn forget_clause(&mut self, clause: ClsIdx) -> Res<Clause> {
        for pred in self.clauses[clause].lhs_preds().keys() {
            let pred = *pred;
            let was_there = self.pred_to_clauses[pred].0.remove(&clause);
            debug_assert!(was_there || self[pred].is_defined())
        }
        if let Some((pred, _)) = self.clauses[clause].rhs() {
            self.pred_to_clauses[pred].1.remove(&clause);
        }
        // Relink the last clause as its index is going to be `clause`. Except if
        // `clause` is already the last one.
        let last_clause: ClsIdx = (self.clauses.len() - 1).into();
        if clause != last_clause {
            self.relink_preds_to_clauses(last_clause, clause)?
        }
        let res = self.clauses.swap_remove(clause);
        Ok(res)
    }

    /// First free clause index.
    pub fn next_clause_index(&self) -> ClsIdx {
        self.clauses.next_index()
    }

    /// Pushes a new clause.
    pub fn push_new_clause(
        &mut self,
        vars: VarInfos,
        lhs: Vec<TTerm>,
        rhs: Option<PredApp>,
        info: &'static str,
    ) -> Res<Option<ClsIdx>> {
        let idx = self.clauses.next_index();
        let clause = clause::new(vars, lhs, rhs, info, idx);
        self.push_clause(clause)
    }

    /// The name of an original clause if any.
    pub fn name_of_old_clause(&self, cls: ClsIdx) -> Option<&String> {
        self.old_names.get(&cls)
    }

    /// Sets the name for an original clause.
    pub fn set_old_clause_name(&mut self, cls: ClsIdx, name: String) -> Res<()> {
        let prev = self.old_names.insert(cls, name);
        if let Some(prev) = prev {
            bail!(format!(
                "trying to name clause #{}, but it's already called {}",
                cls,
                conf.bad(&prev)
            ))
        }
        Ok(())
    }

    /// Mutable accessor for side clauses.
    ///
    /// Does not expose function invariants.
    pub fn side_clauses_retain<Keep>(&mut self, mut keep: Keep) -> Res<RedInfo>
    where
        Keep: FnMut(&mut Clause) -> Res<bool>,
    {
        let mut info = RedInfo::new();
        let mut cnt = 0;
        while cnt < self.side_clauses.len() {
            if !keep(&mut self.side_clauses[cnt])? {
                info.clauses_rmed += 1;
                self.side_clauses.swap_remove(cnt);
                ()
            } else {
                cnt += 1
            }
        }
        Ok(info)
    }

    /// Asserts all the side-clauses in a solver.
    pub fn assert_side_clauses<P>(&self, solver: &mut Solver<P>) -> Res<()> {
        for side_clause in &self.side_clauses {
            let side_clause = smt::SmtSideClause::new(side_clause);
            solver.assert(&side_clause)?
        }
        Ok(())
    }

    /// Registers a clause as a side-clause.
    ///
    /// A side clause is a clause that does not mention any predicate, but
    /// mentions a user-defined function.
    pub fn add_side_clause(&mut self, clause: Clause) -> Res<()> {
        if clause.rhs().is_some() {
            bail!("cannot convert to side-clause: predicate application in rhs")
        }
        if !clause.lhs_preds().is_empty() {
            bail!("cannot convert to side-clause: predicate application(s) in lhs")
        }

        self.side_clauses.push(clause);

        Ok(())
    }

    /// Registers a new side clause: forces the term to be true.
    ///
    /// A side clause is a clause that does not mention any predicate, but
    /// mentions a user-defined function.
    pub fn add_new_side_clause(
        &mut self,
        vars: VarInfos,
        term: Term,
        info: &'static str,
    ) -> Res<()> {
        let clause = clause::new(
            vars,
            vec![TTerm::T(term::not(term))],
            None,
            info,
            self.side_clauses.len().into(),
        );

        self.add_side_clause(clause)
    }

    /// Pushes a clause.
    ///
    /// Returns its index, if it was added.
    pub fn push_clause(&mut self, clause: Clause) -> Res<Option<ClsIdx>> {
        for term in clause.lhs_terms() {
            if let Some(false) = term.bool() {
                return Ok(None);
            }
        }

        if clause.lhs_preds().is_empty()
            && clause.rhs().is_none()
            && clause
                .lhs_terms()
                .iter()
                .any(|term| term.has_fun_app_or_adt())
        {
            self.add_side_clause(clause)?;
            return Ok(None);
        }

        let idx = self.clauses.next_index();
        let is_new = self.push_clause_unchecked(clause);
        // self.check("after `push_clause`") ? ;
        Ok(if is_new { Some(idx) } else { None })
    }

    /// True if the clause is redundant.
    pub fn is_redundant(&self, idx: ClsIdx) -> bool {
        let clause = &self.clauses[idx];

        if let Some((pred, _)) = clause.rhs() {
            for i in &self.pred_to_clauses[pred].1 {
                if *i != idx && self[*i].same_as(&clause) {
                    return true;
                }
            }
        } else if let Some((pred, _)) = clause.lhs_preds().iter().next() {
            for i in &self.pred_to_clauses[*pred].0 {
                if *i != idx && self[*i].same_as(&clause) {
                    return true;
                }
            }
        } else {
            for (i, c) in self.clauses.index_iter() {
                if i != idx && c.same_as(&clause) {
                    return true;
                }
            }
        }
        false
    }

    /// Pushes a new clause, does not sanity-check but redundancy-checks.
    fn push_clause_unchecked(&mut self, clause: Clause) -> bool {
        let clause_index = self.clauses.next_index();
        self.clauses.push(clause);

        if self.is_redundant(clause_index) {
            self.clauses.pop();
            return false;
        }

        for pred in self.clauses[clause_index].lhs_preds().keys() {
            let pred = *pred;
            let is_new = self.pred_to_clauses[pred].0.insert(clause_index);
            debug_assert!(is_new)
        }
        if let Some((pred, _)) = self.clauses[clause_index].rhs() {
            let is_new = self.pred_to_clauses[pred].1.insert(clause_index);
            debug_assert!(is_new)
        }
        true
    }

    /// Checks that the instance has no inconsistencies.
    ///
    /// Only active in debug.
    #[cfg(not(debug_assertions))]
    #[inline(always)]
    pub fn check(&self, _: &'static str) -> Res<()> {
        Ok(())
    }

    #[cfg(debug_assertions)]
    pub fn check(&self, s: &'static str) -> Res<()> {
        for clause in &self.clauses {
            clause.check(s)?
        }
        self.check_pred_to_clauses()
            .chain_err(|| format!("while checking `{}`", conf.sad("pred_to_clauses")))
            .chain_err(|| format!("instance consistency check failed: {}", conf.emph(s)))?;
        self.check_preds_consistency()?;

        for (idx, clause) in self.clauses.index_iter() {
            for term in clause.lhs_terms() {
                if let Some(false) = term.bool() {
                    bail!(
                        "({}) found a trivial clause: #{} {}",
                        s,
                        idx,
                        clause.to_string_info(&self.preds).unwrap()
                    )
                }
            }

            for pred in clause
                .lhs_preds()
                .iter()
                .map(|(pred, _)| *pred)
                .chain(clause.rhs().into_iter().map(|(pred, _)| pred))
            {
                if let Some(tterms) = self[pred].def() {
                    bail! {
                      "predicate {} is forced{} but appears in a clause: {}",
                      conf.bad( & self[pred].name ),
                      match tterms.bool() {
                        Some(true) => " to true",
                        Some(false) => " to false",
                        None => "",
                      },
                      s
                    }
                }
            }
        }

        scoped! {
          let mut clauses = self.clauses.iter() ;
          while let Some(clause) = clauses.next() {
            for c in clauses.clone() {
              if clause.same_as(c) {
                bail!(
                  "{}\n\n{}\n\nsame clause appears multiple times\n{}",
                  clause.to_string_info(&self.preds).unwrap(),
                  c.to_string_info(&self.preds).unwrap(),
                  conf.bad(s)
                )
              }
            }
          }
        }

        Ok(())
    }

    /// Checks predicate information.
    #[cfg(debug_assertions)]
    fn check_preds_consistency(&self) -> Res<()> {
        for pred in &self.preds {
            pred.check()?
        }
        Ok(())
    }

    /// Pretty printer for a set of clauses.
    #[cfg(debug_assertions)]
    fn pretty_clauses(&self, clauses: &ClsSet) -> String {
        let mut s = String::new();
        s.push('{');
        for clause in clauses {
            s.push(' ');
            s.push_str(&format!("{}", clause))
        }
        s.push(' ');
        s.push('}');
        s
    }

    /// Checks the consistency of `pred_to_clauses`.
    #[cfg(debug_assertions)]
    fn check_pred_to_clauses(&self) -> Res<()> {
        for (cls_idx, clause) in self.clauses.index_iter() {
            for (pred, _) in clause.lhs_preds() {
                let pred = *pred;
                if self[pred].is_defined() {
                    bail!(
                        "predicate {} is forced but appears in lhs of clause {}",
                        self[pred],
                        cls_idx
                    )
                }
                if !self.pred_to_clauses[pred].0.contains(&cls_idx) {
                    bail!(
                        "predicate {} appears in lhs of clause {} \
                         but is not registered as such\n{}\nlhs: {}\nrhs: {}",
                        self[pred],
                        cls_idx,
                        self.clauses[cls_idx].to_string_info(&self.preds)?,
                        self.pretty_clauses(&self.pred_to_clauses[pred].0),
                        self.pretty_clauses(&self.pred_to_clauses[pred].1)
                    )
                }
            }
            if let Some((pred, _)) = clause.rhs() {
                if self[pred].is_defined() {
                    bail!(
                        "predicate {} is forced but appears in rhs of clause {}",
                        self[pred],
                        cls_idx
                    )
                }
                if !self.pred_to_clauses[pred].1.contains(&cls_idx) {
                    bail!(
                        "predicate {} appears in rhs of clause {} \
                         but is not registered as such\n{}\nlhs: {}\nrhs: {}",
                        self[pred],
                        cls_idx,
                        self.clauses[cls_idx].to_string_info(&self.preds)?,
                        self.pretty_clauses(&self.pred_to_clauses[pred].0),
                        self.pretty_clauses(&self.pred_to_clauses[pred].1)
                    )
                }
            }
        }

        for (pred, &(ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
            for clause in lhs {
                if *clause >= self.clauses.len() {
                    bail!(
                        "predicate {} is registered as appearing in lhs of clause {} \
                         which is above the maximal clause index",
                        self[pred],
                        clause
                    )
                }
                if self.clauses[*clause].lhs_preds().get(&pred).is_none() {
                    bail!(
                        "predicate {} is registered as appearing in lhs of clause {} \
                         but it's not the case\n{}\nlhs: {}\nrhs: {}",
                        self[pred],
                        clause,
                        self.clauses[*clause].to_string_info(&self.preds)?,
                        self.pretty_clauses(&self.pred_to_clauses[pred].0),
                        self.pretty_clauses(&self.pred_to_clauses[pred].1)
                    )
                }
            }
            for clause in rhs {
                if *clause >= self.clauses.len() {
                    bail!(
                        "predicate {} is registered as appearing in rhs of clause {} \
                         which is above the maximal clause index",
                        self[pred],
                        clause
                    )
                }
                if let Some((this_pred, _)) = self.clauses[*clause].rhs() {
                    if this_pred == pred {
                        continue;
                    }
                }
                bail!(
                    "predicate {} is registered to appear in rhs of clause {} \
                     but it's not the case\n{}\nlhs: {}\nrhs: {}",
                    self[pred],
                    clause,
                    self.clauses[*clause].to_string_info(&self.preds)?,
                    self.pretty_clauses(&self.pred_to_clauses[pred].0),
                    self.pretty_clauses(&self.pred_to_clauses[pred].1)
                )
            }
        }
        Ok(())
    }

    /// Dumps the instance as an SMT-LIB 2 problem.
    pub fn dump_as_smt2<File, Blah>(&self, w: &mut File, blah: Blah) -> Res<()>
    where
        File: Write,
        Blah: AsRef<str>,
    {
        let blah = blah.as_ref();

        for line in blah.lines() {
            writeln!(w, "; {}", line)?
        }
        writeln!(w)?;
        writeln!(w, "(set-logic HORN)")?;
        writeln!(w)?;

        writeln!(w, "; Datatypes")?;

        dtyp::write_all(w, "")?;

        dtyp::write_constructor_map(w, "; ")?;
        writeln!(w)?;

        writeln!(w, "; Functions")?;
        fun::write_all(w, "", true)?;

        writeln!(w)?;

        writeln!(w, "; Side-clauses")?;
        for side_clause in &self.side_clauses {
            side_clause.write(
                w,
                |w, var_info| write!(w, "{}", var_info.name),
                |_, _, _, _| panic!("illegal side-clause: found predicate application(s)"),
                true,
            )?;
            writeln!(w)?;
        }

        writeln!(w)?;
        writeln!(w)?;

        for (pred_idx, pred) in self.preds.index_iter() {
            if !self[pred_idx].is_defined() {
                if let Some(term) = self[pred_idx].strength() {
                    writeln!(w, "; Strengthening term:")?;
                    writeln!(w, ";   {}", term)?
                }
                write!(w, "({}\n  {}\n  (", keywords::cmd::dec_fun, pred.name)?;
                for typ in &pred.sig {
                    write!(w, " {}", typ)?
                }
                writeln!(w, " ) Bool\n)")?
            }
        }

        writeln!(
            w,
            "\n; Original clauses' names ({}) {{",
            self.old_names.len()
        )?;
        for (idx, name) in &self.old_names {
            writeln!(w, ";   #{}: `{}`.", idx, name)?
        }
        writeln!(w, "; }}")?;

        for (idx, clause) in self.clauses.index_iter() {
            writeln!(w, "\n; Clause #{}", idx)?;

            // Print source.
            let from = clause.from();
            write!(w, ";   from: #{}", from)?;
            if let Some(name) = self.old_names.get(&from) {
                write!(w, ": {}", name)?
            }
            writeln!(w)?;

            clause.write(
                w,
                |w, var_info| write!(w, "{}", var_info.name),
                |w, p, args, bindings| {
                    if !args.is_empty() {
                        write!(w, "(")?
                    }
                    w.write_all(self[p].name.as_bytes())?;
                    for arg in args.iter() {
                        write!(w, " ")?;
                        arg.write_with(w, |w, var| write!(w, "{}", clause.vars[var]), bindings)?
                    }
                    if !args.is_empty() {
                        write!(w, ")")
                    } else {
                        Ok(())
                    }
                },
                true,
            )?;
            writeln!(w)?;
            writeln!(w)?
        }

        writeln!(w, "\n(check-sat)")?;

        Ok(())
    }

    /// Simplifies some predicate definitions.
    ///
    /// Simplifies its internal predicate definitions and the ones in the model.
    pub fn simplify_pred_defs(&mut self, model: &mut Model) -> Res<()> {
        let mut old_model = Vec::with_capacity(model.len());
        ::std::mem::swap(&mut old_model, model);
        for (pred, def) in old_model {
            let simplified = def.simplify_pred_apps(&model, &self.preds);
            model.push((pred, simplified))
        }

        if self.sorted_pred_terms.is_empty() {
            self.finalize()?
        }

        let mut old_tterms: PrdMap<_> =
            self.preds.iter_mut().map(|pred| pred.unset_def()).collect();

        for pred in &self.sorted_pred_terms {
            let pred = *pred;
            let mut curr_def = None;
            ::std::mem::swap(&mut curr_def, &mut old_tterms[pred]);
            if let Some(def) = curr_def {
                let simplified = def.simplify_pred_apps(&model, &self.preds);
                self.preds[pred].set_def(simplified)?
            }
        }
        Ok(())
    }

    /// Writes a conjunction of top terms.
    pub fn write_tterms_conj<W: Write>(&self, w: &mut W, conj: &[TTerms]) -> Res<()> {
        if conj.is_empty() {
            write!(w, "true")?
        } else if conj.len() == 1 {
            self.print_tterms_as_model(w, &conj[0])?
        } else {
            write!(w, "(and")?;
            for tterms in conj {
                write!(w, " ")?;
                self.print_tterms_as_model(w, tterms)?
            }
            write!(w, ")")?
        }
        Ok(())
    }

    /// Writes a predicate signature.
    ///
    /// Does not write the name of the predicate.
    pub fn write_pred_sig<W: Write>(&self, w: &mut W, pred: PrdIdx) -> Res<()> {
        write!(w, "(")?;
        for (var, typ) in self[pred].original_sig().index_iter() {
            write!(w, " ({} {})", var.default_str(), typ)?
        }
        write!(w, " ) {}", typ::bool())?;
        Ok(())
    }

    /// Writes some definitions.
    pub fn write_definitions<W: Write>(
        &self,
        w: &mut W,
        pref: &str,
        model: ConjModelRef,
    ) -> Res<()> {
        fun::write_for_model(w, pref, &model)?;

        for defs in model {
            if defs.is_empty() {
                ()
            } else if defs.len() == 1 {
                let (pred, ref tterms) = defs[0];

                writeln!(w, "{}({} {}", pref, keywords::cmd::def_fun, self[pred].name)?;
                write!(w, "{}  ", pref)?;
                self.write_pred_sig(w, pred)?;
                write!(w, "\n{}  ", pref)?;
                self.write_tterms_conj(w, tterms)?;
                writeln!(w, "\n{})", pref)?
            } else {
                write!(w, "{}({} (", pref, keywords::cmd::def_funs_rec)?;
                for &(pred, _) in defs {
                    write!(w, "\n{}  {} ", pref, self[pred].name)?;
                    self.write_pred_sig(w, pred)?;
                }
                write!(w, "\n{}) (", pref)?;
                for &(_, ref tterms) in defs {
                    write!(w, "\n{}  ", pref)?;
                    self.write_tterms_conj(w, tterms)?;
                }
                writeln!(w, "\n{}) )", pref)?;
            }
        }

        Ok(())
    }

    /// Writes a model.
    pub fn write_model<W: Write>(&self, model: ConjModelRef, w: &mut W) -> Res<()> {
        writeln!(w, "(model")?;
        self.write_definitions(w, "  ", model)?;
        writeln!(w, ")")?;
        Ok(())
    }

    /// Sets print-success flag.
    pub fn set_print_success(&mut self, b: bool) {
        self.print_success = b
    }
    /// Print-success flag accessor.
    pub fn print_success(&self) -> bool {
        self.print_success
    }
    /// Sets unsat-cores flag.
    pub fn set_unsat_cores(&mut self, b: bool) {
        self.unsat_cores = b
    }
    /// Unsat-cores flag.
    pub fn unsat_cores(&self) -> bool {
        self.unsat_cores
    }
    /// Sets proofs flag.
    pub fn set_proofs(&mut self, b: bool) {
        self.proofs = b
    }
    /// Unsat-cores flag.
    pub fn proofs(&self) -> bool {
        self.proofs
    }

    /// True if the teacher needs to maintain a sample graph (unsat
    /// cores/proofs).
    pub fn track_samples(&self) -> bool {
        false // self.unsat_cores() || self.proofs()
    }

    /// Converts `"true"` to `true`, `"false"` to `false`, and everything else to
    /// an error.
    fn bool_of_str(s: &str) -> Res<bool> {
        match s {
            "true" => Ok(true),
            "false" => Ok(false),
            _ => bail!("expected boolean `true/false`, got `{}`", s),
        }
    }

    /// Sets an option.
    pub fn set_option(&mut self, flag: &str, val: &str) -> Res<()> {
        let flag_err = || format!("while handling set-option for {}", flag);
        match flag {
            "print-success" => {
                let print_succ = Self::bool_of_str(&val).chain_err(flag_err)?;
                self.set_print_success(print_succ)
            }
            "produce-unsat-cores" => {
                let unsat_cores = Self::bool_of_str(&val).chain_err(flag_err)?;
                self.set_unsat_cores(unsat_cores)
            }
            "produce-proofs" => {
                let proofs = Self::bool_of_str(&val).chain_err(flag_err)?;
                self.set_proofs(proofs)
            }
            _ => warn!(
                "ignoring (set-option :{} {}): unknown flag {}",
                flag, val, flag
            ),
        }
        Ok(())
    }
}

/// Lhs part of a cex.
type CexLhs = Vec<(PrdIdx, VarTermsSet)>;
/// Lhs part of a cex, reference version.
type CexLhsRef<'a> = &'a [(PrdIdx, VarTermsSet)];
/// Rhs part of a cex.
type CexRhs<'a> = Option<(PrdIdx, &'a VarTerms)>;

/// Cex-related functions.
impl Instance {
    /// Retrieves the lhs and rhs cex part from a bias.
    fn break_cex(&self, clause_idx: ClsIdx, bias: Bias) -> (CexLhs, CexRhs) {
        let clause = &self[clause_idx];
        let bias = if self.proofs { Bias::Non } else { bias };

        match bias {
            // Consider the whole lhs of the clause positive.
            Bias::Lft => (vec![], clause.rhs()),

            // Consider the rhs of the clause negative.
            Bias::Rgt => (
                clause
                    .lhs_preds()
                    .iter()
                    .map(|(pred, argss)| (*pred, argss.clone()))
                    .collect(),
                None,
            ),

            // Consider the rhs of the clause negative, and all lhs applications
            // positive except this one.
            Bias::NuRgt(pred, args) => {
                debug_assert! { clause.lhs_preds().get(& pred).is_some() }
                debug_assert! {
                  clause.lhs_preds().get(& pred).unwrap().contains(& args)
                }
                let mut argss = VarTermsSet::with_capacity(1);
                argss.insert(args);
                (vec![(pred, argss)], None)
            }

            // No bias.
            Bias::Non => (
                clause
                    .lhs_preds()
                    .iter()
                    .map(|(pred, argss)| (*pred, argss.clone()))
                    .collect(),
                clause.rhs(),
            ),
        }
    }

    /// Forces non-values in the cex if needed.
    pub fn force_non_values(&self, cex: &mut Cex, lhs: CexLhsRef, rhs: &CexRhs) {
        // Factored set of variables when fixing cex for arguments.
        let mut known_vars = VarSet::new();

        macro_rules! fix_cex {
            ($args:expr) => {{
                log! { @6 "fixing {}", $args }
                for arg in $args.iter() {
                    if let Some(var) = arg.var_idx() {
                        if !cex[var].is_known() {
                            // Value for `var` is a non-value.
                            let is_new = known_vars.insert(var);
                            // Variable appears in more than one arg, force its value.
                            if !is_new {
                                cex[var] = cex[var].typ().default_val()
                            }
                        }
                    } else {
                        for var in term::vars(arg) {
                            if !cex[var].is_known() {
                                cex[var] = cex[var].typ().default_val()
                            }
                        }
                    }
                }
            }};
        }

        // Force non-values in the cex if we're dealing with a constraint, not a
        // sample.
        if (
            // Positive sample?
            lhs.is_empty() && rhs.is_some()
        ) || (
            // Negative sample?
            lhs.len() == 1 && lhs.iter().all(|(_, argss)| argss.len() == 1) && rhs.is_none()
        ) {
            // We're generating a sample. Still need to force variables that appear
            // more than once in arguments.
            for (_, argss) in lhs {
                debug_assert_eq! { argss.len(), 1 }
                for args in argss {
                    fix_cex!(args)
                }
            }
            if let Some((_, args)) = rhs.as_ref() {
                fix_cex!(args)
            }
        } else {
            // We're dealing with a constraint, not a sample. Force non-values.
            for val in cex.iter_mut() {
                if !val.is_known() {
                    *val = val.typ().default_val()
                }
            }
        }
    }

    /// Transforms a cex for a clause into some learning data.
    ///
    /// Returns `true` if some new data was generated.
    pub fn clause_cex_to_data(&self, data: &mut Data, clause_idx: ClsIdx, cex: BCex) -> Res<bool> {
        let (mut cex, bias) = cex;

        if_log! { @6
          let clause = & self[clause_idx] ;
          let mut s = String::new() ;
          for (var, val) in cex.index_iter() {
            s.push_str(& format!("{}: {}, ", var.default_str(), val))
          }
          log! { @6
            "lhs preds: {}", clause.lhs_pred_apps_len() ;
            "      rhs: {}", if clause.rhs().is_some() { "some" } else { "none" } ;
            "     bias: {}", bias ;
            "      cex: {}", s
          }
        }

        let (lhs, rhs) = self.break_cex(clause_idx, bias);
        self.force_non_values(&mut cex, &lhs, &rhs);

        // Evaluates some arguments for a predicate.
        macro_rules! eval {
            ($args:expr) => {{
                use crate::var_to::vals::RVarVals;
                let mut sample = RVarVals::with_capacity($args.len());
                for arg in $args.get() {
                    let val = arg.eval(&cex)?;
                    sample.push(val)
                }
                sample
            }};
        }

        // Evaluate antecedents.
        let mut antecedents = vec![];
        for (pred, argss) in lhs {
            for args in argss {
                let sample = eval!(args);
                antecedents.push((pred, sample))
            }
        }

        let consequent = if let Some((pred, args)) = rhs {
            let sample = eval!(args);
            Some((pred, sample))
        } else {
            None
        };

        if_log! { @6
          let mut s = String::new() ;
          if ! antecedents.is_empty() {
            for (pred, sample) in & antecedents {
              s.push_str( & format!("({} {}) ", self[* pred], sample) )
            }
          } else {
            s.push_str("true ")
          }
          s.push_str("=> ") ;
          if let Some((pred, sample)) = consequent.as_ref() {
            s.push_str( & format!("({} {})", self[* pred], sample) )
          } else {
            s.push_str("false")
          }
          log! { @6 "{}", s }
        }
        data.add_data(clause_idx, antecedents, consequent)
    }

    /// Turns some teacher counterexamples into learning data.
    pub fn cexs_to_data(&self, data: &mut Data, cexs: Cexs) -> Res<bool> {
        let mut changed = false;

        for (clause_idx, cexs) in cexs {
            log! { @5 "adding cexs for #{}", clause_idx }

            for cex in cexs {
                let new_stuff = self.clause_cex_to_data(data, clause_idx, cex)?;
                changed = changed || new_stuff
            }
        }

        let (pos, neg) = data.propagate()?;

        Ok(changed || pos > 0 || neg > 0)
    }
}

impl ::std::ops::Index<PrdIdx> for Instance {
    type Output = Pred;
    fn index(&self, index: PrdIdx) -> &Pred {
        &self.preds[index]
    }
}
impl ::std::ops::Index<ClsIdx> for Instance {
    type Output = Clause;
    fn index(&self, index: ClsIdx) -> &Clause {
        &self.clauses[index]
    }
}
impl ::std::ops::IndexMut<ClsIdx> for Instance {
    fn index_mut(&mut self, index: ClsIdx) -> &mut Clause {
        &mut self.clauses[index]
    }
}
impl AsRef<Instance> for Instance {
    fn as_ref(&self) -> &Self {
        self
    }
}
impl AsMut<Instance> for Instance {
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}
// impl ::std::ops::Deref for Instance {
//   type Target = Self ;
//   fn deref(& self) -> & Self {
//     self
//   }
// }
// impl ::std::ops::DerefMut for Instance {
//   fn deref_mut(& mut self) -> & mut Self {
//     self
//   }
// }

impl<'a> PebcakFmt<'a> for Clause {
    type Info = &'a Preds;
    fn pebcak_err(&self) -> ErrorKind {
        "during clause pebcak formatting".into()
    }
    fn pebcak_io_fmt<W: Write>(&self, w: &mut W, preds: &'a Preds) -> IoRes<()> {
        self.write(
            w,
            |w, var_info| write!(w, "{}", var_info.name),
            |w, prd, args, bindings| {
                write!(w, "(")?;
                w.write_all(preds[prd].name.as_bytes())?;
                for arg in args.iter() {
                    write!(w, " ")?;
                    arg.write_with(w, |w, var| write!(w, "{}", self.vars[var]), bindings)?
                }
                write!(w, ")")
            },
            false,
        )
    }
}

impl<'a> PebcakFmt<'a> for Instance {
    type Info = ();
    fn pebcak_err(&self) -> ErrorKind {
        "during instance pebcak formatting".into()
    }
    fn pebcak_io_fmt<W: Write>(&self, w: &mut W, _: ()) -> IoRes<()> {
        writeln!(w, "; Datatypes:")?;

        dtyp::write_all(w, "")?;

        dtyp::write_constructor_map(w, "; ")?;

        for pred in &self.preds {
            if !pred.is_defined() {
                write!(w, "({}\n  {}\n  (", keywords::cmd::dec_fun, pred.name)?;
                for typ in &pred.sig {
                    write!(w, " {}", typ)?
                }
                writeln!(w, " ) Bool\n)")?;
                if pred.sig.len() != pred.original_sig().len() {
                    write!(w, "; original signature:\n;")?;
                    for (var, typ) in pred.original_sig().index_iter() {
                        write!(w, " ({} {})", var.default_str(), typ)?
                    }
                    writeln!(w, "\n; variable map (new -> old):\n;")?;
                    for (src, tgt) in pred.original_sig_map().index_iter() {
                        write!(w, " {} -> {},", src.default_str(), tgt.default_str())?
                    }
                    writeln!(w)?
                }
            }
        }

        let empty_prd_set = PrdSet::new();
        if self.sorted_pred_terms.is_empty() {
            // Either there's no forced predicate, or we are printing before
            // finalizing.
            for (pred, tterms) in self
                .preds
                .iter()
                .filter_map(|pred| pred.def().map(|tt| (pred.idx, tt)))
            {
                write!(w, "({} {}\n  (", keywords::cmd::def_fun, self[pred])?;
                for (var, typ) in self[pred].sig.index_iter() {
                    write!(w, " (v_{} {})", var, typ)?
                }
                write!(w, " ) Bool\n  ")?;
                tterms
                    .expr_to_smt2(w, &(&empty_prd_set, &empty_prd_set, &self.preds))
                    .unwrap();
                writeln!(w, "\n)")?
            }
        } else {
            for pred in &self.sorted_pred_terms {
                let pred = *pred;
                write!(w, "({} {}\n  (", keywords::cmd::def_fun, self[pred])?;
                for (var, typ) in self[pred].sig.index_iter() {
                    write!(w, " (v_{} {})", var, typ)?
                }
                let tterms = self[pred].def().unwrap();
                write!(w, " ) Bool\n  ")?;
                tterms
                    .expr_to_smt2(w, &(&empty_prd_set, &empty_prd_set, &self.preds))
                    .unwrap();
                writeln!(w, "\n)",)?
            }
        }

        writeln!(
            w,
            "\n; Original clauses' names ({}) {{",
            self.old_names.len()
        )?;
        for (idx, name) in &self.old_names {
            writeln!(w, "; Original clause #{} is called `{}`.", idx, name)?
        }
        writeln!(w, "; }}")?;

        for (idx, clause) in self.clauses.index_iter() {
            writeln!(w, "\n; Clause #{}", idx)?;
            let from = clause.from();
            write!(w, ";   from: #{}", from)?;
            if let Some(name) = self.old_names.get(&from) {
                write!(w, ": {}", name)?
            }
            writeln!(w)?;
            clause.pebcak_io_fmt(w, &self.preds)?
        }

        writeln!(w, "\npred to clauses:")?;
        for (pred, &(ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
            write!(w, "  {}: lhs {{", self[pred])?;
            for lhs in lhs {
                write!(w, " {}", lhs)?
            }
            write!(w, " }}, rhs {{")?;
            for rhs in rhs {
                write!(w, " {}", rhs)?
            }
            writeln!(w, " }}")?
        }

        Ok(())
    }
}

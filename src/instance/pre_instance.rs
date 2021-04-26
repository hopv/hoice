//! A pre-instance wraps an instance for preprocessing.

use crate::{
    common::{
        smt::{ClauseTrivialExt, SmtImpl},
        *,
    },
    preproc::utils::ExtractionCxt,
};

/// Performs a checksat.
macro_rules! check_sat {
    ($pre_instance:expr) => {{
        // let actlit = if $pre_instance.reset_solver {
        //   Some( $pre_instance.solver.get_actlit() ? )
        // } else {
        //   None
        // } ;

        // let sat =
        $pre_instance.solver.check_sat()?
        // ;

        // if let Some(actlit) = actlit {
        //   $pre_instance.solver.de_actlit(actlit) ?
        // }

        // sat
    }};
}

/// Wraps an instance for preprocessing.
///
/// Provides high-level functions to manipulate predicates and clauses. The reason for this wrapper
/// is that an [`Instance`] should almost never be mutated, except during creation and
/// preprocessing.
///
/// This is why the instance type barely exposes any way to mutate its values.
///
/// [`Instance`]: ../common/struct.Instance.html (Instance struct)
pub struct PreInstance<'a> {
    /// The instance wrapped.
    instance: &'a mut Instance,
    /// Solver used for triviality-checking.
    solver: Solver<()>,
    /// Clause simplifier.
    simplifier: ClauseSimplifier,

    /// Factored vector of clauses to simplify.
    clauses_to_simplify: Vec<ClsIdx>,

    /// Set of variables used by some simplification techniques.
    vars: VarSet,

    /// Term extraction context.
    extraction: ExtractionCxt,

    /// Use actlits in checksats.
    reset_solver: bool,
}
impl<'a> PreInstance<'a> {
    /// Constructor.
    pub fn new(instance: &'a mut Instance) -> Res<Self> {
        let solver = conf.solver.spawn("preproc", (), &*instance)?;

        let simplifier = ClauseSimplifier::new();
        let clauses_to_simplify = Vec::with_capacity(7);

        let mut reset_solver = false;

        fun::iter(|_| {
            reset_solver = true;
            Ok(())
        })?;

        if dtyp::get_all().iter().next().is_some() {
            reset_solver = true
        }

        Ok(PreInstance {
            instance,
            solver,
            simplifier,
            clauses_to_simplify,
            vars: VarSet::new(),
            extraction: ExtractionCxt::new(),
            reset_solver,
        })
    }

    /// Resets the solver.
    pub fn reset_solver(&mut self) -> Res<()> {
        smt::preproc_reset(&mut self.solver)
    }

    /// Accessor for the solver.
    pub fn solver(&mut self) -> &mut Solver<()> {
        &mut self.solver
    }

    /// Accessor for the extraction context and the instance.
    pub fn extraction(&mut self) -> (&mut ExtractionCxt, &mut Instance) {
        (&mut self.extraction, self.instance)
    }

    /// Destroys the pre instance, kills the internal solver.
    pub fn destroy(mut self) -> Res<()> {
        self.solver
            .kill()
            .chain_err(|| "While killing preproc solver")?;
        Ok(())
    }

    /// Sets the strengthener for a predicate.
    ///
    /// A strengthener is a term such that the predicate should be false at least when this term is
    /// false.
    pub fn set_strength(&mut self, pred: PrdIdx, strengthener: Term) -> Res<()> {
        self.instance.preds[pred].set_strength(strengthener)
    }
    /// Unsets the strengthener for a predicate.
    pub fn unset_strength(&mut self, pred: PrdIdx) -> Option<Term> {
        self.instance.preds[pred].unset_strength()
    }

    /// Adds a companion function for a predicate.
    ///
    /// Function that were created specifically for this predicate, and must be given to the user
    /// before giving the definition for this predicate.
    pub fn add_companion_fun(&mut self, pred: PrdIdx, fun: Fun) {
        self.instance.preds[pred].add_fun(fun)
    }

    /// Checks whether a clause alone forces the definition of a predicate.
    /// - forces to true all predicates appearing in `terms => (p vars)` where
    ///   `vars` are all distinct and don't appear in `terms`
    /// - forces to false all predicates appearing in `terms /\ (p vars) =>
    ///   false` where `vars` are all distinct and don't appear in `terms`
    pub fn force_trivial_from_clause(&mut self, clause_idx: ClsIdx) -> Option<(PrdIdx, bool)> {
        if !self.instance[clause_idx].preds_changed() && !self.instance[clause_idx].terms_changed()
        {
            return None;
        }
        self.instance[clause_idx].preds_checked();

        let clause = &self.instance[clause_idx];

        let (pred, positive, args) = if let Some((pred, args)) = clause.rhs() {
            // Positive clause.
            if clause.lhs_preds().is_empty() {
                // No lhs predicate applications.
                (pred, true, args)
            } else {
                return None;
            }
        } else {
            // Negative clause.
            let mut lhs_preds = clause.lhs_preds().iter();

            if let Some((pred, argss)) = lhs_preds.next() {
                if lhs_preds.next().is_none() // Only one predicate?
        && argss.len() == 1
                {
                    // Only one application?
                    let args = argss.iter().next().unwrap();

                    (*pred, false, args)
                } else {
                    return None;
                }
            } else {
                return None;
            }
        };

        self.vars.clear();
        // Are all arguments different variables?
        for arg in args.iter() {
            if let Some(v) = arg.var_idx() {
                let is_new = self.vars.insert(v);
                if !is_new {
                    return None;
                }
            } else {
                return None;
            }
        }

        for term in clause.lhs_terms() {
            // `vars` don't appear in any lhs term?
            if term.mentions_one_of(&self.vars) {
                return None;
            }
        }

        Some((pred, positive))
    }

    /// Performs cheap triviality checks.
    ///
    /// - forces to false (true) all the predicates that only appear in clauses'
    ///   lhs (rhs)
    /// - forces to true all predicates appearing in `terms => (p vars)` where
    ///   `vars` are all distinct and don't appear in `terms`
    /// - forces to false all predicates appearing in `terms /\ (p vars) =>
    ///   false` where `vars` are all distinct and don't appear in `terms`
    pub fn force_trivial(&mut self) -> Res<RedInfo> {
        let mut info: RedInfo = (0, 0, 0).into();
        let mut fixed_point = false;

        while !fixed_point {
            fixed_point = true;

            'all_preds: for pred in PrdRange::zero_to(self.instance.preds.len()) {
                if self.instance[pred].is_defined() {
                    continue 'all_preds;
                }

                let force = if self.instance.pred_to_clauses[pred].1.is_empty() {
                    // Only appears as an antecedent.
                    Some(false)
                } else if self.instance.pred_to_clauses[pred].0.is_empty()
                    || self.instance.pred_to_clauses[pred]
                        .1
                        .is_superset(&self.instance.pred_to_clauses[pred].0)
                {
                    // Only appears as a consequent.
                    // ||
                    // Only appears as a antecedent in clauses where it's also an
                    // consequent.
                    Some(true)
                } else if self.instance.pred_to_clauses[pred]
                    .0
                    .is_superset(&self.instance.pred_to_clauses[pred].1)
                {
                    // Only appears as a consequent in clauses where it's also an
                    // antecedent.
                    Some(false)
                } else {
                    None
                };

                if let Some(pos) = force {
                    info.preds += 1;
                    fixed_point = false;
                    info += if pos {
                        self.force_true(pred)?
                    } else {
                        self.force_false(pred)?
                    }
                }
            }

            let mut force = vec![];

            for clause_idx in ClsRange::zero_to(self.clauses.len()) {
                if let Some((pred, positive)) = self.force_trivial_from_clause(clause_idx) {
                    force.push((pred, positive))
                }
            }

            for (pred, positive) in force {
                if !self[pred].is_defined() {
                    fixed_point = false;
                    info.preds += 1;
                    if positive {
                        info += self.force_true(pred)?
                    } else {
                        info += self.force_false(pred)?
                    }
                }
            }
        }
        Ok(info)
    }

    /// Strict negative clauses.
    pub fn strict_neg_clauses(
        &mut self,
    ) -> (
        &mut ExtractionCxt,
        &Instance,
        impl Iterator<Item = (ClsIdx, &Clause)>,
    ) {
        let extraction = &mut self.extraction;
        let instance = &self.instance;
        let clauses = &instance.clauses;
        (
            extraction,
            instance,
            clauses.index_iter().filter(|(_, clause)| {
                clause.rhs().is_none()
                    && clause.lhs_preds().len() == 1
                    && (clause
                        .lhs_preds()
                        .iter()
                        .next()
                        .map(|(_, apps)| apps.len() == 1)
                        .unwrap_or(false))
            }),
        )
    }

    /// Non-strict negative clauses.
    pub fn non_strict_neg_clauses(
        &mut self,
    ) -> (
        &mut ExtractionCxt,
        &Instance,
        impl Iterator<Item = (ClsIdx, &Clause)>,
    ) {
        let extraction = &mut self.extraction;
        let instance = &self.instance;
        let clauses = &instance.clauses;
        (
            extraction,
            instance,
            clauses.index_iter().filter(|(_, clause)| {
                clause.rhs().is_none()
                    && (clause.lhs_preds().len() > 1
                        || clause.lhs_preds().iter().any(|(_, apps)| apps.len() > 1))
            }),
        )
    }

    /// Simplifies all the clauses.
    pub fn simplify_all(&mut self) -> Res<RedInfo> {
        let mut info = RedInfo::new(); // self.force_trivial() ? ;

        // Go through the clauses in reverse so that swap removes are safe.
        let mut clause = self.instance.clauses.next_index();

        while clause > 0 {
            clause.dec();
            info += self.simplify_clause(clause)?;
            conf.check_timeout()?
        }

        info += self.force_trivial()?;

        if self.reset_solver {
            smt::reset(&mut self.solver, &self.instance)?;
        }

        // Check side-clauses.
        scoped! {
          let instance = & mut self.instance ;
          let solver = & mut self.solver ;

          log! { @4 "checking side clauses" }

          info += instance.side_clauses_retain(
            |clause| {
              solver.push(1) ? ;
              let res = match solver.is_clause_trivial(clause) ? {
                None => bail!( ErrorKind::Unsat ),
                Some(is_trivial) => Ok(is_trivial),
              } ;
              solver.pop(1) ? ;
              res
            }
          ) ? ;
        }

        if self.reset_solver {
            smt::reset(&mut self.solver, &self.instance)?;
        }

        Ok(info)
    }

    /// Simplifies some clauses.
    ///
    /// - can change **all** clause indices because of potential swap removes
    /// - does not run `force_trivial`
    fn simplify_clauses(&mut self) -> Res<RedInfo> {
        let mut info = RedInfo::new();
        // We're **popping**, so sort lowest to highest to avoid problems with swap
        // removes.
        self.clauses_to_simplify
            .sort_unstable_by(|c_1, c_2| c_1.cmp(c_2));
        log! { @4 "simplify clauses ({})", self.clauses_to_simplify.len() }
        let mut prev = None;

        let mut force = PrdHMap::new();

        while let Some(clause) = self.clauses_to_simplify.pop() {
            log! { @5 "{}", self[clause].to_string_info(self.preds()).unwrap() }
            prev = {
                if let Some(prev) = prev {
                    if clause == prev {
                        continue;
                    }
                }
                Some(clause)
            };
            info += self.simplify_clause(clause)?;
            if !info.non_zero() {
                if let Some((pred, pos)) = self.force_trivial_from_clause(clause) {
                    let prev = force.insert(pred, pos);
                    debug_assert! {
                      if let Some(prev) = prev {
                        prev == pos
                      } else {
                        true
                      }
                    }
                }
            }
        }

        for (pred, pos) in force {
            if pos {
                info += self.force_true(pred)?
            } else {
                info += self.force_false(pred)?
            }
        }

        self.check("after `simplify_clauses`")?;
        Ok(info)
    }

    /// Simplifies the terms of a clause.
    ///
    /// Returns true if the clause should be removed.
    fn simplify_clause_term(&mut self, clause: ClsIdx) -> Res<bool> {
        if self.instance[clause].terms_changed() {
            log! { @3 "propagation..." }
            self.simplifier
                .clause_propagate(&mut self.instance.clauses[clause], &self.instance.preds)?;
            log! { @3 "pruning..." }
            // Remove redundant atoms.
            if conf.preproc.prune_terms {
                self.prune_atoms(clause)?
            }
            self.instance[clause].lhs_terms_checked();
            log! { @3 "trivial?" }
            self.is_clause_trivial(clause)
        } else {
            Ok(false)
        }
    }

    /// Simplifies a clause.
    ///
    /// This function might create new clauses. Potentially voids the semantics
    /// of clause indices *after* `clause`. Modifying this function by making it
    /// void clause indices *before* `clause` will break the whole
    /// pre-processing.
    // #[cfg_attr(feature = "cargo-clippy", allow(cyclomatic_complexity))]
    fn simplify_clause(&mut self, clause: ClsIdx) -> Res<RedInfo> {
        macro_rules! rm_return {
            ($blah:expr) => {{
                log! { @debug
                  "  removing clause #{} by {}", clause, $blah
                }
                self.instance.forget_clause(clause)?;
                return Ok(RedInfo::of_clauses_rmed(1));
            }};
        }

        if self.instance.simplify_clauses() {
            log! { @debug
              "simplifying clause #{} (terms_changed: {})",
              clause, self.instance[clause].terms_changed()
            }

            if self.instance[clause].is_pred_trivial() {
                rm_return!("trivial implication")
            }

            if self.instance[clause].is_unsat() {
                unsat!("by preprocessing, clause simplification")
            }

            if self.simplify_clause_term(clause)? {
                rm_return!("term simplification")
            }

            log! { @3 "redundancy check..." }

            if self.is_redundant(clause) {
                rm_return!("clause redundant")
            }
        }

        log! { @3 "split disj..." }

        // Try to split the clause.
        let res = self.split(clause);

        log! { @3 "done" }

        res
    }

    /// Splits disjunctions.
    ///
    /// Splits a clause if
    ///
    /// - it contains a disjunction with kids `subs`
    /// - `f_subs` is not empty, where `f_subs` are the kids on which `f` is true
    ///
    /// Generates one clause `C` per element `f_sub` of `f_subs` where `C` is
    /// `idx` augmented with the term `sub`. If `f_subs == subs`, drops clause
    /// `idx`. Otherwise, removes the disjunction from `idx` and adds the
    /// disjunction of `subs` minus `f_subs`.
    fn split_on<F>(&mut self, idx: ClsIdx, f: F) -> Res<RedInfo>
    where
        F: Fn(&Term) -> bool,
    {
        let mut info = RedInfo::new();
        macro_rules! clause {
            () => {
                self.instance[idx]
            };
        }

        let mut split: Option<(Term, Vec<_>, Vec<_>)> = None;
        let (mut f_subs, mut others) = (vec![], vec![]);

        for maybe_disj in clause!().lhs_terms() {
            if let Some(subs) = maybe_disj.disj_inspect() {
                for sub in subs {
                    if f(sub) {
                        f_subs.push(sub.clone())
                    } else {
                        others.push(sub.clone())
                    }
                }

                if !f_subs.is_empty() {
                    if let Some((_, prev, _)) = split.as_ref() {
                        if prev.len() > 1 && f_subs.len() > 1 {
                            // Skip if we already have
                            return Ok(info);
                        }
                    }

                    split = Some((
                        maybe_disj.clone(),
                        ::std::mem::replace(&mut f_subs, vec![]),
                        ::std::mem::replace(&mut others, vec![]),
                    ))
                } else {
                    others.clear()
                }
            }
        }

        if let Some((disj, f_subs, others)) = split {
            debug_assert! { ! f_subs.is_empty() }

            let was_there = clause!().rm_term(&disj);
            debug_assert! { was_there }

            let clause = if others.is_empty() {
                info.clauses_rmed += 1;
                self.instance.forget_clause(idx)?
            } else {
                let clause = clause!().clone();
                clause!().insert_term(term::or(others));
                info += self.simplify_clause(idx)?;
                clause
            };

            for f_sub in f_subs {
                let mut clause = clause.clone();
                clause.insert_term(f_sub);
                info.clauses_added += 1;
                if let Some(idx) = self.instance.push_clause(clause)? {
                    info += self.simplify_clause(idx)?
                }
                ()
            }
        } else {
            let mut split: Option<(VarIdx, _, _)> = None;

            // We haven't split. Maybe we can split on the arguments of the rhs.
            if let Some((_, args)) = clause!().rhs() {
                'args: for (index, arg) in args.index_iter() {
                    if let Some((c, t, e)) = arg.ite_inspect() {
                        debug_assert! { split.is_none() }
                        if f(c) || { c.rm_neg().as_ref().map(|c| f(c)).unwrap_or(false) } {
                            split = Some((
                                index,
                                (c.clone(), t.clone()),
                                (term::not(c.clone()), e.clone()),
                            ))
                        }
                        break 'args;
                    }
                }
            }

            if let Some((index, (lhs_1, rhs_1), (lhs_2, rhs_2))) = split {
                let (pred, args) = clause!().unset_rhs().unwrap();

                // let (mut args_1, mut args_2) = (args.clone(), args) ;
                let mut args_1 = args.get().clone();
                let mut args_2 = args.get().clone();

                args_1[index] = rhs_1;
                args_2[index] = rhs_2;

                let mut other_clause = clause!().clone_with_rhs(
                    Some(TTerm::P {
                        pred,
                        args: var_to::terms::new(args_2),
                    }),
                    "split",
                );

                clause!().set_rhs(pred, var_to::terms::new(args_1))?;
                clause!().insert_term(lhs_1);

                other_clause.insert_term(lhs_2);
                info += self.simplify_clause(idx)?;

                if let Some(idx) = self.instance.push_clause(other_clause)? {
                    info += self.simplify_clause(idx)?
                }
            }
        }

        Ok(info)
    }

    /// Checks whether a term is worth splitting on.
    fn should_split(term: &Term) -> bool {
        term.var_idx().is_some()
            || term
                .neg_inspect()
                .map(|sub| sub.var_idx().is_some())
                .unwrap_or(false)
            || term.eq_inspect().is_some()
    }

    /// Clever disjunction splitting.
    fn split(&mut self, idx: ClsIdx) -> Res<RedInfo> {
        self.split_on(idx, |sub| {
            if let Some(subs) = sub.conj_inspect() {
                for sub in subs {
                    if Self::should_split(sub) {
                        return true;
                    }
                }
                false
            } else {
                Self::should_split(sub)
            }
        })
    }

    /// Removes redundant atoms.
    fn prune_atoms(&mut self, clause: ClsIdx) -> Res<()> {
        let atoms: Vec<Term> = self.instance[clause].lhs_terms().iter().cloned().collect();

        if atoms.is_empty() {
            return Ok(());
        }

        let clause = &mut self.instance[clause];

        self.solver.push(1)?;

        self.solver.comment("Pruning atoms...")?;

        clause.declare(&mut self.solver)?;

        for atom in atoms {
            let keep = if let Some(implication) = SmtImpl::new(clause.lhs_terms(), &atom) {
                let actlit = self.solver.get_actlit()?;
                self.solver.assert_act(&actlit, &implication)?;
                let res = self.solver.check_sat_act(Some(&actlit))?;
                self.solver.de_actlit(actlit)?;
                res
            } else {
                bail!("failed to construct implication wrapper")
            };
            if !keep {
                let was_there = clause.rm_term(&atom);
                debug_assert! { was_there }
            }
            conf.check_timeout()?;
        }

        self.solver.comment("Done pruning atoms...")?;

        self.solver.pop(1)?;

        Ok(())
    }

    /// Checks whether a clause is trivial.
    ///
    /// Returns true if
    ///
    /// - the terms in the lhs are equivalent to `false`, or
    /// - the rhs is a predicate application contained in the lhs.
    fn is_clause_trivial(&mut self, clause_idx: ClsIdx) -> Res<bool> {
        if self.reset_solver {
            smt::reset(&mut self.solver, &self.instance)?;
        } else {
            self.solver.push(1)?;
        }
        let res = self
            .solver
            .is_clause_trivial(&mut self.instance[clause_idx]);
        if self.reset_solver {
            smt::reset(&mut self.solver, &self.instance)?;
        } else {
            self.solver.pop(1)?;
        }

        if let Some(res) = res? {
            Ok(res)
        } else {
            log! { @3
                "unsat because of {}",
                self.instance[clause_idx].to_string_info(self.instance.preds()).unwrap()
            }
            bail!(ErrorKind::Unsat)
        }
    }

    /// Checks whether a clause is trivial.
    ///
    /// Returns `None` if the clause is unsat.
    ///
    /// Returns true if
    ///
    /// - the terms in the lhs are equivalent to `false`, or
    /// - the rhs is a predicate application contained in the lhs.
    #[cfg_attr(feature = "cargo-clippy", allow(wrong_self_convention))]
    pub fn is_this_clause_trivial(&mut self, clause: &mut Clause) -> Res<Option<bool>> {
        if self.reset_solver {
            smt::reset(&mut self.solver, &self.instance)?;
        } else {
            self.solver.push(1)?;
        }
        let res = self.solver.is_clause_trivial(clause);
        if self.reset_solver {
            smt::reset(&mut self.solver, &self.instance)?;
        } else {
            self.solver.pop(1)?;
        }
        res
    }

    /// Checks the underlying instance is correct.
    pub fn check(&self, blah: &'static str) -> Res<()> {
        if !self.clauses_to_simplify.is_empty() {
            bail!("clauses_to_simplify is not empty: {}", blah)
        }
        self.instance.check(blah)
    }

    /// Forces all the remaining predicates to some DNFs at the same time.
    ///
    /// Checks that the positive and negative constraints are respected. Returns
    /// `true` if they are, *i.e.* the definitions are a legal model, and `false`
    /// otherwise.
    pub fn force_all_preds<Defs>(&mut self, defs: Defs, universal: bool) -> Res<(bool, RedInfo)>
    where
        Defs: IntoIterator<Item = (PrdIdx, Dnf)>,
    {
        log_debug! { "forcing all remaining predicates" }

        let mut info = RedInfo::new();
        info.clauses_rmed += self.instance.clauses.len();

        // Force predicates.
        for (pred, def) in defs {
            log! { @4 "  forcing (1) {}", self[pred] }
            let def = TTerms::dnf(
                def.into_iter()
                    .map(|(quantfed, conj)| {
                        (
                            if universal {
                                Quant::forall(quantfed)
                            } else {
                                Quant::exists(quantfed)
                            },
                            conj,
                        )
                    })
                    .collect(),
            );
            debug_assert! { !self.instance[pred].is_defined() }
            self.instance.preds[pred].set_def(def)?
        }

        // Check if instance is unsat before dropping clauses.
        self.finalize()?;
        let is_sat = self.check_pred_defs()?;

        // Drop all clauses.
        log_debug! { "  unlinking all predicates" }
        for &mut (ref mut lhs, ref mut rhs) in self.instance.pred_to_clauses.iter_mut() {
            lhs.clear();
            rhs.clear()
        }
        log_debug! { "  dropping non pos/neg clauses" }
        let mut clause: ClsIdx = 0.into();
        while clause < self.instance.clauses.len() {
            if self.instance.clauses[clause].rhs().is_none()
                || self.instance.clauses[clause].lhs_preds().is_empty()
            {
                clause.inc();
                continue;
            } else {
                self.instance.clauses.swap_remove(clause);
            }
        }
        log_debug! { "  checking pred defs" }

        for (pred, _) in self.preds().index_iter() {
            if !self[pred].is_defined() {
                bail!(format!(
                    "error in `force_all_preds`, no definition for {}",
                    self[pred]
                ))
            }
        }

        self.instance.clauses.clear();

        Ok((is_sat, info))
    }

    /// Forces a predicate to be equal to something.
    ///
    /// Does not impact `pred_to_clauses`.
    fn force_pred(&mut self, pred: PrdIdx, tterms: TTerms) -> Res<()> {
        log! { @5 "forcing (2) {}", conf.emph(& self.instance[pred].name) }
        if self.instance[pred].is_defined() {
            let mut s: Vec<u8> = Vec::new();
            tterms
                .write_smt2(&mut s, |w, pred, args| {
                    write!(w, "({}", self[pred])?;
                    for arg in args.iter() {
                        write!(w, " {}", arg)?
                    }
                    write!(w, ")")
                })
                .chain_err(|| "while dumping top terms during error on `force_pred`")?;
            bail!(
                "trying to force predicate {} twice\n{}",
                conf.sad(&self.instance[pred].name),
                String::from_utf8_lossy(&s)
            )
        } else {
            self.instance.preds[pred].set_def(tterms)?
        }
        Ok(())
    }

    /// Forces some predicate to false.
    ///
    /// Simplifies all clauses impacted.
    pub fn force_false(&mut self, pred: PrdIdx) -> Res<RedInfo> {
        self.check("before force false")?;

        let mut info = RedInfo::new();

        self.force_pred(pred, TTerms::fls())?;

        // Forget everything in `lhs`.
        debug_assert!(self.clauses_to_simplify.is_empty());
        self.instance
            .unlink_pred_lhs(pred, &mut self.clauses_to_simplify);
        info.clauses_rmed += self.clauses_to_simplify.len();
        self.instance
            .forget_clauses(&mut self.clauses_to_simplify)?;

        // Update `rhs`.
        debug_assert!(self.clauses_to_simplify.is_empty());
        self.instance
            .unlink_pred_rhs(pred, &mut self.clauses_to_simplify);
        for clause in &self.clauses_to_simplify {
            let old_rhs = self.instance.clauses[*clause].unset_rhs();
            debug_assert_eq! {
              old_rhs.map(|(p, _)| p), Some(pred)
            }
            debug_assert! {
                self.instance.clauses[*clause].preds_changed()
            }
        }

        info += self.simplify_clauses()?;

        self.check("after force true")?;

        Ok(info)
    }

    /// Forces some predicates to true.
    ///
    /// Simplifies all clauses impacted.
    pub fn force_true(&mut self, pred: PrdIdx) -> Res<RedInfo> {
        self.check("before force true")?;

        let mut info = RedInfo::new();

        self.force_pred(pred, TTerms::tru())?;

        // Forget everything in `rhs`.
        debug_assert!(self.clauses_to_simplify.is_empty());
        self.instance
            .unlink_pred_rhs(pred, &mut self.clauses_to_simplify);
        info.clauses_rmed += self.clauses_to_simplify.len();
        self.instance
            .forget_clauses(&mut self.clauses_to_simplify)?;

        // Update `rhs`.
        debug_assert!(self.clauses_to_simplify.is_empty());
        self.instance
            .unlink_pred_lhs(pred, &mut self.clauses_to_simplify);
        for clause in &self.clauses_to_simplify {
            let prev = self.instance.clauses[*clause].drop_lhs_pred(pred);
            debug_assert! { prev.is_some() }
            debug_assert! { self.instance.clauses[* clause].preds_changed() }
        }

        info += self.simplify_clauses()?;

        self.check("after force true")?;

        Ok(info)
    }

    /// Forces the lhs occurences of a predicate to be equal to something.
    ///
    /// If `pred` appears in `pred /\ apps /\ trms => rhs`, the clause will
    /// become `apps /\ pred_apps /\ trms /\ terms => rhs`.
    ///
    /// Simplifies the clauses before returning.
    ///
    /// # Usage
    ///
    /// This function can only be called if `pred` appears exactly once as a
    /// consequent, say in clause `c`, and `c`'s antecedent has no application
    /// of `pred`.
    ///
    /// Otherwise, it will return an error.
    ///
    /// # Consequences
    ///
    /// - forgets the one clause `pred` is in the rhs of
    /// - forces `pred` to be `exists qvars, pred_apps /\ terms`
    /// - simplifies all clauses impacted
    ///
    /// # Used by
    ///
    /// - `SimpleOneRhs`
    /// - `OneRhs`
    pub fn force_pred_left(
        &mut self,
        pred: PrdIdx,
        qvars: Quantfed,
        tterm_set: TTermSet,
    ) -> Res<RedInfo> {
        self.check("before `force_pred_left`")?;

        // let mut tterm_set = TTermSet::new() ;
        // tterm_set.insert_terms(terms) ;
        // for (pred, args) in pred_apps {
        //   tterm_set.insert_pred_app(pred, args) ;
        // }

        if tterm_set.is_empty() {
            return self.force_true(pred);
        }

        let mut info = RedInfo::new();

        log_debug! {
          "force pred left on {}...", conf.emph(& self.instance[pred].name)
        }

        // Forget the rhs clause.
        log_debug! {
          "forgetting rhs clause"
        }
        debug_assert! { self.clauses_to_simplify.is_empty() }
        self.instance
            .unlink_pred_rhs(pred, &mut self.clauses_to_simplify);
        let clause_to_rm = if let Some(clause) = self.clauses_to_simplify.pop() {
            // Fail if illegal.
            if self.clauses_to_simplify.pop().is_some() {
                bail!(
                    "illegal context for `force_pred_left`, \
                     {} appears in more than one rhs",
                    conf.emph(&self.instance[pred].name)
                )
            }
            if self.instance.preds_of_clause(clause).0.get(&pred).is_some() {
                bail!(
                    "illegal context for `force_pred_left`, \
                     {} appears as both lhs and rhs",
                    conf.emph(&self.instance[pred].name)
                )
            }

            clause
        } else {
            bail!(
                "illegal context for `force_pred_left`, \
                 {} appears in no rhs",
                conf.emph(&self.instance[pred].name)
            )
        };

        info.clauses_rmed += 1;
        self.instance.forget_clause(clause_to_rm)?;

        // Update lhs clauses.
        debug_assert! { self.clauses_to_simplify.is_empty() }
        self.instance
            .unlink_pred_lhs(pred, &mut self.clauses_to_simplify);
        log! { @4 |
          "updating lhs clauses ({})", self.clauses_to_simplify.len()
        }

        for clause in &self.clauses_to_simplify {
            let clause = *clause;
            log! { @4
                "- working on lhs of clause {}",
                self.instance[clause].to_string_info(self.instance.preds()).unwrap()
            }

            let argss = if let Some(argss) = self.instance.clauses[clause].drop_lhs_pred(pred) {
                argss
            } else {
                bail!(
                    "inconsistent instance state, \
                     `pred_to_clauses` and clauses out of sync"
                )
            };

            for args in argss {
                // Generate fresh variables for the clause if needed.
                let qual_map = self.instance.clauses[clause].fresh_vars_for(&qvars);

                for term in tterm_set.terms() {
                    if let Some((term, _)) = term.subst_total(&(&args, &qual_map)) {
                        self.instance.clause_add_lhs_term(clause, term);
                    } else {
                        bail!("error during total substitution in `force_pred_left`")
                    }
                }

                for (pred, app_argss) in tterm_set.preds() {
                    let pred = *pred;
                    for app_args in app_argss {
                        let mut nu_args = VarMap::with_capacity(args.len());
                        for arg in app_args.iter() {
                            if let Some((arg, _)) = arg.subst_total(&(&args, &qual_map)) {
                                nu_args.push(arg)
                            }
                        }
                        self.instance.clause_add_lhs_pred(clause, pred, nu_args)
                    }
                }
            }

            log! { @5
              "done with clause: {}",
              self.instance[clause].to_string_info(
                self.instance.preds()
              ).unwrap()
            }

            debug_assert! { self.instance[clause].preds_changed() }
        }

        // Actually force the predicate.
        self.force_pred(pred, TTerms::conj(Quant::exists(qvars), tterm_set))?;

        info += self.simplify_clauses()?;

        self.check("after `force_pred_left`")?;

        Ok(info)
    }

    /// Extends the lhs occurences of a predicate with some a term.
    ///
    /// If `pred` appears in `pred /\ apps /\ trms => rhs` where `rhs` is a
    /// predicate application, the clause will become `pred /\ apps /\ trms /\
    /// term => rhs`.
    ///
    /// Simplifies before returning.
    ///
    /// # Consequences
    ///
    /// - simplifies all clauses impacted
    ///
    /// # Used by
    ///
    /// - sub instance generation, when splitting on one clause
    pub fn extend_pred_left(
        &mut self,
        preds: &PrdHMap<crate::preproc::PredExtension>,
    ) -> Res<RedInfo> {
        self.check("before `extend_pred_left`")?;

        // let mut tterm_set = TTermSet::new() ;
        // tterm_set.insert_terms(terms) ;
        // for (pred, args) in pred_apps {
        //   tterm_set.insert_pred_app(pred, args) ;
        // }

        let mut info = RedInfo::new();

        if preds.is_empty() {
            return Ok(info);
        }

        // Update lhs clauses.
        let mut to_simplify = ClsSet::new();
        for pred in preds.keys() {
            to_simplify.extend(self.clauses_of(*pred).0.iter().cloned());
        }

        debug_assert! { self.clauses_to_simplify.is_empty() }

        'clause_iter: for clause in &to_simplify {
            let clause = *clause;
            self.clauses_to_simplify.push(clause);

            if self.clauses[clause].rhs().is_none() {
                continue 'clause_iter;
            }

            log! { @4 |
                "- working on lhs of clause {}",
                self[clause].to_string_info(self.preds()).unwrap()
            }

            for (pred, &(ref terms, ref quantified)) in preds {
                let pred = *pred;

                let argss = if let Some(argss) = self.clauses[clause].lhs_preds().get(&pred) {
                    argss.clone()
                } else {
                    continue;
                };

                for args in argss {
                    for term in terms {
                        if let Some((term, _)) = term.subst_total(&args) {
                            self.instance.clause_add_lhs_term(clause, term)
                        } else {
                            bail!("error during total substitution in `extend_pred_left`")
                        }
                    }

                    for &(ref qvars, ref term) in quantified {
                        // Generate fresh variables for the clause if needed.
                        let qual_map = self.instance.clauses[clause].fresh_vars_for(qvars);

                        if let Some((term, _)) = term.subst_total(&(&args, &qual_map)) {
                            self.instance.clause_add_lhs_term(clause, term)
                        } else {
                            bail!("error during total substitution in `extend_pred_left`")
                        }
                    }
                }
            }

            log! { @4
              "done with clause: {}",
              self[clause].to_string_info(
                self.preds()
              ).unwrap()
            }
        }

        info += self.simplify_clauses()?;

        self.check("after `extend_pred_left`")?;

        Ok(info)
    }

    /// Forces all lhs occurrences of a predicate to be replaced by a DNF.
    ///
    /// - only legal if `pred` does not appear in any rhs
    /// - in general, will create new clauses
    /// - if `def` is empty, equivalent to `force_false`
    /// - simplifies all clauses impacted
    /// - does not call `force_trivial`
    ///
    /// Simplifies before returning.
    ///
    /// Used by `GraphRed`.
    pub fn force_dnf_left(&mut self, pred: PrdIdx, def: Dnf) -> Res<RedInfo> {
        let def: Vec<_> = def
            .into_iter()
            .map(|(qvars, conj)| (Quant::exists(qvars), conj))
            .collect();

        if def.is_empty() {
            return self.force_false(pred);
        }

        let mut info = RedInfo::new();

        self.check("before `force_dnf_left`")?;

        log! { @6 |
            "force_dnf_left {} ({} defs)", self[pred], def.len() ;
            "unlinking rhs"
        }

        // Make sure there's no rhs clause for `pred`.
        debug_assert! { self.clauses_to_simplify.is_empty() }
        self.instance
            .unlink_pred_rhs(pred, &mut self.clauses_to_simplify);
        if !self.clauses_to_simplify.is_empty() {
            bail!(
                "can't force dnf {}, it appears in some rhs",
                self.instance[pred]
            )
        }

        log! { @6 | "unlinking lhs" }

        // Update lhs clauses.
        debug_assert! { self.clauses_to_simplify.is_empty() }
        self.instance
            .unlink_pred_lhs(pred, &mut self.clauses_to_simplify);
        // Rev-sorting as we're going to swap remove stuff.
        self.clauses_to_simplify
            .sort_unstable_by(|c_1, c_2| c_2.cmp(c_1));

        let mut nu_clauses = vec![];

        for clause in self.clauses_to_simplify.drain(0..) {
            info.clauses_rmed += 1;

            log! { @7 | "working on #{}", clause }

            let pred_argss: Vec<VarTerms> =
                if let Some(argss) = self.instance.clauses[clause].drop_lhs_pred(pred) {
                    argss.iter().cloned().collect()
                } else {
                    bail!("inconsistent instance state")
                };

            log! { @7 | "  {} applications", pred_argss.len() }

            // This is why we rev-sorted:
            let clause = self.instance.forget_clause(clause)?;

            // Iterator over all combinations of elements from `def` with len
            // `pred_argss`.
            let mut all_combinations = CombinationIter::new(def.iter(), pred_argss.len())?;

            // Go over all the combinations.
            while let Some(combination) = all_combinations.next_combination() {
                debug_assert_eq! { combination.len(), pred_argss.len() }

                let mut clause = clause.clone();

                // Apply substitution and insert into the new clause.
                for ((quant, def), pred_args) in combination.iter().zip(pred_argss.iter()) {
                    let quant_map = clause.nu_fresh_vars_for(quant);

                    for term in def.terms() {
                        if let Some((term, _)) = term.subst_total(&(pred_args, &quant_map)) {
                            clause.insert_term(term);
                        } else {
                            bail!("unexpected total substitution failure on term {}", term)
                        }
                    }

                    for (pred, argss) in def.preds() {
                        let pred = *pred;
                        for args in argss {
                            let mut nu_args = VarMap::with_capacity(args.len());
                            for arg in args.iter() {
                                if let Some((arg, _)) = arg.subst_total(&(pred_args, &quant_map)) {
                                    nu_args.push(arg)
                                } else {
                                    bail!(
                                        "unexpected total substitution failure on arg {} \
                                         of ({} {})",
                                        arg,
                                        self.instance[pred],
                                        args
                                    )
                                }
                            }
                            clause.insert_pred_app(pred, nu_args.into());
                        }
                    }
                }

                nu_clauses.push(clause)
            }
        }

        // Actually force the predicate.
        self.force_pred(pred, TTerms::dnf(def))?;

        for clause in nu_clauses {
            let is_new = self.instance.push_clause_unchecked(clause);
            if is_new {
                info.clauses_added += 1;
            }
        }

        info += self.simplify_all()?;

        self.check("after `force_dnf_left`")?;

        Ok(info)
    }

    /// Retrieves the only clause a predicate appears in.
    ///
    /// Only legal if
    ///
    /// - `self.clauses_to_simplify.is_empty()`
    /// - `pred` appears as a rhs in a single clause, and does not appear as a
    ///   lhs in said clause.
    fn rm_only_lhs_clause_of(&mut self, pred: PrdIdx) -> Res<ClsIdx> {
        debug_assert! { self.clauses_to_simplify.is_empty() }
        self.instance
            .unlink_pred_lhs(pred, &mut self.clauses_to_simplify);
        if let Some(clause) = self.clauses_to_simplify.pop() {
            if self.clauses_to_simplify.pop().is_some() {
                bail!(
                    "{} appears in more than one lhs",
                    conf.emph(&self.instance[pred].name)
                )
            }
            if self.instance.preds_of_clause(clause).1 == Some(pred) {
                bail!(
                    "{} appears as both lhs and rhs",
                    conf.emph(&self.instance[pred].name)
                )
            }
            Ok(clause)
        } else {
            bail!("{} appears in no lhs", conf.emph(&self.instance[pred].name))
        }
    }

    /// Forces the rhs occurrences of a predicate to be equal to something.
    ///
    /// If `pred` appears in `args /\ trms => pred`, the clause will become
    /// `apps /\ pred_apps /\ trms /\ terms => pred_app`.
    ///
    /// Quantified variables are understood as universally quantified.
    ///
    /// Simplifies before returning.
    ///
    /// # Usage
    ///
    /// This function can only be called if `pred` appears exactly once as an
    /// antecedent, say in clause `c`, and `c`'s consequent is not an application
    /// of `pred`.
    ///
    /// Otherwise, it will return an error.
    ///
    /// # Consequences
    ///
    /// - forgets the one clause `pred` is in the lhs of
    /// - forces `pred` to be `forall qvars, pred_app \/ (not /\ pred_apps) \/
    ///   (not /\ terms)`
    ///
    /// # Used by
    ///
    /// - `SimpleOneLhs`
    pub fn force_pred_right(
        &mut self,
        pred: PrdIdx,
        qvars: Quantfed,
        pred_app: Option<(PrdIdx, VarTerms)>,
        negated: TTermSet,
    ) -> Res<RedInfo> {
        self.check("before `force_pred_right`")?;

        let mut info = RedInfo::new();

        let quant = Quant::forall(qvars);

        log! { @debug |
            "force pred right on {}...", conf.emph(& self.instance[pred].name)
        }

        // Update rhs clauses.
        debug_assert! { self.clauses_to_simplify.is_empty() }
        self.instance
            .unlink_pred_rhs(pred, &mut self.clauses_to_simplify);

        'clause_iter: for clause in &self.clauses_to_simplify {
            let clause = *clause;
            log! { @4 | "working on clause #{}", clause }
            log! { @4
                "{}", self.instance[clause].to_string_info(self.instance.preds()).unwrap()
            }

            let rhs = self.instance.clauses[clause].unset_rhs();

            if let Some((prd, subst)) = rhs {
                let qual_map = self.instance.clauses[clause].nu_fresh_vars_for(&quant);

                if pred == prd {
                    log! { @5 "generating new rhs" }

                    // New rhs.
                    if let Some(&(prd, ref args)) = pred_app.as_ref() {
                        let mut nu_args = VarMap::with_capacity(args.len());

                        for arg in args.iter() {
                            if let Some((nu_arg, _)) = arg.subst_total(&(&subst, &qual_map)) {
                                nu_args.push(nu_arg)
                            } else {
                                bail!("unexpected failure during total substitution")
                            }
                        }

                        self.instance.clause_force_rhs(clause, prd, nu_args)?
                    }
                    // No `else`, clause's rhs is already `None`.

                    log! { @5 | "generating new lhs pred apps" }

                    // New lhs predicate applications.
                    for (pred, argss) in negated.preds() {
                        let pred = *pred;
                        for args in argss {
                            let mut nu_args = VarMap::with_capacity(args.len());
                            for arg in args.iter() {
                                if let Some((nu_arg, _)) = arg.subst_total(&(&subst, &qual_map)) {
                                    nu_args.push(nu_arg)
                                } else {
                                    bail!("unexpected failure during total substitution")
                                }
                            }
                            self.instance.clause_add_lhs_pred(clause, pred, nu_args)
                        }
                    }

                    log! { @5 | "generating new lhs terms" }

                    // New lhs terms.
                    for term in negated.terms() {
                        if let Some((term, _)) = term.subst_total(&(&subst, &qual_map)) {
                            self.instance.clause_add_lhs_term(clause, term);
                        }
                    }

                    // Explicitely continueing, otherwise the factored error message
                    // below will fire.
                    continue 'clause_iter;
                }
            }

            bail!(
                "inconsistent instance state, \
                 `pred_to_clauses` and clauses out of sync"
            )
        }

        info += self.simplify_clauses()?;

        let clause_to_rm = self
            .rm_only_lhs_clause_of(pred)
            .chain_err(|| "illegal context for `force_pred_right`")?;

        // Actually force the predicate.
        self.force_pred(
            pred,
            TTerms::disj_of_pos_neg(quant, pred_app.map(|(pred, args)| (pred, args)), negated),
        )?;

        info.clauses_rmed += 1;
        self.instance.forget_clause(clause_to_rm)?;

        self.check("after `force_pred_right`")?;

        Ok(info)
    }

    /// Unrolls some predicates.
    ///
    /// Simplifies before returning.
    ///
    /// For each clause `(pred args) /\ lhs => rhs`, adds `terms /\ lhs => rhs` for terms in
    /// `terms[p]`.
    ///
    /// Only unrolls negative clauses where `(pred args)` is not the only application.
    pub fn unroll(&mut self, pred: PrdIdx, terms: &[(Option<Quant>, TTermSet)]) -> Res<RedInfo> {
        let mut info = RedInfo::new();
        let mut to_add = Vec::with_capacity(17);
        let fls = term::fls();

        log! { @debug |
            "{} appears in {} clause's lhs",
            conf.emph(& self[pred].name),
            self.instance.pred_to_clauses[pred].0.len()
        }

        for clause in &self.instance.pred_to_clauses[pred].0 {
            let clause = &self.instance[*clause];

            // Negative clause and `pred` is the only application.
            if clause.rhs().is_none() && clause.lhs_preds().len() == 1 {
                continue;
            }

            let argss = if let Some(argss) = clause.lhs_preds().get(&pred) {
                argss
            } else {
                bail!("inconsistent instance state, `pred_to_clauses` out of sync")
            };

            for &(ref quant, ref tterms) in terms {
                let mut nu_clause = clause.clone_except_lhs_of(pred, "unrolling");
                let qual_map = nu_clause.nu_fresh_vars_for(quant);

                for args in argss {
                    conf.check_timeout()?;
                    if !tterms.preds().is_empty() {
                        bail!("trying to unroll predicate by another predicate")
                    }
                    for term in tterms.terms() {
                        if let Some((nu_term, _)) = term.subst_total(&(&args, &qual_map)) {
                            nu_clause.insert_term(nu_term);
                        } else {
                            bail!("unexpected failure during total substitution")
                        }
                    }
                }

                log! { @4 |
                    "pre-simplification {}",
                    nu_clause.to_string_info(& self.preds).unwrap()
                }

                self.simplifier
                    .clause_propagate(&mut nu_clause, self.instance.preds())?;

                if !nu_clause.lhs_terms().contains(&fls) {
                    log! { @4
                        "staging clause {}",
                        nu_clause.to_string_info(& self.preds).unwrap()
                    }
                    // nu_clause.from_unrolling = true ;
                    to_add.push(nu_clause)
                }
            }
        }

        log! { @debug "adding {} clauses", to_add.len() }

        for clause in to_add {
            if let Some(index) = self.instance.push_clause(clause)? {
                let mut simplinfo = self.simplify_clause(index)?;
                if simplinfo.clauses_rmed > 0 {
                    simplinfo.clauses_rmed -= 1
                } else {
                    simplinfo.clauses_added += 1
                }
                info += simplinfo
            }
        }

        self.check("after unroll")?;

        Ok(info)
    }

    /// Reverse unrolls some predicates.
    ///
    /// Simplifies before returning.
    ///
    /// For each clause `lhs => (pred args)`, adds `(not terms) /\ lhs => false` for terms in
    /// `terms[p]`.
    ///
    /// Only unrolls clauses which have at least one lhs predicate application.
    pub fn reverse_unroll(
        &mut self,
        pred: PrdIdx,
        terms: &[(Option<Quant>, TermSet)],
    ) -> Res<RedInfo> {
        let mut info = RedInfo::new();
        let mut to_add = Vec::with_capacity(17);
        let fls = term::fls();

        for clause in &self.instance.pred_to_clauses[pred].1 {
            let clause = &self.instance[*clause];

            // Negative clause and `pred` is the only application.
            if clause.lhs_preds().is_empty() {
                continue;
            }

            let args = if let Some((p, args)) = clause.rhs() {
                debug_assert_eq! { p, pred }
                args
            } else {
                bail!("inconsistent instance state")
            };

            for &(ref quant, ref terms) in terms {
                let mut nu_clause = clause.clone_with_rhs(None, "r_unroll");
                let qual_map = nu_clause.nu_fresh_vars_for(quant);

                for term in terms {
                    conf.check_timeout()?;
                    if let Some((nu_term, _)) = term.subst_total(&(&args, &qual_map)) {
                        nu_clause.insert_term(nu_term);
                    } else {
                        bail!("unexpected failure during total substitution")
                    }
                }

                self.simplifier
                    .clause_propagate(&mut nu_clause, self.instance.preds())?;

                if !nu_clause.lhs_terms().contains(&fls) {
                    // nu_clause.from_unrolling = true ;
                    to_add.push(nu_clause)
                }
            }
        }

        for clause in to_add {
            log! { @4
                "adding clause {}", clause.to_string_info(& self.preds).unwrap()
            }
            if let Some(index) = self.instance.push_clause(clause)? {
                let mut simplinfo = self.simplify_clause(index)?;
                if simplinfo.clauses_rmed > 0 {
                    simplinfo.clauses_rmed -= 1
                } else {
                    simplinfo.clauses_added += 1
                }
                info += simplinfo
            }
        }

        self.check("after runroll")?;

        Ok(info)
    }

    /// Removes some arguments for a predicate.
    ///
    /// Returns `true` if something happened.
    pub fn rm_args_of(&mut self, pred: PrdIdx, to_keep: &VarSet) -> Res<usize> {
        macro_rules! rm_args {
            (from $args:expr, keep nothing, swap $nu_args:expr) => {{
                debug_assert!($nu_args.is_empty());
                ::std::mem::swap($nu_args, $args);
                $nu_args.clear();
            }};
            (from $args:expr, keep $to_keep:expr, to $nu_args:expr) => {{
                debug_assert!($nu_args.is_empty());
                for (var, arg) in $args.index_iter() {
                    if $to_keep.contains(&var) {
                        $nu_args.push(arg.clone())
                    }
                }
            }};
        }

        log! { @4 |
            "working on {} ({}/{})", self[pred], to_keep.len(), self[pred].sig.len()
        }

        let mut rmed = 0;
        let mut var_map = VarMap::with_capacity(to_keep.len());
        let mut nu_sig = VarMap::with_capacity(to_keep.len());

        for (var, typ) in self[pred].sig.index_iter() {
            if to_keep.contains(&var) {
                // Re-route current **new** var to the original variable `var` is
                // pointing to.
                var_map.push(self[pred].original_sig_map()[var]);
                nu_sig.push(typ.clone())
            } else {
                rmed += 1
            }
        }

        // Update `preds` with the new signature.
        self.instance.preds[pred].set_sig(nu_sig, var_map);

        // Propagate removal to clauses.
        let (ref lhs, ref rhs) = self.instance.pred_to_clauses[pred];

        for clause in lhs {
            self.instance.clauses[*clause].lhs_map_args_of(pred, |args| {
                let mut nu_args = VarMap::with_capacity(args.len() - to_keep.len());
                rm_args! { from args, keep to_keep, to nu_args }
                nu_args.into()
            });

            conf.check_timeout()?
        }

        for clause in rhs {
            debug_assert! { self.instance.clauses[* clause].rhs().is_some() }
            self.instance.clauses[*clause].rhs_map_args(|p, args| {
                debug_assert_eq!(pred, p);
                let mut nu_args = VarMap::with_capacity(args.len() - to_keep.len());
                rm_args! { from args, keep to_keep, to nu_args }
                (p, nu_args.into())
            });
            conf.check_timeout()?
        }

        Ok(rmed)
    }

    /// Removes all predicate arguments not in `to_keep`.
    ///
    /// Simplifies before returning.
    ///
    /// Removes useless arguments in the clauses. Updates the signature of the predicates in the
    /// instance.
    pub fn rm_args(&mut self, to_keep: PrdHMap<VarSet>) -> Res<RedInfo> {
        if_log! { @debug
            log! { @debug | "  rm_args ({})", to_keep.len() }
            log! { @debug | "  to keep {{" }
            for (pred, vars) in to_keep.iter() {
                let mut s = String::new() ;
                for var in vars {
                    s.push_str(" ") ;
                    s.push_str( & var.default_str() )
                }
                log! { @debug | "    {}:{}", self[* pred], s }
            }
            log! { @debug | "  }}" }
        }

        self.check("rm_args")?;

        let mut info = RedInfo::new();

        // Remove args from forced predicates.
        for pred in &mut self.instance.preds {
            if let Some(mut tterms) = pred.unset_def() {
                tterms.remove_vars(&to_keep);
                pred.set_def(tterms)?
            }
        }

        let mut did_something = false;

        // Remove args from applications in clauses.
        for (pred, to_keep) in to_keep {
            debug_assert!(to_keep.len() <= self[pred].sig.len());
            log! { @4 | "- {}", self[pred] }
            if to_keep.len() == self[pred].sig.len() {
                log! { @4 | "skipping" }
                continue;
            }

            did_something = true;

            let rmed = self.rm_args_of(pred, &to_keep)?;
            info.args_rmed += rmed
        }

        if !did_something {
            return Ok(info);
        }

        // Simplify the clauses we just updated.
        debug_assert! { self.clauses_to_simplify.is_empty() }

        info += self.simplify_all()?;

        self.check("after `rm_args`")?;

        Ok(info)
    }

    /// Removes all clauses in which `pred` is in the rhs.
    ///
    /// Does not run simplifications.
    pub fn rm_rhs_clauses_of(&mut self, pred: PrdIdx) -> Res<RedInfo> {
        debug_assert! { self.clauses_to_simplify.is_empty() }
        let mut info = RedInfo::new();
        let to_rm = self.instance.pred_to_clauses[pred].1.clone();
        // self.instance.unlink_pred_rhs(pred, & mut self.clauses_to_simplify) ;
        info.clauses_rmed += to_rm.len();
        self.instance
            .forget_clauses(&mut to_rm.into_iter().collect())?;
        Ok(info)
    }

    /// Checks whether some partial definitions for the predicate constitute a model.
    pub fn check_pred_partial_defs<'b, I>(&mut self, defs: I) -> Res<bool>
    where
        I: Iterator<Item = (PrdIdx, &'b Vec<(Quantfed, Term)>)> + Clone,
    {
        self.solver.comment("checking partial definitions")?;

        let (instance, solver) = (&self.instance, &mut self.solver);
        for (_idx, clause) in instance.clauses().index_iter() {
            log! { @5 "checking clause #{}", _idx }
            solver.comment_args(format_args! { "checking clause #{}", _idx })?;

            for (pred, def) in defs.clone() {
                write!(solver, "(define-fun {} (", instance[pred])?;
                for (var, typ) in instance[pred].sig().index_iter() {
                    write!(solver, " ({} {})", var.default_str(), typ)?
                }
                writeln!(solver, " ) Bool")?;

                if def.len() > 1 {
                    write!(solver, "  (and ")?
                }

                for (q, t) in def {
                    write!(solver, " ")?;
                    if !q.is_empty() {
                        write!(solver, "(forall (")?;
                        for (var, typ) in q {
                            write!(solver, " ({} {})", var.default_str(), typ)?
                        }
                        write!(solver, " ) ")?
                    }

                    t.write(solver, |w, var| write!(w, "{}", var.default_str()))?;

                    if !q.is_empty() {
                        write!(solver, ")")?
                    }
                }

                if def.len() > 1 {
                    write!(solver, "  )")?
                }

                writeln!(solver, ")")?
            }

            clause.declare(solver)?;
            let actlit = solver.get_actlit()?;
            write!(solver, "(assert (=> ")?;
            actlit.expr_to_smt2(solver, ())?;
            write!(solver, " (not")?;
            clause.qf_write(
                solver,
                |w, v| write!(w, "{}", v.idx.default_str()),
                |w, pred, args, bindings| {
                    if args.is_empty() {
                        write!(w, "{}", instance[pred])
                    } else {
                        write!(w, "({}", instance[pred])?;
                        for arg in args.iter() {
                            write!(w, " ")?;
                            arg.write_with(w, |w, v| write!(w, "{}", v.default_str()), bindings)?
                        }
                        write!(w, ")")
                    }
                },
                2,
            )?;
            writeln!(solver, ")))")?;

            let sat = solver.check_sat_act_or_unk(&[actlit])?;

            if sat.is_none() {
                log! { @4 "got unknown while checking partial definitions" }
            }

            crate::smt::preproc_reset(solver)?;

            if sat != Some(false) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Checks the predicates' definition verify the current instance.
    ///
    /// Returns `true` if they work (sat).
    ///
    /// # Errors if
    ///
    /// - some predicates are not defined
    pub fn check_pred_defs(&mut self) -> Res<bool> {
        if self.active_pred_count() > 0 {
            bail!("can't check predicate definitions, some predicates are not defined")
        }

        let _ = self.simplify_all()?;

        let set = PrdSet::new();
        self.instance.finalize()?;
        for pred in self.instance.sorted_forced_terms() {
            let pred = *pred;
            let pred_info = &self.instance[pred];
            log! { @4 | "definining {}", pred_info }

            let sig: Vec<_> = pred_info
                .sig
                .index_iter()
                .map(|(var, typ)| (var.default_str(), typ.get()))
                .collect();

            if let Some(ref def) = pred_info.def() {
                self.solver.define_fun_with(
                    &self.instance[pred].name,
                    &sig,
                    &typ::RTyp::Bool,
                    def,
                    &(&set, &set, &self.instance.preds),
                )?
            } else {
                bail!(
                    "can't check predicate definitions, predicate {} is not defined",
                    conf.bad(&pred_info.name)
                )
            }
        }

        self.solver.comment("checking side clauses")?;

        for clause in &self.instance.side_clauses {
            self.solver.push(1)?;
            for info in clause.vars() {
                if info.active {
                    self.solver
                        .declare_const(&info.idx.default_str(), info.typ.get())?
                }
            }
            self.solver
                .assert_with(clause, &(true, &set, &set, &self.instance.preds))?;

            let sat = check_sat!(self);

            self.solver.pop(1)?;
            if !sat {
                return Ok(false);
            }
        }

        self.solver.comment("checking clauses")?;

        for clause in &self.instance.clauses {
            self.solver.push(1)?;
            for info in clause.vars() {
                if info.active {
                    self.solver
                        .declare_const(&info.idx.default_str(), info.typ.get())?
                }
            }
            self.solver
                .assert_with(clause, &(false, &set, &set, &self.instance.preds))?;

            let sat = check_sat!(self);
            self.solver.pop(1)?;
            if sat {
                return Ok(false);
            }
        }

        self.reset_solver()?;

        Ok(true)
    }
}

impl<'a> ::std::ops::Deref for PreInstance<'a> {
    type Target = Instance;
    fn deref(&self) -> &Instance {
        self.instance
    }
}
impl<'a> ::std::ops::DerefMut for PreInstance<'a> {
    fn deref_mut(&mut self) -> &mut Instance {
        self.instance
    }
}

/// Simplifies clauses.
///
/// The goal of this type is to avoid reallocation and compartment the clause
/// simplification process.
pub struct ClauseSimplifier {
    /// Factored variable substitution.
    subst: VarHMap<Term>,
    /// Terms to add to the clause.
    terms_to_add: Vec<Term>,
    /// Variables that can't be inserted during the substitution.
    var_set: VarSet,
}
impl ClauseSimplifier {
    /// Constructor.
    pub fn new() -> Self {
        ClauseSimplifier {
            subst: VarHMap::with_capacity(20),
            terms_to_add: Vec::with_capacity(29),
            var_set: VarSet::with_capacity(27),
        }
    }

    /// Propagates booleans at top level.
    ///
    /// Returns `None` iff the clause is trivial, otherwise returns `true` is
    /// something changed.
    pub fn clause_propagate_bool(&mut self, clause: &mut Clause) -> Res<Option<bool>> {
        debug_assert! { self.terms_to_add.is_empty() }
        debug_assert! { self.subst.is_empty() }
        debug_assert! { self.var_set.is_empty() }

        let mut trivial = false;
        let mut changed = false;

        // Propagate all top-level (negated) boolean variables.
        for term in clause.lhs_terms() {
            let plain_term = term.rm_neg();
            let plain_term = if let Some(plain) = plain_term.as_ref() {
                plain
            } else {
                term
            };
            if let Some(idx) = plain_term.var_idx() {
                let (value, b_value) = if plain_term == term {
                    (term::tru(), true)
                } else {
                    (term::fls(), false)
                };
                // println!("term: {}", term) ;
                // println!("      {}", clause[idx].name) ;
                // println!("      {}", value) ;
                let prev = self.subst.insert(idx, value);
                if let Some(prev) = prev {
                    match prev.bool() {
                        Some(prev) if b_value != prev => {
                            trivial = true;
                            break;
                        }
                        _ => unreachable!(
                            "problem in bool var propagation: value is {}, prev is {}",
                            b_value, prev
                        ),
                    }
                }
            }
        }

        if trivial {
            // println!("trivializing clause") ;
            clause.insert_term(term::fls());
            self.subst.clear();
            return Ok(None);
        } else if !self.subst.is_empty() {
            changed = clause.subst(&self.subst) || changed;
            for (var, _) in self.subst.drain() {
                clause.deactivate(var)?
            }
        }

        Ok(Some(changed))
    }

    /// Works on an equality.
    ///
    /// Returns `true` if the equality was not registered as a substitution
    /// (`skip`).
    fn work_on_eq(&mut self, clause: &mut Clause, eq: &Term) -> Res<bool> {
        macro_rules! skip {
            () => {{
                log! { @5 | "skipping" }
                return Ok(true);
            }};
        }

        let args = if let Some(args) = eq.eq_inspect() {
            args
        } else {
            bail!("illegal call to `work_on_eq` on {}", eq)
        };

        if args.len() != 2 {
            skip!()
        }

        match eq.as_subst() {
            Some((var, term)) => {
                if self.subst.get(&var).is_some() {
                    skip!()
                }

                let vars = term::vars(&term);
                if vars.contains(&var)
                    || self.var_set.contains(&var)
                    || term::vars(&term)
                        .into_iter()
                        .any(|v| v == var || self.subst.get(&v).is_some())
                {
                    skip!()
                }

                log! { @4 "{} -> {}", var.default_str(), term }

                let prev = self.subst.insert(var, term);
                debug_assert_eq! { prev, None }

                self.var_set.extend(vars)
            }

            // Two terms.
            None => {
                debug_assert_eq! { args[1].typ(), args[0].typ() }
                let nu_term = if args[0].typ().is_bool() {
                    let not_lhs = term::not(args[0].clone());
                    let not_rhs = term::not(args[1].clone());
                    if clause.lhs_terms().contains(&args[0])
                        || self.terms_to_add.iter().any(|t| t == &args[0])
                    {
                        args[1].clone()
                    } else if clause.lhs_terms().contains(&args[1])
                        || self.terms_to_add.iter().any(|t| t == &args[1])
                    {
                        args[0].clone()
                    } else if clause.lhs_terms().contains(&not_lhs)
                        || self.terms_to_add.iter().any(|t| t == &not_lhs)
                    {
                        not_rhs
                    } else if clause.lhs_terms().contains(&not_rhs)
                        || self.terms_to_add.iter().any(|t| t == &not_rhs)
                    {
                        not_lhs
                    } else {
                        skip!()
                    }
                } else {
                    skip!()
                };

                log! { @5 | "{} -> {}", eq, nu_term }

                clause.insert_term(nu_term);
            }
        }

        Ok(false)
    }

    /// Propagates equalities in a clause.
    pub fn clause_propagate(&mut self, clause: &mut Clause, _preds: &Preds) -> Res<()> {
        debug_assert! { self.terms_to_add.is_empty() }
        debug_assert! { self.subst.is_empty() }
        debug_assert! { self.var_set.is_empty() }

        let mut eq = None;

        log! { @6 "working on\n{}", clause.to_string_info( _preds ).unwrap() }

        let mut changed = false;

        macro_rules! bool_prop {
            () => {
                match self.clause_propagate_bool(clause)? {
                    // Clause is trivial.
                    None => return Ok(()),
                    Some(true) => changed = true,
                    Some(false) => (),
                }
            };
        }

        bool_prop!();

        'outter: loop {
            debug_assert_eq! { eq, None }
            for term in clause.lhs_terms() {
                if let Some((Op::Eql, _)) = term.app_inspect() {
                    eq = Some(term.clone())
                }
            }

            if let Some(eq) = ::std::mem::replace(&mut eq, None) {
                log! { @4 | "{}", eq }

                let was_there = clause.rm_term(&eq);
                debug_assert! { was_there }

                let skip = self.work_on_eq(clause, &eq)?;

                if skip {
                    self.terms_to_add.push(eq)
                }
            } else {
                if !self.subst.is_empty() || !self.terms_to_add.is_empty() {
                    for term in self.terms_to_add.drain(0..) {
                        clause.insert_term(term);
                    }
                    changed = clause.subst(&self.subst) || changed;
                    log! { @5 "yielding {}", clause.to_string_info( _preds ).unwrap() }
                    for (var, _) in self.subst.drain() {
                        clause.deactivate(var)?
                    }
                    self.var_set.clear()
                }

                bool_prop!();

                if !changed {
                    break 'outter;
                } else {
                    changed = false;
                }
            }
        }

        Ok(())
    }
}

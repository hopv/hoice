//! Handles counterexample bias for the teacher.

use crate::{
    common::{smt::DisjArgs, *},
    data::Data,
    var_to::{
        terms::{VarTermsMap, VarTermsSet},
        vals::VarValsSet,
    },
};

/// Solver.
type Slvr = Solver<smt::FullParser>;

///
#[derive(Default, Debug)]
pub struct CexBias {
    /// Activation literals for the predicate applications in the lhs of a
    /// clause.
    lhs_actlits: PrdHMap<VarTermsMap<Actlit>>,
    /// LHS predicate applications that can't be forced positive.
    lhs_non_pos: PrdHMap<VarTermsSet>,
}

impl CexBias {
    /// Constructor.
    pub fn new() -> Self {
        CexBias {
            lhs_actlits: PrdHMap::new(),
            lhs_non_pos: PrdHMap::new(),
        }
    }

    /// Generates activation literals forcing a bias in the clause.
    ///
    /// Assumes all variables are already declared.
    pub fn apply(
        &mut self,
        _profiler: &Profiler,
        solver: &mut Slvr,
        clause: ClsIdx,
        instance: &Instance,
        data: &Data,
        bias_only: bool,
    ) -> Res<Vec<(Actlit, Bias)>> {
        if !conf.teacher.bias_cexs {
            return Ok(vec![]);
        }

        macro_rules! clause {
            () => {
                instance[clause]
            };
        }

        self.lhs_actlits.clear();
        self.lhs_non_pos.clear();

        self.get_lhs_actlits(solver, clause, instance, data)?;

        let rhs_actlit = self.get_rhs_actlit(solver, clause, instance, data)?;

        // Let's do this.
        let mut actlits = vec![];

        // If there's any positive samples at all, we can do something for the rhs
        // (if any).
        if !self.lhs_actlits.is_empty()
            && clause!().rhs().is_some()
            && (
                // Skip if we're only generating biased check-sat and there are
                // applications without any positive data.
                !bias_only || self.lhs_non_pos.is_empty()
            )
        {
            self.bias_left(_profiler, solver, &mut actlits, bias_only)?
        }

        // If there's no rhs or it has negative samples we can do something for the
        // lhs.
        if clause!().rhs().is_none() || rhs_actlit.is_some() {
            if self.lhs_non_pos.is_empty() {
                self.exhaustive_bias_right(_profiler, solver, &mut actlits, instance, &rhs_actlit)?
            } else if !bias_only
                || self.lhs_non_pos.iter().fold(
                    // Skip if only generating biased checksat and there's more than one
                    // application without positive data.
                    0,
                    |acc, (_, argss)| acc + argss.len(),
                ) == 1
            {
                self.partial_bias_right(_profiler, solver, &mut actlits, &rhs_actlit)?
            }
        }

        Ok(actlits)
    }

    /// Generates an actlit that forces the RHS of a clause to be a negative
    /// sample.
    ///
    /// Returns `None` if either
    /// - there's no RHS,
    /// - there's no negative data for the RHS,
    /// - the negative data for the RHS can't be activated.
    fn get_rhs_actlit(
        &mut self,
        solver: &mut Slvr,
        clause: ClsIdx,
        instance: &Instance,
        data: &Data,
    ) -> Res<Option<Actlit>> {
        log! { @4 "working on rhs" }

        let res = if let Some((pred, args)) = instance[clause].rhs() {
            log! { @5 "-> {}", instance[pred] }
            if data.neg[pred].is_empty() {
                // No negative data...
                log! { @5 "   no negative data" }
                None
            } else {
                log! { @5 "   has negative data" }
                // Negative data, generate an actlit for that.
                solver.comment(&format!(
                    "activating negative samples for {}",
                    instance[pred]
                ))?;

                if let Some(actlit) = get_actlit(solver, args, &data.neg[pred])? {
                    Some(actlit)
                } else {
                    None
                }
            }
        } else {
            log! { @5 "-> None" }
            None
        };

        Ok(res)
    }

    ///
    fn get_lhs_actlits(
        &mut self,
        solver: &mut Slvr,
        clause: ClsIdx,
        instance: &Instance,
        data: &Data,
    ) -> Res<()> {
        macro_rules! clause {
            () => {
                instance[clause]
            };
        }

        self.lhs_actlits.clear();
        self.lhs_non_pos.clear();

        log! { @4 "creating lhs actlits" }

        let mut cant_pos_argss = VarTermsSet::new();

        // Create actlits for lhs applications when possible.
        for (pred, argss) in clause!().lhs_preds() {
            let pred = *pred;
            log! { @5 "for {} ({})", instance[pred], argss.len() }

            if data.pos[pred].is_empty() {
                log! { @5 "  no positive data" }
                self.lhs_non_pos.insert(pred, argss.clone());
                continue;
            }

            solver.comment(&format!(
                "activating positive samples for {} ({} applications)",
                instance[pred],
                argss.len()
            ))?;

            let mut argss_map = VarTermsMap::with_capacity(argss.len());

            debug_assert! { cant_pos_argss.is_empty() }

            for args in argss {
                log! { @6 "generating actlit for {}", args }

                if let Some(actlit) = get_actlit(solver, args, &data.pos[pred])? {
                    let prev = argss_map.insert(args.clone(), actlit);
                    debug_assert! { prev.is_none() }
                } else {
                    let is_new = cant_pos_argss.insert(args.clone());
                    debug_assert! { is_new }
                }
            }

            if !cant_pos_argss.is_empty() {
                let prev = self.lhs_non_pos.insert(pred, cant_pos_argss.drain().into());
                debug_assert! { prev.is_none() }
            }

            if !argss_map.is_empty() {
                let prev = self.lhs_actlits.insert(pred, argss_map);
                debug_assert! { prev.is_none() }
            }
        }

        Ok(())
    }

    /// Generates a bias-left actlit.
    fn bias_left(
        &mut self,
        _profiler: &Profiler,
        solver: &mut Slvr,
        actlits: &mut Vec<(Actlit, Bias)>,
        bias_only: bool,
    ) -> Res<()> {
        solver.comment("activating all lhs positive samples")?;
        let actlit = solver.get_actlit()?;
        for (_, map) in &self.lhs_actlits {
            for (_, pos_actlit) in map {
                solver.assert_act(&actlit, pos_actlit)?
            }
        }

        let bias = if self.lhs_non_pos.is_empty() {
            log! { @4 "total bias left" }
            profile! { |_profiler| "bias: total left" => add 1 }
            // If all lhs predicates have positive sample then this actlit yields a
            // positive example for the rhs.
            Bias::Lft
        } else {
            log! { @4 "partial bias left" }
            profile! { |_profiler| "bias: partial left" => add 1 }
            // Otherwise this will generate a constraint.
            Bias::Non
        };

        if !bias.is_none() || !bias_only {
            actlits.push((actlit, bias))
        } else {
            solver.de_actlit(actlit)?
        }

        Ok(())
    }

    /// Generates a partial bias-right actlit.
    fn partial_bias_right(
        &mut self,
        _profiler: &Profiler,
        solver: &mut Slvr,
        actlits: &mut Vec<(Actlit, Bias)>,
        rhs_actlit: &Option<Actlit>,
    ) -> Res<()> {
        // There's some lhs applications with no negative data. Activate
        // everything we can.
        let this_actlit = solver.get_actlit()?;

        // Force rhs false if any.
        if let Some(rhs_actlit) = rhs_actlit.as_ref() {
            solver.assert_act(&this_actlit, rhs_actlit)?
        }

        // Activate everything we can.
        for (_, map) in &self.lhs_actlits {
            for (_, actlit) in map {
                solver.assert_act(&this_actlit, actlit)?
            }
        }

        // Now the question is what kind of bias this corresponds to.

        let mut iter = self.lhs_non_pos.drain();
        let (this_pred, argss) = iter
            .next()
            .expect("next on non-empty iterator cannot yield none");

        let mut argss_iter = argss.into_iter();
        let this_args = argss_iter
            .next()
            .expect("empty arguments for predicate are illegal in clauses");

        // If we have a single predicate application with no negative samples
        // we can generate an actlit for this one.
        let bias = if iter.next().is_none() && argss_iter.next().is_none() {
            log! { @4 "singular bias right" }
            profile! { |_profiler| "bias: singular right" => add 1 }
            Bias::NuRgt(this_pred, this_args.clone())
        } else {
            // Otherwise we can just generate a negative constraint that's more
            // constrained.
            log! { @4 "partial bias right" }
            profile! { |_profiler| "bias: partial right" => add 1 }
            Bias::Non
        };

        actlits.push((this_actlit, bias));

        Ok(())
    }

    /// Generates exhaustive bias-right actlits.
    fn exhaustive_bias_right(
        &mut self,
        _profiler: &Profiler,
        solver: &mut Slvr,
        actlits: &mut Vec<(Actlit, Bias)>,
        instance: &Instance,
        rhs_actlit: &Option<Actlit>,
    ) -> Res<()> {
        log! { @4 "exhaustive bias right" }
        // We can force all positive examples for all lhs applications but
        // one in turn to try to generate negative examples.
        for (this_pred, map) in &self.lhs_actlits {
            for (this_args, _) in map {
                solver.comment(&format!(
                    "actlit forcing everything but ({} {})",
                    instance[*this_pred], this_args
                ))?;
                let this_actlit = solver.get_actlit()?;

                // Force rhs false if any.
                if let Some(rhs_actlit) = rhs_actlit.as_ref() {
                    solver.assert_act(&this_actlit, rhs_actlit)?
                }

                // Activate everything else than this particular application
                for (pred, map) in &self.lhs_actlits {
                    for (args, actlit) in map {
                        if pred == this_pred && args == this_args {
                            continue;
                        }
                        solver.assert_act(&this_actlit, actlit)?
                    }
                }

                profile! { |_profiler| "bias: exhaustive right" => add 1 }

                actlits.push((this_actlit, Bias::NuRgt(*this_pred, this_args.clone())))
            }
        }

        Ok(())
    }
}

///
fn get_actlit(solver: &mut Slvr, args: &VarTerms, data: &VarValsSet) -> Res<Option<Actlit>> {
    let actlit = solver.get_actlit()?;
    let disjunction = DisjArgs::new(args, data)?;
    solver.assert_act(&actlit, &disjunction)?;

    if solver.check_sat_act(Some(&actlit))? {
        log! { @6 "  sat, keeping actlit" }
        Ok(Some(actlit))
    } else {
        log! { @6 "  unsat, discarding actlit" }
        solver.de_actlit(actlit)?;
        Ok(None)
    }
}

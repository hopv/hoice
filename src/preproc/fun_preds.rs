//! Predicate-to-function reduction.
//!
//! This preprocessor attempts to reconstruct function definitions from Horn clauses. Functions are
//! reconstructed as multiple branches of an if-then-else.
//!
//! The core of how this works is the [`map_invert`] function.
//!
//! [`map_invert`]: (fn.map_invert.html) (map_invert function)

use crate::{
    common::*,
    fun::FunSig,
    info::VarInfo,
    preproc::{Clause, PreInstance, RedStrat},
};

/// A branch in the definition of a function.
#[derive(Clone, Debug)]
struct FunBranch {
    /// Guard of the branch (condition).
    guard: TermSet,
    /// Value yielded by the branch.
    value: Term,
    /// Recursive calls.
    calls: VarHMap<Term>,
}

impl FunBranch {
    /// Constructor.
    pub fn new(
        (pred, fun_name, fun_sig, fun_typ): (PrdIdx, &str, &VarInfos, &Typ),
        rhs_args: &VarTerms,
        lhs_terms: &TermSet,
        lhs_preds: &PredApps,
        invars: &mut TermMap<Vec<(usize, Term)>>,
        index: usize,
    ) -> Res<Option<Self>> {
        let fun_args_len = fun_sig.len();
        let (last, fresh, res_idx) = if fun_args_len == rhs_args.len() {
            let last: VarIdx = fun_args_len.into();
            let res_idx: VarIdx = (fun_args_len - 1).into();
            (None, last, res_idx)
        } else {
            let mut fresh: VarIdx = fun_args_len.into();
            let res_idx = fresh;
            fresh.inc();
            (Some(res_idx), fresh, res_idx)
        };

        // println!(
        //     "last: {}, fresh: {}, res_idx: {}",
        //     last.as_ref()
        //         .map(|idx| format!("{}", idx.default_str()))
        //         .unwrap_or("none".into()),
        //     fresh,
        //     res_idx
        // );

        if_log! { @4
            log! { @4 |=>
                "building branch (keeping first {} argumentss) from", fun_args_len ;
                "  rhs_args: (p_{} {})", pred, rhs_args;
                "  fresh:    v_{}", fresh;
                "  lhs_terms:"
            } ;
            for term in lhs_terms {
                log! { @4 |=> "    {}", term }
            };
            log! { @4 |=> "  lhs apps:" };
            for (pred, argss) in lhs_preds {
                for args in argss {
                    log! { @4 |=> "    (p_{} {})", pred, args }
                }
            }
        }

        debug_assert! { fun_args_len == rhs_args.len() || fun_args_len == rhs_args.len() - 1 }
        debug_assert! { lhs_preds.len() <= 1 }
        debug_assert! {
            lhs_preds.iter().next().map(|(p, _)| * p == pred).unwrap_or(true)
        }

        let (guard, subst) = if let Some(res) = args_invert(rhs_args, fun_args_len)? {
            res
        } else {
            log! { @3 "failed to invert rhs arguments {}", rhs_args }
            return Ok(None);
        };

        let mut builder = BranchBuilder {
            args_len: fun_sig.len(),
            fun_typ,
            fun_name,
            last,
            res_idx,
            fresh,
            guard,
            subst,
            calls: VarHMap::new(),
            value: None,
            index,
        };

        if_log! { @4
            log! { @4 |=> "rhs inversion successful" }
            builder.log_subst();
            builder.log_guard();
        }

        let mut lhs_argss: Vec<_> = lhs_preds
            .get(&pred)
            .map(|argss| argss.iter().collect())
            .unwrap_or_else(Vec::new);

        // println!("lhs");
        let okay = builder.work_on_lhs(&mut lhs_argss)?;
        if !okay {
            return Ok(None);
        }
        // println!("done");

        if_log! { @4
            log! { @4 |=> "lhs inversion successful" };
            builder.log_subst();
            builder.log_guard();
            builder.log_calls();
        }

        // println!("subst");
        for term in lhs_terms {
            if let Some((term, _)) = term.subst_total(&builder.subst) {
                builder.guard.insert(term);
            } else {
                log! { @3 | "total substitution failed on term {}", term }
                return Ok(None);
            }
        }
        // println!("done");

        if_log! { @4
            log! { @4 |=> "lhs terms substitution successful" }
            builder.log_guard();
        }

        let value = if let Some(last) = builder.last {
            if let Some((res, _)) = rhs_args[last].subst_total(&builder.subst) {
                res
            } else {
                log! { @3 | "failed to retrieve value for {}", rhs_args[last] }
                return Ok(None);
            }
        } else if let Some(conj) = ::std::mem::replace(&mut builder.value, None) {
            term::and(conj)
        } else {
            term::tru()
        };

        log! { @4 | "value extraction successful: {}", value }

        // println!("potential invariants");
        builder.potential_invariants(invars);
        // println!("done");

        if_log! { @4
            log! { @4 |=> "potential invariant extraction successful" }
            builder.log_guard();
            log! { @4 |=> "  invariants:" };
            for invar in invars.keys() {
                log! { @4 |=> "    {}", invar }
            };
        }

        Ok(Some(FunBranch {
            guard: builder.guard,
            value,
            calls: builder.calls,
        }))
    }

    /// Propagates the substition `calls` to the whole branch.
    fn propagate_calls(&mut self) {
        if !self.calls.is_empty() {
            self.guard = self
                .guard
                .iter()
                .map(|term| term.subst(&self.calls).0)
                .collect();
            self.value = self.value.subst(&self.calls).0;
            // self.calls.clear()
        }
    }
}

/// Helper for branch construction for a function.
struct BranchBuilder<'a> {
    /// Number of arguments of the function.
    args_len: usize,
    /// Return type of the function.
    fun_typ: &'a Typ,
    /// Name of the function.
    fun_name: &'a str,
    /// Index of the result. Used to generate invariants.
    res_idx: VarIdx,
    /// The index of the last variable if we are not working on all the arguments. None otherwise.
    ///
    /// If none, then we are reconstructing the predicate itself. Otherwise, we are reconstructing
    /// the function that yields the last argument of the predicate when it is true.
    last: Option<VarIdx>,
    /// Index of the next fresh variable.
    fresh: VarIdx,
    /// Substitution from clause variables to the function's variables.
    subst: VarHMap<Term>,
    /// Guard of the branch.
    guard: TermSet,
    /// Recursive calls appearing in this branch.
    calls: VarHMap<Term>,
    /// Value yielded by the branch.
    value: Option<Vec<Term>>,
    /// Index of the current branch.
    index: usize,
}
impl<'a> BranchBuilder<'a> {
    /// Index of the next fresh variable.
    ///
    /// Increases the internal counter.
    fn get_fresh(&mut self) -> VarIdx {
        let res = self.fresh;
        self.fresh.inc();
        res
    }

    /// Retrieves potential invariants.
    ///
    /// A term from the guard of the branch is elligible as a candidate invariant if it mentions
    /// **exactly one** variable from `builder.calls`.
    fn potential_invariants(&mut self, invars: &mut TermMap<Vec<(usize, Term)>>) {
        let mut invar_subst = VarHMap::with_capacity(1);
        let guard = &mut self.guard;
        let calls = &mut self.calls;
        let fun_typ = &self.fun_typ;
        let index = self.index;
        let res_idx = self.res_idx;

        guard.retain(|term| {
            let term_vars = term::vars(&term);

            let mut vars = vec![];

            for var in term_vars {
                if calls.get(&var).is_some() {
                    vars.push(var)
                }
            }

            if vars.len() == 1 {
                let var = vars[0];
                invar_subst.insert(var, term::var(res_idx, (*fun_typ).clone()));
                let (invar, _) = term.subst(&invar_subst);
                invars
                    .entry(invar)
                    .or_insert_with(Vec::new)
                    .push((index, term.clone()));
                false
            } else {
                true
            }
        })
    }

    /// Handles the lhs predicate applications.
    fn work_on_lhs(&mut self, lhs_argss: &mut Vec<&VarTerms>) -> Res<bool> {
        let mut nu_args = Vec::with_capacity(self.args_len);
        debug_assert! { self.value.is_none() }

        macro_rules! register_call {
            ($call:expr) => {{
                // Check if we already have a binding for this call.
                let mut var = None;
                for (v, trm) in &self.calls {
                    if $call == *trm {
                        // Found a variable for this call.
                        var = Some(*v);
                        break;
                    }
                }
                if let Some(var) = var {
                    // Already have a binding.
                    var
                } else {
                    // Create new binding.
                    let fresh = self.get_fresh();
                    // println!("fresh: {}", fresh);
                    let prev = self.calls.insert(fresh, $call);
                    debug_assert! { prev.is_none() }
                    fresh
                }
            }};
        }

        while !lhs_argss.is_empty() {
            let prev_len = lhs_argss.len();
            let mut failed: Res<_> = Ok(false);

            // println!();

            lhs_argss.retain(|args| {
                for arg in &args[0..self.args_len] {
                    if let Some((nu_arg, _)) = arg.subst_total(&self.subst) {
                        // println!("  {} -> {}", arg, nu_arg);
                        nu_args.push(nu_arg);
                    } else {
                        // println!("skip");
                        nu_args.clear();
                        return true;
                    }
                }
                let nu_args = ::std::mem::replace(&mut nu_args, Vec::with_capacity(self.args_len));

                // println!("fun app 1");
                let fun_app = term::fun(self.fun_name, nu_args);
                let fun_app_var = register_call!(fun_app);
                // println!("fun app 2");
                let fun_app = term::var(fun_app_var, self.fun_typ.clone());
                // println!("done");

                let okay = if let Some(last) = self.last.as_ref() {
                    let last = *last;
                    // println!("map_invert ({})", last);
                    // println!("  {} ({})", args[last], args[last].typ());
                    // println!("  {} ({})", fun_app, fun_app.typ());
                    let res = map_invert(&args[last], fun_app, &mut self.subst, &mut self.guard);
                    // println!("done");
                    res
                } else {
                    self.value.get_or_insert_with(Vec::new).push(fun_app);
                    Ok(true)
                };

                match okay {
                    Ok(true) => false,
                    Ok(false) => {
                        if let Ok(failed) = failed.as_mut() {
                            *failed = true
                        }
                        true
                    }
                    err => {
                        failed = err.chain_err(|| format!("while inverting {}", args));
                        true
                    }
                }
            });

            if failed? {
                log! { @3 | "failed" }
                return Ok(false);
            } else if lhs_argss.len() == prev_len {
                // not making progress.
                log! { @3 | "not making progress on lhs preds" }
                return Ok(false);
            }
        }

        Ok(true)
    }
}

/// Log functions.
impl<'a> BranchBuilder<'a> {
    #[allow(dead_code)]
    #[cfg(not(feature = "bench"))]
    fn log_guard(&self) {
        log! { @4 |=> "  guard:" }
        for term in &self.guard {
            log! { @4 |=> "    {}", term }
        }
    }
    #[allow(dead_code)]
    #[cfg(not(feature = "bench"))]
    fn log_calls(&self) {
        log! { @4 |=> "  rec calls:" }
        for (var, term) in &self.calls {
            log! { @4 |=> "    v_{} -> {}", var, term }
        }
    }
    #[allow(dead_code)]
    #[cfg(not(feature = "bench"))]
    fn log_subst(&self) {
        log! { @4 |=> "  subst:" }
        for (var, term) in &self.subst {
            log! { @4 |=> "    v_{} -> {}", var, term }
        }
    }
}

/// A function definition.
#[derive(Clone, Debug)]
struct FunDef {
    /// Predicate this function is for.
    pred: PrdIdx,
    /// Index of the result. Used to represent invariants.
    res_idx: VarIdx,
    /// Function name.
    name: String,
    /// Function signature.
    sig: VarInfos,
    /// Function type.
    typ: Typ,
    /// Branches of the definition.
    branches: Vec<FunBranch>,
    /// Candidates invariants.
    ///
    /// Maps candidates to the index of the branch they come from, and the term they originate
    /// from. If a candidate is not an invariant, it will be added back to the corresponding
    /// branches.
    candidate_invars: TermMap<Vec<(usize, Term)>>,
    /// Invariants.
    ///
    /// Invariants are all terms ranging over exactly one variable, the variable `v_0`. This
    /// variable is a placeholder for the function call.
    ///
    /// # Examples
    ///
    /// If `fun(args) >= 0` is an invariant, then the set contains `v_0 >= 0`.
    invars: TermSet,
}

impl FunDef {
    /// Creates an empty function definition.
    pub fn new(pred: PrdIdx, name: String, sig: VarInfos, typ: Typ, res_idx: VarIdx) -> Self {
        FunDef {
            pred,
            name,
            sig,
            typ,
            res_idx,
            branches: Vec::new(),
            candidate_invars: TermMap::new(),
            invars: TermSet::new(),
        }
    }

    /// Registers a clause.
    ///
    /// Returns none if the registration failed and the reconstruction process must be aborted.
    /// Invariants are not checked.
    pub fn register_clause(mut self, clause: &Clause) -> Res<Option<Self>> {
        let rhs_args = if let Some((p, args)) = clause.rhs() {
            debug_assert_eq! { p, self.pred }
            args
        } else {
            bail!("FunDef::register_clause called with illegal clause")
        };

        let index = self.branches.len();

        let res = if let Some(branch) = FunBranch::new(
            (self.pred, &self.name, &self.sig, &self.typ),
            rhs_args,
            clause.lhs_terms(),
            clause.lhs_preds(),
            &mut self.candidate_invars,
            index,
        )? {
            self.branches.push(branch);
            Some(self)
        } else {
            None
        };

        Ok(res)
    }

    /// Checks that invariants are actual invariants.
    ///
    /// Once the invariants are confirmed, all the substitutions defined by `calls` in the branches
    /// are applied to the guard and the result.
    pub fn check_invariants(&mut self, instance: &mut PreInstance) -> Res<()> {
        macro_rules! solver {
            () => {
                instance.solver()
            };
        }

        if !self.candidate_invars.is_empty() {
            log! { @3 | "checking {} invariants...", self.candidate_invars.len() }
            if_log! { @4
                for invar in self.candidate_invars.keys() {
                    log! { @4 |=> "{}", invar }
                }
            }
            solver!().comment_args(format_args!(
                "checking candidate invariants for function {}",
                self.name
            ))?;
        }

        let mut subst = VarHMap::with_capacity(1);

        'check_invariants: for (invariant, backtrack) in self.candidate_invars.drain() {
            solver!().comment_args(format_args!("checking candidate invariant {}", invariant))?;

            macro_rules! backtrack {
                () => {{
                    log! { @3 | "  not an invariant: {}", invariant }
                    for (index, term) in backtrack {
                        self.branches[index].guard.insert(term);
                    }
                    continue 'check_invariants;
                }};
            }

            // Check invariant holds for each branch.
            'all_branches: for branch_index in 0..self.branches.len() {
                macro_rules! branch {
                    () => {
                        self.branches[branch_index]
                    };
                }

                // Target invariant (negated).
                let neg_objective = {
                    let invariant = if self.sig.len() < instance[self.pred].sig().len() {
                        subst.insert(self.res_idx, branch!().value.clone());
                        // println!("subst ({}):", self.res_idx);
                        // for (key, val) in &subst {
                        //     println!("  {} -> {}", key.default_str(), val)
                        // }
                        // println!("{}", invariant);
                        let res = invariant.clone().subst(&subst).0;
                        subst.clear();
                        res
                    } else {
                        invariant.clone()
                    };

                    match invariant.bool() {
                        Some(true) => continue 'all_branches,
                        Some(false) => backtrack!(),
                        None => term::not(invariant),
                    }
                };

                // Declare function's variables.
                for info in &self.sig {
                    solver!().declare_const(&info.idx, info)?
                }

                // Declare recursive call variables.
                if !branch!().calls.is_empty() {
                    solver!().comment("declaring vars for recursive calls")?;
                    for (var, _) in &branch!().calls {
                        solver!().declare_const(var, self.typ.get())?
                    }
                }

                solver!().comment("branch guard")?;

                for term in &branch!().guard {
                    solver!().assert(&smt::SmtTerm::new(term))?
                }

                if !branch!().calls.is_empty() {
                    solver!().comment("recursion hypotheses")?;

                    for (var, term) in &branch!().calls {
                        if let Some((_, args)) = term.fun_inspect() {
                            let mut var: VarIdx = 0.into();
                            for arg in args {
                                subst.insert(var, arg.clone());
                                var.inc()
                            }
                        } else {
                            bail!("ill-formed function reconstruction context")
                        }
                        if self.sig.len() < instance[self.pred].sig().len() {
                            subst.insert(self.res_idx, term::var(*var, self.typ.clone()));
                        }
                        // println!("subst:");
                        // for (key, val) in &subst {
                        //     println!("  {} -> {}", key.default_str(), val)
                        // }
                        // println!("{}", invariant);
                        let invariant = invariant
                            .clone()
                            .subst_total(&subst)
                            .expect("cannot fail by construction")
                            .0;

                        subst.clear();

                        solver!().assert(&smt::SmtTerm::new(&invariant))?
                    }
                }

                solver!().comment("invariant to prove on output value")?;
                solver!().assert(&smt::SmtTerm::new(&neg_objective))?;

                let sat = solver!().check_sat()?;

                instance.reset_solver()?;

                if sat {
                    backtrack!()
                }
            }

            log! { @3 | "  confirmed invariant: {}", invariant }
            let is_new = self.invars.insert(invariant);
            debug_assert! { is_new }
        }

        for branch in &mut self.branches {
            branch.propagate_calls()
        }

        Ok(())
    }

    /// Checks that all branches are exclusive and exhaustive.
    pub fn check_branches(&self, instance: &mut PreInstance, check_exhaustive: bool) -> Res<bool> {
        let res = self.inner_check_branches(instance, check_exhaustive)?;
        instance.reset_solver()?;
        Ok(res)
    }

    /// Checks that all branches are exclusive and exhaustive.
    fn inner_check_branches(
        &self,
        instance: &mut PreInstance,
        check_exhaustive: bool,
    ) -> Res<bool> {
        macro_rules! solver {
            () => {
                instance.solver()
            };
        }

        for info in &self.sig {
            solver!().declare_const(&info.idx, info.typ.get())?
        }

        solver!().declare_fun(&self.name, &self.sig, self.typ.get())?;

        solver!().comment_args(format_args!(
            "checking branches for {} are exclusive",
            self.name
        ))?;

        let mut actlits = Vec::with_capacity(self.branches.len());

        for branch in &self.branches {
            let conj = smt::TermConj::new(branch.guard.iter());
            let actlit = solver!().get_actlit()?;
            solver!().assert_act_with(&actlit, &conj, true)?;
            actlits.push(actlit)
        }

        {
            let mut actlits_iter = actlits.iter();
            while let Some(actlit) = actlits_iter.next() {
                for other in actlits_iter.clone() {
                    let not_exclusive = solver!().check_sat_act(vec![actlit, other])?;
                    if not_exclusive {
                        log! { @3 "branches are not mutually exclusive" }
                        return Ok(false);
                    }
                }
            }
        }

        for actlit in actlits {
            solver!().de_actlit(actlit)?
        }

        log! { @3 | "all branches are exclusive" }

        if check_exhaustive {
            log! { @3 | "checking they're exhaustive" }

            solver!().comment_args(format_args!(
                "checking branches for {} are exhaustive",
                self.name
            ))?;

            for branch in &self.branches {
                let conj = smt::TermConj::new(branch.guard.iter());
                solver!().assert_with(&conj, false)?;
            }

            let not_exhaustive = solver!().check_sat()?;

            if not_exhaustive {
                log! { @3 | "branches are not exhaustive" }
                return Ok(false);
            } else {
                log! { @3 | "branches are exhaustive" }
            }
        }

        Ok(true)
    }

    /// Finalizes the function definition.
    pub fn finalize(
        mut self,
        instance: &mut PreInstance,
        check_exhaustive: bool,
    ) -> Res<Option<Fun>> {
        // println!("candidates:");
        crate::learning::ice::quals::NuQuals::mine_sig(instance[self.pred].sig(), |candidate| {
            // println!("  {}", candidate);
            // println!("candidate ({}): {}", candidate, self.res_idx.default_str());
            if term::vars(&candidate).contains(&self.res_idx) {
                // println!("  adding it");
                self.candidate_invars
                    .entry(candidate.clone())
                    .or_insert_with(Vec::new);
                self.candidate_invars
                    .entry(term::not(candidate))
                    .or_insert_with(Vec::new);
                ()
            }
            Ok(())
        })?;
        // println!("done");
        // if self.typ.is_arith() {
        //     let (zero, one) = if self.typ.is_int() {
        //         (term::int(0), term::int(1))
        //     } else {
        //         (
        //             term::real((0.into(), 1.into())),
        //             term::real((1.into(), 1.into())),
        //         )
        //     };

        //     let term = term::var(0, self.typ.clone());

        //     let t = term::ge(term.clone(), zero.clone());
        //     self.candidate_invars.entry(t).or_insert_with(Vec::new);
        //     let t = term::le(term.clone(), zero.clone());
        //     self.candidate_invars.entry(t).or_insert_with(Vec::new);

        //     let t = term::ge(term.clone(), one.clone());
        //     self.candidate_invars.entry(t).or_insert_with(Vec::new);
        //     let t = term::le(term.clone(), term::u_minus(one.clone()));
        //     self.candidate_invars.entry(t).or_insert_with(Vec::new);
        // }
        // println!("checking invariants");
        self.check_invariants(instance)
            .chain_err(|| "while checking the invariants")?;
        // println!("done");

        let invs = self.invars.len();
        if invs > 0 {
            log! { @3 | "discovered {} invariant(s)", invs }
        }

        let okay = self
            .check_branches(instance, check_exhaustive)
            .chain_err(|| "while checking branches")?;

        if !okay {
            return Ok(None);
        }

        // Everything okay, let's do this.

        self.branches.sort_by(|b_1, b_2| {
            use std::cmp::Ordering::*;
            match b_1.calls.len().cmp(&b_2.calls.len()) {
                Equal => b_1.guard.len().cmp(&b_2.guard.len()),
                res => res,
            }
        });

        let mut invs = Vec::with_capacity(self.invars.len());
        if !self.invars.is_empty() {
            let mut subst = VarHMap::new();
            if self.sig.len() < instance[self.pred].sig().len() {
                subst.insert(
                    self.res_idx,
                    term::fun(
                        self.name.clone(),
                        self.sig
                            .clone()
                            .into_iter()
                            .map(|info| term::var(info.idx, info.typ))
                            .collect(),
                    ),
                );
            }

            for inv in self.invars {
                // println!("subst:");
                // for (key, val) in subst.iter() {
                //     println!("  {} -> {}", key.default_str(), val)
                // }
                // println!("inv: {}", inv);
                let inv = if self.sig.len() == instance[self.pred].sig().len() {
                    let mut args: Vec<Term> = Vec::with_capacity(self.sig.len()).into();
                    for info in &self.sig {
                        args.push(term::var(info.idx, info.typ.clone()))
                    }
                    let fun_app = term::fun(self.name.clone(), args);
                    term::implies(fun_app, inv)
                } else {
                    inv.subst(&subst).0
                };

                invs.push(inv);
            }
        }

        // Build actual definition.
        let mut def = None;
        for branch in self.branches.into_iter().rev() {
            let cond = term::and(branch.guard.into_iter().collect());
            let nu_def = if let Some(def) = def {
                term::ite(cond, branch.value, def)
            } else {
                if !check_exhaustive {
                    debug_assert! { self.typ.is_bool() }
                    term::ite(cond, branch.value, term::fls())
                } else {
                    branch.value
                }
            };
            def = Some(nu_def)
        }

        let def = def.ok_or("empty definitions during finalization in fun_preds")?;

        // Finally creating the function.
        let pred = self.pred;

        let sig = fun::retrieve_sig(&self.name)?;
        let mut rfun = sig.into_fun(def);

        rfun.set_synthetic(pred);
        rfun.invariants.extend(invs);

        let fun = fun::new(rfun).chain_err(|| {
            format!(
                "while creating internal function for predicate {}",
                conf.bad(&instance[pred].name)
            )
        })?;
        instance.add_companion_fun(pred, fun.clone());

        // Restart the solver to make sure the function is defined for the next user.
        instance.reset_solver()?;

        Ok(Some(fun))
    }
}

/// Function reconstruction from clauses over some predicates.
///
/// The technique will attempt to reconstruct predicate `pred` of arity `ar` if
///
/// - when it appears in the RHS of aclause, then the only predicate applications in the LHS of
///   this clause are applications of `pred`, and
/// - it is not the only undefined predicate left, and
/// - exactly *one* of its `ar - 1` first arguments is a datatype.
///
/// # Examples
///
/// ```
/// # use hoice::{ common::PrdIdx, parse, preproc::{ PreInstance, RedStrat, FunPreds } };
/// let mut instance = parse::instance("
///   (declare-fun len_fun_preds_example ( (List Int) Int ) Bool)
///   (declare-fun unused ( Int ) Bool)
///   (assert
///     (forall ( (n Int) )
///       (len_fun_preds_example nil 0)
///     )
///   )
///   (assert
///     (forall ( (t (List Int)) (h Int) (n Int) )
///       (=>
///         (and
///           (len_fun_preds_example t n)
///         )
///         (len_fun_preds_example (insert h t) (+ n 1))
///       )
///     )
///   )
/// ");
///
/// let mut fun_preds = FunPreds::new(& instance);
/// let mut instance = PreInstance::new(& mut instance).unwrap();
/// let info = fun_preds.apply(& mut instance).unwrap();
/// assert_eq! { info.preds, 2 } // 2 because `unused` is simplified by propagation
///
/// let pred: PrdIdx = 0.into();
/// assert_eq! { "len_fun_preds_example", & instance[pred].name }
///
/// let funs = instance[pred].funs();
/// assert_eq!( "len_fun_preds_example_hoice_reserved_fun", &funs[0].name);
/// assert_eq! {
///     "(ite \
///         (not (is-insert v_0)) \
///         0 \
///         (+ 1 (len_fun_preds_example_hoice_reserved_fun (tail v_0)))\
///     )", & format!("{}", funs[0].def)
/// }
/// ```
pub struct FunPreds {
    to_inline: Vec<(PrdIdx, bool)>,
}

impl FunPreds {
    /// Reduces a predicate to a function.
    pub fn reduce_pred(
        instance: &mut PreInstance,
        pred: PrdIdx,
        use_all_args: bool,
    ) -> Res<Option<RedInfo>> {
        let mut info = RedInfo::new();
        // Clauses to remove.
        let mut to_rm = vec![];

        log!(@2 "working on {}", conf.emph(& instance[pred].name));

        debug_assert! { to_rm.is_empty() }

        let mut var_infos = VarInfos::new();

        let args_len = if use_all_args {
            instance[pred].sig.len()
        } else {
            instance[pred].sig.len() - 1
        };

        for typ in &instance[pred].sig[0..args_len] {
            let idx = var_infos.next_index();
            let var_info = VarInfo::new(idx.default_str(), typ.clone(), idx);
            var_infos.push(var_info)
        }
        let res_idx: VarIdx = (instance[pred].sig.len() - 1).into();
        let last: Option<VarIdx> = if use_all_args { None } else { Some(res_idx) };

        // println!(
        //     "last: {}, res_idx: {}",
        //     last.as_ref()
        //         .map(|idx| format!("{}", idx.default_str()))
        //         .unwrap_or("none".into()),
        //     res_idx
        // );

        let pred_fun_name = make_fun_name(&instance[pred].name).chain_err(|| {
            format!(
                "while creating function for predicate {}",
                conf.emph(&instance[pred].name)
            )
        })?;
        let pred_fun_typ = if let Some(last) = last.as_ref() {
            instance[pred].sig[*last].clone()
        } else {
            typ::bool()
        };

        let sig = FunSig::new(
            pred_fun_name.clone(),
            var_infos.clone(),
            pred_fun_typ.clone(),
        );
        fun::register_sig(sig)?;

        macro_rules! abort {
            ($($stuff:tt)*) => {{
                let _ = fun::retrieve_sig(&pred_fun_name);
                return Ok(None);
            }};
        }

        let mut fun_def = FunDef::new(
            pred,
            pred_fun_name.clone(),
            var_infos,
            pred_fun_typ,
            res_idx,
        );

        for clause in instance.clauses_of(pred).1 {
            let clause = *clause;
            to_rm.push(clause);

            log! { @3 | "working on clause #{}", clause }

            fun_def = if let Some(new) = fun_def.register_clause(&instance[clause])? {
                new
            } else {
                log! { @3 | "clause registration failed" }
                abort!()
            };
        }

        let fun = if let Some(fun) = fun_def.finalize(instance, !use_all_args)? {
            fun
        } else {
            abort!()
        };

        info.clauses_rmed += to_rm.len();
        instance.forget_clauses(&mut to_rm)?;

        let mut args = Vec::with_capacity(args_len);
        for (var, typ) in instance[pred].sig.index_iter().take(args_len) {
            args.push(term::var(var, typ.clone()))
        }
        let fun_app = term::fun(fun.name.clone(), args);

        let def = if let Some(last) = last.as_ref() {
            term::eq(term::var(*last, fun.typ.clone()), fun_app)
        } else {
            fun_app
        };

        info.preds += 1;
        let mut tterm_set = TTermSet::new();
        tterm_set.insert_term(def);
        info += instance.force_dnf_left(pred, vec![(Quantfed::new(), tterm_set)])?;

        Ok(Some(info))
    }
}

impl RedStrat for FunPreds {
    fn name(&self) -> &'static str {
        "fun_preds"
    }

    fn new(_: &Instance) -> Self {
        FunPreds {
            to_inline: Vec::new(),
        }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();
        let mut new_stuff = true;

        while new_stuff {
            new_stuff = false;
            self.to_inline.clear();

            'all_preds: for info in instance.preds() {
                let pred = info.idx;

                // println!("{}", instance[pred]);
                // for clause in instance.clauses_of(pred).1 {
                //     println!(
                //         "{}",
                //         instance[*clause].to_string_info(instance.preds()).unwrap()
                //     );
                // }

                // Predicate is still unknown.
                if instance[pred].is_defined() {
                    // println!("  known");
                    continue 'all_preds;
                }

                // When `pred` appears in the rhs of a clause, the lhs only mentions
                // `pred`.
                for clause in instance.clauses_of(pred).1 {
                    if instance[*clause]
                        .lhs_preds()
                        .iter()
                        .any(|(p, _)| *p != pred)
                    {
                        continue 'all_preds;
                    }
                }

                // // `pred` appears more than once in a clause where it's not alone.
                // let potential_relation = instance.clauses_of(pred).0.iter().any(|clause| {
                //     instance[*clause].lhs_preds().get(&pred).unwrap().len() > 1
                //         && (instance[*clause].lhs_preds().len() > 1 || instance[*clause]
                //             .rhs()
                //             .map(|(p, _)| pred != *p)
                //             .unwrap_or(false))
                //         && instance[*clause].rhs().is_none()
                // });

                let mut has_fun_apps = false;

                // Clauses where `pred` is in the rhs do not have function calls.
                // if !potential_relation {
                for clause in instance.clauses_of(pred).1 {
                    if instance[*clause].has_fun_apps() {
                        has_fun_apps = true
                    }
                    // if instance[*clause].has_fun_apps() {
                    //     // println!("  recursive function");
                    //     continue 'all_preds;
                    // }
                }
                // }

                // `pred` has only one dtyp argument (ignoring the last argument)
                if info.sig.len() <= 1
                    || info.sig[0..info.sig.len() - 1]
                        .iter()
                        .filter(|typ| typ.is_dtyp())
                        .count()
                        != 1
                {
                    // println!("  more than one dtyp arg");
                    continue 'all_preds;
                }

                self.to_inline.push((pred, has_fun_apps))
            }

            // Note that we're reverse-sorting because we're going to pop below.
            self.to_inline
                .sort_by(|(p_1, has_fun_1), (p_2, has_fun_2)| {
                    use std::cmp::Ordering::*;
                    if *has_fun_1 && !*has_fun_2 {
                        return Less;
                    } else if *has_fun_2 && !*has_fun_1 {
                        return Greater;
                    }

                    let (sig_1, sig_2) = (&instance[*p_1].sig, &instance[*p_2].sig);
                    let adt_count_1 =
                        sig_1
                            .iter()
                            .fold(0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc });
                    let adt_count_2 =
                        sig_2
                            .iter()
                            .fold(0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc });

                    match adt_count_1.cmp(&adt_count_2).reverse() {
                        ::std::cmp::Ordering::Equal => sig_1.len().cmp(&sig_2.len()).reverse(),
                        res => res,
                    }
                });

            if self.to_inline.is_empty() {
                return Ok(info);
            }

            while let Some((pred, _)) = self.to_inline.pop() {
                // if instance.active_pred_count() <= 1 {
                //     return Ok(info);
                // }

                let res = FunPreds::reduce_pred(instance, pred, false)?;
                // pause("to resume fun_preds", & Profiler::new()) ;
                if let Some(red_info) = res {
                    new_stuff = true;
                    info += red_info;
                    break;
                } else {
                    let res = FunPreds::reduce_pred(instance, pred, true)?;
                    // pause("to resume fun_preds", & Profiler::new()) ;
                    if let Some(red_info) = res {
                        new_stuff = true;
                        info += red_info;
                        break;
                    }
                    ()
                }
            }
        }

        Ok(info)
    }
}

/// Builds a cube and a substitution corresponding to inverting some arguments.
///
/// It is essentially a repeated application of [`map_invert`] to all
/// arguments. It ends when
///
/// - all of the arguments are inversed, or
/// - a subset of the arguments cannot be inversed at all (the result will be `None` in this case).
///
/// [`map_invert`]: fn.map_invert.html (map_invert function)
pub fn args_invert(args: &VarTerms, args_len: usize) -> Res<Option<(TermSet, VarHMap<Term>)>> {
    let (mut cube, mut subst) = (TermSet::new(), VarHMap::new());

    debug_assert! { args.len() >= 1 }

    let mut postponed = Vec::new();
    let mut current: Vec<_> = args
        .index_iter()
        .take(args_len)
        .map(|(var, term)| (term::var(var, term.typ()), term))
        .collect();

    let mut did_something;

    while !current.is_empty() {
        debug_assert! { postponed.is_empty() }

        did_something = false;

        for (var, term) in current.drain(0..) {
            log! { @5 | "attempting to invert {} | {}", var, term }
            if_log! { @6
              log! { @6 |=> "subst:" }
              for (var, term) in & subst {
                log! { @6 |=> "  {}: {}", var.default_str(), term }
              }
              log! { @6 |=> "cube:" }
              for term in & cube {
                log! { @6 |=> "  {}", term }
              }
            }

            let worked = map_invert(term, var.clone(), &mut subst, &mut cube)?;

            if worked {
                log! { @5 "success :)" }
                did_something = true;
            } else {
                log! { @5 "failed :(" }
                postponed.push((var, term))
            }
        }

        // Making progress?
        if !did_something {
            return Ok(None);
        } else {
            ::std::mem::swap(&mut postponed, &mut current)
        }
    }

    Ok(Some((cube, subst)))
}

/// Inverts a term to complete a substitution and a cube.
///
/// Returns false if the invertion failed. In this case, `subst` and `cube` are the same as before
/// the call.
///
/// Otherwise, the cube is augmented with the constraints regarding `term` coming from `to_invert`
/// (see the example). The substitution is augmented with a map from one of the variables in
/// `to_invert` to a term built around `term`.
///
/// # Examples
///
/// ```rust
/// # use hoice::{ common::*, preproc::fun_preds::map_invert };
/// let v_0 = term::var(0, typ::int());
/// let (mut subst, mut cube) = (VarHMap::new(), TermSet::new());
///
/// // First term cannot be inverted as is.
/// let t_1 = term::add( vec![term::var(2, typ::int()), term::var(3, typ::int())] );
/// // Second one is.
/// let t_2 = term::cmul(7, term::var(3, typ::int()));
///
/// // This fails, an addition of two variables cannot be inverted unless one of them appears in
/// // the substitution.
/// let okay = map_invert(& t_1, v_0.clone(), & mut subst, & mut cube).unwrap();
/// assert! { !okay }
/// assert! { subst.is_empty() }
/// assert! {  cube.is_empty() }
///
/// let okay = map_invert(& t_2, v_0.clone(), & mut subst, & mut cube).unwrap();
/// assert! { okay }
/// let v_7_mod_7 = term::eq(
///     term::modulo(v_0.clone(), term::cst( val::int(7) )), term::cst( val::int(0) )
/// );
/// assert! { cube.contains(&v_7_mod_7) }
/// let v_0_div_7 = term::idiv( vec![v_0.clone(), term::cst( val::int(7) )] );
/// assert_eq! { & v_0_div_7, subst.get(& 3.into()).unwrap() }
///
/// // Now we have a substitution for `v_3`, so now inverting `t_1` works.
/// let okay = map_invert(& t_1, v_0.clone(), & mut subst, & mut cube).unwrap();
/// assert! { okay }
/// let v_0_sub_v_0_div_7 = term::sub( vec![v_0.clone(), v_0_div_7.clone()] );
/// assert_eq! { & v_0_sub_v_0_div_7, subst.get(& 2.into()).unwrap() }
/// ```
pub fn map_invert(
    to_invert: &Term,
    term: Term,
    subst: &mut VarHMap<Term>,
    cube: &mut TermSet,
) -> Res<bool> {
    debug_assert_eq! { to_invert.typ(), term.typ() }

    // These are the new terms to insert in `cube` and the new map from variables to terms that we
    // need to add. We do not mutate `subst` nor `cube` directly because the invertion process
    // might fail, in which case the caller will move on.
    let (mut nu_cube, mut nu_subst) = (vec![], VarHMap::<Term>::new());

    // Stack of pairs composed of two terms. The second one is the term to invert, and the first
    // one is the pivot.
    let mut stack = vec![(term, to_invert.get())];

    while let Some((term, to_invert)) = stack.pop() {
        match to_invert {
            RTerm::Cst(val) => {
                nu_cube.push(term::eq(term, term::val(val.clone())));
                continue;
            }

            RTerm::Var(_, var) => {
                if let Some(t) = subst.get(var) {
                    nu_cube.push(term::eq(term, t.clone()));
                    continue;
                } else if let Some(t) = nu_subst.get(var) {
                    nu_cube.push(term::eq(term, t.clone()));
                    continue;
                }

                nu_subst.insert(*var, term);
            }

            // Constant array.
            RTerm::CArray {
                term: inner, typ, ..
            } => {
                stack.push((
                    // Array is constant, select any value.
                    term::select(term, typ.default_term()),
                    inner.get(),
                ))
            }

            RTerm::App { typ, op, args, .. } => {
                match op {
                    Op::CMul => {
                        cmul_invert(to_invert, term, typ, args, &mut nu_cube, &mut stack)?;
                        continue;
                    }

                    Op::Add => {
                        let okay = add_invert(
                            term,
                            typ,
                            args,
                            &mut nu_cube,
                            &mut stack,
                            subst,
                            &nu_subst,
                        )?;
                        if !okay {
                            return Ok(false);
                        }
                        continue;
                    }

                    Op::Sub => {
                        let okay = sub_invert(
                            term,
                            typ,
                            args,
                            &mut nu_cube,
                            &mut stack,
                            subst,
                            &nu_subst,
                        )?;
                        if !okay {
                            return Ok(false);
                        }

                        continue;
                    }

                    _ => (),
                }

                let mut nu_args = Vec::with_capacity(args.len());
                for arg in args {
                    if let Some((arg, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
                        nu_args.push(arg)
                    } else {
                        return Ok(false);
                    }
                }

                nu_cube.push(term::eq(term, term::app(*op, nu_args)))
            }

            RTerm::DTypNew {
                typ, name, args, ..
            } => dtyp_new_invert(&term, typ, name, args, &mut nu_cube, &mut stack)?,

            RTerm::DTypSlc {
                typ,
                name,
                term: inner,
                ..
            } => {
                let okay = dtyp_slc_invert(term, typ, name, inner, &mut nu_cube, subst, &nu_subst);
                if !okay {
                    return Ok(false);
                }
            }

            RTerm::DTypTst {
                name, term: inner, ..
            } => {
                let okay = dtyp_tst_invert(term, name, inner, &mut nu_cube, subst, &nu_subst);
                if !okay {
                    return Ok(false);
                }
            }

            RTerm::Fun { name, args, .. } => {
                let okay = fun_invert(term, name, args, &mut nu_cube, subst, &nu_subst);
                if !okay {
                    return Ok(false);
                }
            }
        }
    }

    for term in nu_cube {
        cube.insert(term);
    }
    for (var, term) in nu_subst {
        let prev = subst.insert(var, term);
        debug_assert! { prev.is_none() }
    }

    Ok(true)
}

/// Inverts a datatype constructor.
fn dtyp_new_invert<'a>(
    term: &Term,
    typ: &Typ,
    name: &str,
    args: &'a [Term],
    cube: &mut Vec<Term>,
    stack: &mut Vec<(Term, &'a RTerm)>,
) -> Res<()> {
    let selectors = typ.selectors_of(name)?;
    debug_assert_eq! { args.len(), selectors.len() }

    cube.push(term::dtyp_tst(name, term.clone()));

    for (arg, (slc, _)) in args.iter().zip(selectors.iter()) {
        stack.push((
            term::dtyp_slc(arg.typ(), slc.clone(), term.clone()),
            arg.get(),
        ))
    }

    Ok(())
}

/// Inverts a cmul application.
fn cmul_invert<'a>(
    to_invert: &RTerm,
    term: Term,
    typ: &Typ,
    args: &'a [Term],
    cube: &mut Vec<Term>,
    stack: &mut Vec<(Term, &'a RTerm)>,
) -> Res<()> {
    if args[0].val().is_some() {
        let nu_term = if typ.is_int() {
            // Current term modulo `args[0].val()` is zero.
            cube.push(term::eq(
                term::modulo(term.clone(), args[0].clone()),
                term::int(0),
            ));
            term::idiv(vec![term, args[0].clone()])
        } else if typ.is_real() {
            term::div(vec![term, args[0].clone()])
        } else {
            bail!("unexpected multiplication over type {}", typ)
        };
        stack.push((nu_term, args[1].get()));
    } else {
        bail!("illegal CMul term {}", to_invert)
    }

    Ok(())
}

/// Inverts an addition.
fn add_invert<'a>(
    term: Term,
    typ: &Typ,
    args: &'a [Term],
    cube: &mut Vec<Term>,
    stack: &mut Vec<(Term, &'a RTerm)>,
    subst: &VarHMap<Term>,
    nu_subst: &VarHMap<Term>,
) -> Res<bool> {
    let mut subtraction = vec![term];
    let mut not_substed = None;

    for arg in args {
        if let Some((term, _)) = arg.subst_total(&(subst, nu_subst)) {
            subtraction.push(term)
        } else if not_substed.is_some() {
            return Ok(false);
        } else {
            not_substed = Some(arg.get())
        }
    }

    let nu_term = term::sub(subtraction);

    if let Some(nu_to_invert) = not_substed {
        stack.push((nu_term, nu_to_invert))
    } else {
        cube.push(term::eq(
            nu_term,
            if typ.is_int() {
                term::int_zero()
            } else if typ.is_real() {
                term::real_zero()
            } else {
                bail!("unexpected addition over type {}", typ)
            },
        ))
    }

    Ok(true)
}

/// Inverts a subtraction.
fn sub_invert<'a>(
    term: Term,
    typ: &Typ,
    args: &'a [Term],
    cube: &mut Vec<Term>,
    stack: &mut Vec<(Term, &'a RTerm)>,
    subst: &VarHMap<Term>,
    nu_subst: &VarHMap<Term>,
) -> Res<bool> {
    let mut sub = None;
    let mut add = vec![term];
    let mut not_substed = None;

    let mut first = true;
    for arg in args {
        if let Some((term, _)) = arg.subst_total(&(subst, nu_subst)) {
            if first {
                debug_assert! { sub.is_none() }
                sub = Some(term)
            } else {
                add.push(term)
            }
        } else if not_substed.is_some() {
            return Ok(false);
        } else {
            // Careful of the polarity here.
            not_substed = Some((arg.get(), first))
        }

        first = false
    }

    let nu_term = term::add(add);
    let nu_term = if let Some(sub) = sub {
        term::sub(vec![nu_term, sub])
    } else {
        nu_term
    };

    if let Some((nu_to_invert, positive)) = not_substed {
        stack.push((
            if positive {
                nu_term
            } else {
                term::u_minus(nu_term)
            },
            nu_to_invert,
        ))
    } else {
        cube.push(term::eq(
            nu_term,
            if typ.is_int() {
                term::int_zero()
            } else if typ.is_real() {
                term::real_zero()
            } else {
                bail!("unexpected addition over type {}", typ)
            },
        ))
    }

    Ok(true)
}

/// Inverts a datatype selector.
fn dtyp_slc_invert<'a>(
    term: Term,
    typ: &Typ,
    name: &str,
    inner: &'a Term,
    cube: &mut Vec<Term>,
    subst: &VarHMap<Term>,
    nu_subst: &VarHMap<Term>,
) -> bool {
    if let Some((inner, _)) = inner.subst_total(&(subst, nu_subst)) {
        cube.push(term::eq(term, term::dtyp_slc(typ.clone(), name, inner)));
        true
    } else {
        false
    }
}

/// Inverts a datatype tester.
fn dtyp_tst_invert<'a>(
    term: Term,
    name: &str,
    inner: &'a Term,
    cube: &mut Vec<Term>,
    subst: &VarHMap<Term>,
    nu_subst: &VarHMap<Term>,
) -> bool {
    if let Some((inner, _)) = inner.subst_total(&(subst, nu_subst)) {
        cube.push(term::eq(term, term::dtyp_tst(name, inner)));
        true
    } else {
        false
    }
}

/// Inverts a function application.
fn fun_invert<'a>(
    term: Term,
    name: &str,
    args: &'a [Term],
    cube: &mut Vec<Term>,
    subst: &VarHMap<Term>,
    nu_subst: &VarHMap<Term>,
) -> bool {
    let mut nu_args = Vec::with_capacity(args.len());
    for arg in args {
        if let Some((arg, _)) = arg.subst_total(&(subst, nu_subst)) {
            nu_args.push(arg)
        } else {
            return false;
        }
    }

    cube.push(term::eq(term, term::fun(name, nu_args)));

    true
}

/// Creates a fresh (hopefully) function name for a predicate.
fn make_fun_name(other_name: &str) -> Res<String> {
    let split: Vec<_> = other_name.split('|').collect();
    let str = match split.len() {
        1 => format!("{}_hoice_reserved_fun", other_name),
        3 if split[0] == "" && split[2] == "" && split[1] != "" => {
            format!("|{}_hoice_reserved_fun|", split[1])
        }
        _ => bail!("illegal symbol `{}`", other_name),
    };
    Ok(str)
}

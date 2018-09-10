//! Predicate-to-function reduction.
//!
//! This preprocessor attempts to reconstruct function definitions from Horn clauses. Functions are
//! reconstructed as multiple branches of an if-then-else.

use common::*;
use fun::RFun;
use instance::{info::VarInfo, instance::PreInstance, preproc::RedStrat, Clause};

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
        let (last, mut fresh) = if fun_args_len == rhs_args.len() {
            (None, rhs_args.len().into())
        } else {
            let last: VarIdx = (rhs_args.len() - 1).into();
            let mut fresh = last;
            fresh.inc();
            (Some(last), fresh)
        };

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

        macro_rules! get_fresh {
            () => {{
                let res = fresh;
                fresh.inc();
                res
            }};
        }

        debug_assert! { fun_args_len == rhs_args.len() || fun_args_len == rhs_args.len() - 1 }
        debug_assert! { lhs_preds.len() <= 1 }
        debug_assert! {
            if let Some((p, _)) = lhs_preds.iter().next() {
                * p == pred
            } else {
                true
            }
        }

        let (mut guard, mut subst) = if let Some(res) = args_invert(rhs_args, fun_args_len)? {
            res
        } else {
            log! { @3 "failed to invert rhs arguments {}", rhs_args }
            return Ok(None);
        };

        if_log! { @4
            log! { @4 |=>
                "rhs inversion successful" ;
                "  substitution:"
            }
            for (var, term) in subst.iter() {
                log! { @4 |=> "    v_{} -> {}", var, term }
            }
            log! { @4 |=> "  cube:" }
            for term in guard.iter() {
                log! { @4 "    {}", term }
            }
        }

        let mut lhs_argss: Vec<_> = lhs_preds
            .get(&pred)
            .map(|argss| argss.iter().collect())
            .unwrap_or_else(Vec::new);

        let mut nu_args = Vec::with_capacity(fun_args_len);
        let mut value = None;

        // Stores the recursive calls.
        let mut calls = VarHMap::new();

        macro_rules! register_call {
            ($call:expr) => {{
                // Check if we already have a binding for this call.
                let mut var = None;
                for (v, trm) in &calls {
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
                    let fresh = get_fresh!();
                    let prev = calls.insert(fresh, $call);
                    debug_assert! { prev.is_none() }
                    fresh
                }
            }};
        }

        while !lhs_argss.is_empty() {
            let prev_len = lhs_argss.len();
            let mut failed: Res<_> = Ok(false);

            lhs_argss.retain(|args| {
                for arg in &args[0..fun_args_len] {
                    if let Some((arg, _)) = arg.subst_total(&subst) {
                        nu_args.push(arg)
                    } else {
                        nu_args.clear();
                        return true;
                    }
                }
                let nu_args = ::std::mem::replace(&mut nu_args, Vec::with_capacity(fun_args_len));

                let fun_app = term::fun(fun_typ.clone(), fun_name.into(), nu_args);
                let fun_app_var = register_call!(fun_app);
                let fun_app = term::var(fun_app_var, fun_typ.clone());

                let okay = if let Some(last) = last.as_ref() {
                    let last = *last;
                    map_invert(&args[last], fun_app, &mut subst, &mut guard)
                } else {
                    value.get_or_insert_with(Vec::new).push(fun_app);
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
                return Ok(None);
            } else if lhs_argss.len() == prev_len {
                // not making progress.
                log! { @3 | "not making progress on lhs preds" }
                return Ok(None);
            }
        }

        if_log! { @4
            log! { @4 |=>
                "lhs inversion successful" ;
                "  substitution:"
            };
            for (var, term) in &subst {
                log! { @4 |=> "    v_{} -> {}", var, term }
            };
            log! { @4 |=> "  cube:" };
            for term in &guard {
                log! { @4 |=> "    {}", term }
            };
            log! { @4 |=> "  recursive calls:" };
            for (var, term) in & calls {
                log! { @4 |=> "    v_{} -> {}", var, term }
            }
        }

        for term in lhs_terms {
            if let Some((term, _)) = term.subst_total(&subst) {
                guard.insert(term);
            } else {
                log! { @3 | "total substitution failed on term {}", term }
                return Ok(None);
            }
        }

        if_log! { @4
            log! { @4 |=>
                "lhs terms substitution successful";
                "  cube:"
            }
            for term in &guard {
                log! { @4 |=> "    {}", term }
            };
        }

        let value = if let Some(last) = last.as_ref() {
            if let Some((res, _)) = rhs_args[*last].subst_total(&subst) {
                res
            } else {
                log! { @3 | "failed to retrieve value for {}", rhs_args[*last] }
                return Ok(None);
            }
        } else if let Some(conj) = value {
            term::and(conj)
        } else {
            term::tru()
        };

        log! { @4 | "value extraction successful: {}", value }

        let mut invar_subst = VarHMap::with_capacity(1);

        // Term elligible as candidate invariants are the ones that mention **exactly one**
        // variable from `calls`.
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
                invar_subst.insert(var, term::var(0, fun_typ.clone()));
                let (invar, _) = term
                    .subst_total(&invar_subst)
                    .expect("total substitution cannot fail due to previous checks");
                invars
                    .entry(invar)
                    .or_insert_with(Vec::new)
                    .push((index, term.clone()));
                false
            } else {
                true
            }
        });

        if_log! { @4
            log! { @4 |=>
                "potential invariant extraction successful";
                "  cube:"
            }
            for term in &guard {
                log! { @4 |=> "    {}", term }
            };
            log! { @4 |=> "  invariants:" };
            for invar in invars.keys() {
                log! { @4 |=> "    {}", invar }
            };
        }

        Ok(Some(FunBranch {
            guard,
            value,
            calls,
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
            self.calls.clear()
        }
    }
}

/// A function definition.
#[derive(Clone, Debug)]
struct FunDef {
    /// Predicate this function is for.
    pred: PrdIdx,
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
    pub fn new(pred: PrdIdx, name: String, sig: VarInfos, typ: Typ) -> Self {
        FunDef {
            pred,
            name,
            sig,
            typ,
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

        let mut subst = VarMap::with_capacity(1);

        'check_invariants: for (invariant, backtrack) in self.candidate_invars.drain() {
            solver!().comment_args(format_args!("checking candidate invariant {}", invariant))?;

            macro_rules! backtrack {
                () => {{
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
                    debug_assert! { subst.is_empty() }
                    subst.push(branch!().value.clone());

                    let invariant = invariant
                        .subst_total(&subst)
                        .expect("cannot fail by construction")
                        .0;

                    subst.clear();

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

                    for (var, _) in &branch!().calls {
                        debug_assert! { subst.is_empty() }
                        subst.push(term::var(*var, self.typ.clone()));
                        let invariant = invariant
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

                if sat {
                    log! { @3 | "  not an invariant: {}", invariant }
                    backtrack!()
                }

                instance.reset_solver()?;
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
    pub fn check_branches(&self, instance: &mut PreInstance) -> Res<bool> {
        let res = self.inner_check_branches(instance)?;
        instance.reset_solver()?;
        Ok(res)
    }

    /// Checks that all branches are exclusive and exhaustive.
    fn inner_check_branches(&self, instance: &mut PreInstance) -> Res<bool> {
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

        log! { @3 | "all branches are exclusive, checking they're exhaustive" }

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

        Ok(true)
    }

    /// Finalizes the function definition.
    pub fn finalize(mut self, instance: &mut PreInstance) -> Res<Option<Fun>> {
        self.check_invariants(instance)
            .chain_err(|| "while checking the invariants")?;

        let invs = self.invars.len();
        if invs > 0 {
            log! { @3 | "discovered {} invariant(s)", invs }
        }

        let okay = self
            .check_branches(instance)
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
            let subst: VarMap<_> = vec![term::fun(
                self.typ,
                self.name.clone(),
                self.sig
                    .into_iter()
                    .map(|info| term::var(info.idx, info.typ))
                    .collect(),
            )].into();

            for inv in self.invars {
                let inv = inv
                    .subst_total(&subst)
                    .expect("cannot fail by construction")
                    .0;

                invs.push(inv);
            }
        }

        // Build actual definition.
        let mut def = None;
        for branch in self.branches.into_iter().rev() {
            let mut nu_def = if let Some(def) = def {
                term::ite(
                    term::and(branch.guard.into_iter().collect()),
                    branch.value,
                    def,
                )
            } else {
                branch.value
            };
            def = Some(nu_def)
        }

        let def = def.ok_or("empty definitions during finalization in fun_preds")?;

        // Finally creating the function.
        let pred = self.pred;

        let mut dec = fun::retrieve_dec(&self.name)?;
        dec.set_def(def);
        dec.invariants.extend(invs);

        let fun = fun::mk(dec).chain_err(|| {
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

pub struct FunPreds;

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
        let last: Option<VarIdx> = if use_all_args {
            None
        } else {
            Some((instance[pred].sig.len() - 1).into())
        };

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

        let mut rfun = RFun::new(
            pred_fun_name.clone(),
            var_infos.clone(),
            pred_fun_typ.clone(),
        );
        rfun.set_synthetic(pred);

        fun::register_dec(rfun)?;

        macro_rules! abort {
            ($($stuff:tt)*) => {{
                let _ = fun::retrieve_dec(&pred_fun_name);
                return Ok(None);
            }};
        }

        let mut fun_def = FunDef::new(pred, pred_fun_name.clone(), var_infos, pred_fun_typ);

        for clause in instance.clauses_of(pred).1 {
            let clause = *clause;
            to_rm.push(clause);

            log! { @3 | "working on clause #{}", clause }

            fun_def = if let Some(new) = fun_def.register_clause(&instance[clause])? {
                new
            } else {
                log!{ @3 | "clause registration failed" }
                abort!()
            };
        }

        let fun = if let Some(fun) = fun_def.finalize(instance)? {
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
        let fun_app = term::fun(fun.typ.clone(), fun.name.clone(), args);

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
        FunPreds
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        let mut new_stuff = true;

        while new_stuff {
            new_stuff = false;

            if instance.active_pred_count() <= 1 {
                return Ok(info);
            }

            let mut to_inline: Vec<_> = instance
                .preds()
                .iter()
                .filter_map(|info| {
                    let inline = {
                        let pred = info.idx;

                        // Predicate is still unknown.
                        ! instance.is_known(pred)

          // When `pred` appears in the rhs of a clause, the lhs only mentions
          // `pred`.
          && instance.clauses_of(pred).1.iter().all(
            |clause| instance[* clause].lhs_preds().iter().all(
              |(p, _)| * p == pred
            )
          )

          // `pred` appears more than once in a clause where it's not alone.
          // && instance.clauses_of(pred).0.iter().any(
          //   |clause| instance[* clause].lhs_preds().get(
          //     & pred
          //   ).unwrap().len() > 1
          //   && (
          //     instance[* clause].lhs_preds().len() > 1
          //     || instance[* clause].rhs().map(
          //       |(p, _)| pred != * p
          //     ).unwrap_or(false)
          //   )
          // )

          // `pred` has only one dtyp argument (ignoring the last argument)
          && info.sig.len() > 1
          && info.sig[ 0 .. info.sig.len() - 1 ].iter().fold(
            0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc }
          ) <= 1
                    };

                    if inline {
                        Some(info.idx)
                    } else {
                        None
                    }
                }).collect();

            to_inline.sort_by(|p_1, p_2| {
                let adt_count_1 =
                    instance[*p_1]
                        .sig
                        .iter()
                        .fold(0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc });
                let adt_count_2 =
                    instance[*p_2]
                        .sig
                        .iter()
                        .fold(0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc });

                adt_count_1.cmp(&adt_count_2).reverse()
            });

            if to_inline.is_empty() {
                return Ok(info);
            }

            while let Some(pred) = to_inline.pop() {
                let res = FunPreds::reduce_pred(instance, pred, false)?;
                // pause("to resume fun_preds", & Profiler::new()) ;
                if let Some(red_info) = res {
                    new_stuff = true;
                    info += red_info;
                    break;
                } else {
                    // let res = FunPreds::reduce_pred(instance, pred, true)?;
                    // // pause("to resume fun_preds", & Profiler::new()) ;
                    // if let Some(red_info) = res {
                    //     new_stuff = true;
                    //     info += red_info;
                    //     break;
                    // }
                    ()
                }
            }
        }

        Ok(info)
    }
}

/// Builds a cube and a substitution corresponding to inverting some arguments.
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
/// Returns false if the invertion failed.
pub fn map_invert(
    to_invert: &Term,
    term: Term,
    subst: &mut VarHMap<Term>,
    cube: &mut TermSet,
) -> Res<bool> {
    debug_assert_eq! { to_invert.typ(), term.typ() }

    let mut nu_cube = vec![];
    let mut nu_subst = VarHMap::<Term>::new();

    let mut stack = vec![(term, to_invert.get())];

    while let Some((term, to_invert)) = stack.pop() {
        match to_invert {
            RTerm::DTypNew { typ, name, args } => {
                let selectors = typ.selectors_of(name)?;
                debug_assert_eq! { args.len(), selectors.len() }

                // `term` must be a specific variant: `name`
                nu_cube.push(term::dtyp_tst(name.clone(), term.clone()));

                for (arg, (slc, _)) in args.iter().zip(selectors.iter()) {
                    stack.push((term::dtyp_slc(arg.typ(), slc.clone(), term.clone()), arg))
                }
            }

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
            RTerm::CArray { term: inner, typ } => {
                stack.push((
                    // Array is constant, select any value.
                    term::select(term, typ.default_term()),
                    inner.get(),
                ))
            }

            RTerm::App { typ, op, args } => {
                match op {
                    Op::CMul => if args[0].val().is_some() {
                        let nu_term = if typ.is_int() {
                            // Current term modulo `val` is zero.
                            nu_cube.push(term::eq(
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
                        continue;
                    } else {
                        bail!("illegal CMul term {}", to_invert)
                    },

                    Op::Add => {
                        let mut subtraction = vec![term];
                        let mut not_substed = None;

                        for arg in args {
                            if let Some((term, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
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
                            nu_cube.push(term::eq(
                                nu_term,
                                if typ.is_int() {
                                    term::int_zero()
                                } else if typ.is_real() {
                                    term::real_zero()
                                } else {
                                    bail!("unexpected addition over type {}", typ)
                                },
                            ));
                        }
                        continue;
                    }

                    Op::Sub => {
                        let mut sub = None;
                        let mut add = vec![term];
                        let mut not_substed = None;

                        let mut first = true;
                        for arg in args {
                            if let Some((term, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
                                if first {
                                    debug_assert! { sub.is_none() }
                                    sub = Some(term)
                                } else {
                                    add.push(term)
                                }
                            } else if not_substed.is_some() {
                                return Ok(false);
                            } else {
                                // Careful of the polarity here vvvvv
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
                            nu_cube.push(term::eq(
                                nu_term,
                                if typ.is_int() {
                                    term::int_zero()
                                } else if typ.is_real() {
                                    term::real_zero()
                                } else {
                                    bail!("unexpected addition over type {}", typ)
                                },
                            ));
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

            RTerm::DTypSlc {
                typ,
                name,
                term: inner,
            } => if let Some((inner, _)) = inner.subst_total(&(&*subst, &nu_subst)) {
                nu_cube.push(term::eq(
                    term,
                    term::dtyp_slc(typ.clone(), name.clone(), inner),
                ))
            } else {
                return Ok(false);
            },

            RTerm::DTypTst {
                name, term: inner, ..
            } => if let Some((inner, _)) = inner.subst_total(&(&*subst, &nu_subst)) {
                nu_cube.push(term::eq(term, term::dtyp_tst(name.clone(), inner)))
            } else {
                return Ok(false);
            },

            RTerm::Fun { typ, name, args } => {
                let mut nu_args = Vec::with_capacity(args.len());
                for arg in args {
                    if let Some((arg, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
                        nu_args.push(arg)
                    } else {
                        return Ok(false);
                    }
                }

                nu_cube.push(term::eq(
                    term,
                    term::fun(typ.clone(), name.clone(), nu_args),
                ))
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

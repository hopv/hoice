//! Helper types and functions for preprocessing.

use crate::{common::*, var_to::terms::VarTermsSet};

use super::{PreInstance, RedStrat};

/// Result of extracting the terms for a predicate application in a clause.
#[derive(Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum ExtractRes<T = Vec<TTerm>> {
    /// The clause was found to be trivially true.
    Trivial,
    /// Terms could not be extracted.
    ///
    /// Returned when the variables appearing in the application and the other
    /// variables `others` of the clause are related, or if there is a predicate
    /// application mentioning variables from `others`.
    Failed,
    /// Success, predicate is equivalent to true.
    SuccessTrue,
    /// Success, predicate is equivalent to false.
    SuccessFalse,
    /// Success, predicate is equivalent to some top terms.
    Success(T),
}
impl<T: PartialEq + Eq> ExtractRes<T> {
    /// True if failed.
    pub fn is_failed(&self) -> bool {
        *self == ExtractRes::Failed
    }
}

/// Term extraction context.
pub struct ExtractionCxt {
    /// Map from **clause** variables to **predicate** variables.
    map: VarHMap<Term>,
    /// Quantified variables.
    qvars: VarHMap<Typ>,
    /// Index of the next fresh variable.
    fresh: VarIdx,
    /// True if quantifier generation is active.
    quantifiers: bool,
}
impl Default for ExtractionCxt {
    fn default() -> Self {
        Self::new()
    }
}
impl ExtractionCxt {
    /// Index of the next fresh variable.
    pub fn next_fresh(&mut self) -> VarIdx {
        let fresh = self.fresh;
        self.fresh.inc();
        fresh
    }

    /// Constructor.
    pub fn new() -> Self {
        ExtractionCxt {
            map: VarHMap::with_capacity(11),
            qvars: VarHMap::with_capacity(11),
            fresh: 0.into(),
            quantifiers: true,
        }
    }

    /// Creates quantified variables if needed.
    ///
    /// Returns `true` if the process failed.
    pub fn add_qvars(&mut self, var_info: &VarInfos, app_vars: &mut VarSet, vars: VarSet) -> bool {
        for var in vars {
            let is_new = app_vars.insert(var);

            if is_new {
                if !self.quantifiers {
                    return true;
                }
                let fresh = self.next_fresh();
                let _prev = self.qvars.insert(fresh, var_info[var].typ.clone());
                debug_assert_eq! { None, _prev }

                log! {
                  @6 "adding fresh {} for {}", fresh.default_str(), var_info[var]
                }
                let _prev = self
                    .map
                    .insert(var, term::var(fresh, var_info[var].typ.clone()));
                debug_assert_eq! { None, _prev }
            }
        }
        false
    }

    /// Applies a map to some predicate applications, generating quantifiers if
    /// necessary and `quantifiers` is true.
    ///
    /// Returns `None` on failure. Failure happens when some quantifiers are
    /// needed but `quantifiers` is false.
    fn args_of_pred_app(
        &mut self,
        var_info: &VarInfos,
        args: &VarTerms,
        app_vars: &mut VarSet,
    ) -> Res<TExtractRes<VarTerms>> {
        log! { @6 "args_of_pred_app ({})", self.quantifiers }
        let mut nu_args = VarMap::with_capacity(args.len());
        for arg in args.iter() {
            let abort = self.add_qvars(var_info, app_vars, term::vars(arg));
            if abort {
                return Ok(TExtractRes::Failed);
            }

            if let Some((nu_arg, _)) = arg.subst_total(&self.map) {
                nu_args.push(nu_arg)
            } else {
                bail!("unreachable, substitution was not total")
            }
        }
        Ok(TExtractRes::Success(nu_args.into()))
    }

    /// Applies a map to some predicate applications, generating quantifiers if
    /// necessary and `quantifiers` is true.
    ///
    /// The `pred` argument is a special predicate that will be skipped when
    /// handling `src`, but it's arguments will be returned.
    fn terms_of_pred_apps<'a>(
        &mut self,
        var_info: &VarInfos,
        src: &'a PredApps,
        tgt: &mut TTermSet,
        pred: PrdIdx,
        app_vars: &mut VarSet,
    ) -> Res<TExtractRes<Option<&'a VarTermsSet>>> {
        log! { @6 "terms_of_pred_apps" }
        let mut res = None;
        for (prd, argss) in src {
            let prd = *prd;
            if prd == pred {
                res = Some(argss);
                continue;
            }

            for args in argss {
                match self.args_of_pred_app(var_info, args, app_vars)? {
                    TExtractRes::Success(nu_args) => {
                        tgt.insert_pred_app(prd, nu_args);
                        ()
                    }
                    TExtractRes::Failed => {
                        log! { @6 "failed to extract argument {}", args }
                        return Ok(TExtractRes::Failed);
                    }
                }
            }
        }
        Ok(TExtractRes::Success(res))
    }

    /// Applies a map to some terms, generating quantifiers if necessary and `quantifiers` is true.
    ///
    /// Argument `even_if_disjoint` forces to add terms even if its variables are disjoint from
    /// `app_vars`.
    ///
    /// Returns `true` if one of the `src` terms is false (think `is_trivial`).
    fn terms_of_terms<'a, TermIter, Terms, F>(
        &mut self,
        var_info: &VarInfos,
        src: Terms,
        tgt: &mut TermSet,
        app_vars: &mut VarSet,
        even_if_disjoint: bool,
        f: F,
    ) -> Res<TExtractRes<bool>>
    where
        TermIter: Iterator<Item = &'a Term> + ExactSizeIterator,
        Terms: IntoIterator<IntoIter = TermIter, Item = &'a Term> + std::fmt::Debug,
        F: Fn(Term) -> Term,
    {
        log! { @5 | "terms_of_terms" }

        // Finds terms which variables are related to the ones from the predicate
        // applications.
        let src = src.into_iter();

        // The terms we're currently looking at.
        let mut lhs_terms_vec: Vec<_> = Vec::with_capacity(src.len());
        for term in src {
            match term.bool() {
                Some(true) => (),
                Some(false) => return Ok(TExtractRes::Success(true)),
                _ => lhs_terms_vec.push(term),
            }
        }
        // Terms which variables are disjoint from `app_vars` **for now**. This
        // might change as we generate quantified variables.
        let mut postponed: Vec<_> = Vec::with_capacity(lhs_terms_vec.len());

        // A fixed point is reached when we go through the terms in `lhs_terms_vec`
        // and don't generate quantified variables.
        loop {
            let mut fixed_point = true;

            for term in lhs_terms_vec.drain(0..) {
                log! { @6 "{}", term.to_string_info(var_info) ? }
                let vars = term::vars(term);

                if app_vars.len() == var_info.len() || vars.is_subset(&app_vars) {
                    let term = if let Some((term, _)) = term.subst_total(&self.map) {
                        term
                    } else {
                        bail!("[unreachable] failure during total substitution (1)")
                    };
                    log! { @6 "      sub {}", term }
                    tgt.insert(f(term));
                } else if !even_if_disjoint && vars.is_disjoint(&app_vars) {
                    log! { @6 "      disjoint" }
                    postponed.push(term)
                } else {
                    // The term mentions variables from `app_vars` and other variables.
                    // We generate quantified variables to account for them and
                    // invalidate `fixed_point` since terms that were previously disjoint
                    // might now intersect.
                    fixed_point = false;
                    let abort = self.add_qvars(var_info, app_vars, vars);
                    if abort {
                        return Ok(TExtractRes::Failed);
                    }

                    let term = if let Some((term, _)) = term.subst_total(&self.map) {
                        term
                    } else {
                        bail!("[unreachable] failure during total substitution (2)")
                    };
                    tgt.insert(f(term));
                }
            }

            if fixed_point || postponed.is_empty() {
                break;
            } else {
                // Iterating over posponed terms next.
                ::std::mem::swap(&mut lhs_terms_vec, &mut postponed)
            }
        }

        Ok(TExtractRes::Success(false))
    }

    /// Given a predicate application, returns the constraints on the input and a
    /// map from the variables used in the arguments to the variables of the
    /// predicate. Also returns the set of variables appearing in the
    /// application.
    ///
    /// # Assumptions
    ///
    /// - `self.map.is_empty()`
    ///
    /// # TODO
    ///
    /// - more doc with examples
    pub fn terms_of_app(
        &mut self,
        var_info: &VarInfos,
        instance: &Instance,
        pred: PrdIdx,
        args: &VarTerms,
    ) -> Res<Option<(TermSet, VarSet)>> {
        debug_assert! { self.map.is_empty() }

        log! { @5 | "terms of app to {}", args }

        let mut app_vars = VarSet::with_capacity(instance[pred].sig.len());
        let mut terms = TermSet::with_capacity(7);

        // Will store the arguments that are not a variable or a constant.
        let mut postponed = Vec::with_capacity(args.len());

        for (index, arg) in args.index_iter() {
            log! { @6 | "v_{} -> {}", index, arg }
            if let Some(var) = arg.var_idx() {
                log! { @6 | "  success" }
                let _ = app_vars.insert(var);
                if let Some(pre) = self.map.insert(var, term::var(index, arg.typ())) {
                    terms.insert(term::eq(term::var(index, arg.typ()), pre));
                }
            } else {
                log! { @6 | "  postponed" }
                match arg.as_val().to_term() {
                    Some(trm) => {
                        debug_assert_eq! { trm.typ(), arg.typ() }
                        let var = term::var(index, trm.typ());
                        terms.insert(term::eq(var, trm));
                    }
                    None => postponed.push((index, arg)),
                }
            }
        }

        log! { @6 | "postponed" }

        for (var, arg) in postponed {
            log! { @7 "v_{} -> {}", var, arg }

            if let Some((term, _)) = arg.subst_total(&self.map) {
                terms.insert(term::eq(term::var(var, arg.typ()), term));
            } else if let Some((v, inverted)) = arg.invert_var(var, arg.typ()) {
                let _prev = self.map.insert(v, inverted);
                debug_assert_eq!(_prev, None);
                let is_new = app_vars.insert(v);
                debug_assert!(is_new)
            } else if let TExtractRes::Failed = self.terms_of_terms(
                var_info,
                Some(arg),
                &mut terms,
                &mut app_vars,
                true,
                |term| term::eq(term::var(var, term.typ()), term),
            )? {
                log! { @6 | "failed to extract argument v_{}: {}", var, arg }
                return Ok(None);
            }
        }

        Ok(Some((terms, app_vars)))
    }

    /// Retrieves the internal quantified variables.
    pub fn get_qvars(&mut self) -> VarHMap<Typ> {
        self.qvars.shrink_to_fit();
        ::std::mem::replace(&mut self.qvars, VarHMap::with_capacity(11))
    }

    /// Argument `even_if_disjoint` forces to add terms even if its variables are disjoint from
    /// `app_vars`.
    fn terms_of_lhs_part<'a>(
        &mut self,
        instance: &Instance,
        var_info: &VarInfos,
        (lhs_terms, lhs_preds): (&TermSet, &'a PredApps),
        (pred, args): (PrdIdx, &VarTerms),
        even_if_disjoint: bool,
    ) -> Res<ExtractRes<(TTermSet, VarSet, Option<&'a VarTermsSet>)>> {
        log! { @5 "terms of lhs part" }

        let (terms, mut app_vars) =
            if let Some(res) = self.terms_of_app(var_info, instance, pred, args)? {
                res
            } else {
                log! { @5 "failed to extract terms of application" }
                return Ok(ExtractRes::Failed);
            };

        if_log! { @5
          log! { @5 => "terms:" }
          for term in & terms {
            log!{ @5 => "- {}", term }
          }
          log! { @5 => "map:" }
          for (var, term) in & self.map {
            log! { @5 => "- v_{} -> {}", var, term }
          }
          log! { @5 =>
            "working on lhs predicate applications ({})", lhs_preds.len()
          }
        }

        let mut tterms = TTermSet::of_terms(terms, lhs_preds.len());

        // Predicate applications need to be in the resulting term. Depending on
        // the definition they end up having, the constraint might be trivial.
        let pred_argss =
            match self.terms_of_pred_apps(var_info, lhs_preds, &mut tterms, pred, &mut app_vars)? {
                TExtractRes::Success(res) => res,
                TExtractRes::Failed => {
                    log! { @5 "qualifiers required for lhs pred apps, failing" }
                    return Ok(ExtractRes::Failed);
                }
            };

        log! { @5 "working on lhs terms ({})", lhs_terms.len() }

        if let TExtractRes::Success(trivial) = self.terms_of_terms(
            var_info,
            lhs_terms,
            tterms.terms_mut(),
            &mut app_vars,
            even_if_disjoint,
            identity,
        )? {
            if trivial {
                return Ok(ExtractRes::Trivial);
            }
        } else {
            log_debug! { "  could not extract terms of terms" }
            return Ok(ExtractRes::Failed);
        }

        Ok(ExtractRes::Success((tterms, app_vars, pred_argss)))
    }

    /// Returns the weakest predicate `p` such that `(p args) /\ lhs_terms /\
    /// {lhs_preds \ (p args)} => rhs`.
    ///
    /// Quantified variables are understood as universally quantified.
    ///
    /// The result is `(pred_app, pred_apps, terms)` which semantics is `pred_app
    /// \/ (not /\ tterms) \/ (not /\ pred_apps)`.
    pub fn terms_of_lhs_app(
        &mut self,
        quantifiers: bool,
        instance: &Instance,
        var_info: &VarInfos,
        (lhs_terms, lhs_preds): (&TermSet, &PredApps),
        rhs: Option<(PrdIdx, &VarTerms)>,
        (pred, args): (PrdIdx, &VarTerms),
        even_if_disjoint: bool,
    ) -> Res<ExtractRes<(Quantfed, Option<PredApp>, TTermSet)>> {
        log! { @4
          "terms_of_lhs_app on {} {} ({})", instance[pred], args, quantifiers
        }

        // Index of the first quantified variable: fresh for `pred`'s variables.
        self.fresh = instance[pred].fresh_var_idx();
        self.map.clear();
        self.quantifiers = quantifiers;

        // Predicate applications need to be in the resulting term. Depending on
        // the definition they end up having, the constraint might be trivial.
        let (tterms, mut app_vars) = match self.terms_of_lhs_part(
            instance,
            var_info,
            (lhs_terms, lhs_preds),
            (pred, args),
            even_if_disjoint,
        )? {
            ExtractRes::Success((tterms, app_vars, pred_argss)) => {
                match pred_argss.map(|argss| argss.len()).unwrap_or(0) {
                    1 => (tterms, app_vars),
                    len => bail!(
                        "illegal call to `terms_of_lhs_app`, \
                         predicate {} is applied {} times, expected 1",
                        instance[pred],
                        len
                    ),
                }
            }

            ExtractRes::SuccessTrue => return Ok(ExtractRes::SuccessTrue),
            ExtractRes::SuccessFalse => return Ok(ExtractRes::SuccessFalse),

            ExtractRes::Trivial => return Ok(ExtractRes::Trivial),

            ExtractRes::Failed => {
                log! { @5
                  "could not extract terms of predicate app ({})", instance[pred]
                }
                return Ok(ExtractRes::Failed);
            }
        };

        let pred_app = if let Some((pred, args)) = rhs {
            log! { @5 "working on rhs predicate application" }
            if let TExtractRes::Success(nu_args) =
                self.args_of_pred_app(var_info, args, &mut app_vars)?
            {
                Some((pred, nu_args))
            } else {
                log! { @5 "qualifiers required for rhs pred app, failing" }
                return Ok(ExtractRes::Failed);
            }
        } else {
            log! { @5 "no rhs predicate application" }
            None
        };

        debug_assert! { self.quantifiers || self.qvars.is_empty() }

        if pred_app.is_none() && tterms.is_empty() {
            Ok(ExtractRes::SuccessFalse)
        } else {
            let qvars = self.get_qvars();
            Ok(ExtractRes::Success((qvars, pred_app, tterms)))
        }
    }

    /// Returns the weakest predicate `p` such that `lhs_terms /\ lhs_preds => (p args)`.
    ///
    /// Quantified variables are understood as existentially quantified.
    ///
    /// The result is `(pred_apps, terms)` which semantics is `pred_app /\ tterms`.
    pub fn terms_of_rhs_app(
        &mut self,
        quantifiers: bool,
        instance: &Instance,
        var_info: &VarInfos,
        lhs_terms: &TermSet,
        lhs_preds: &PredApps,
        (pred, args): (PrdIdx, &VarTerms),
    ) -> Res<ExtractRes<(Quantfed, TTermSet)>> {
        log! { @4
          "terms of rhs app on {} {} ({})", instance[pred], args, self.quantifiers
        }

        // Index of the first quantified variable: fresh for `pred`'s variables.
        self.fresh = instance[pred].fresh_var_idx();
        self.map.clear();
        self.quantifiers = quantifiers;

        // Predicate applications need to be in the resulting term. Depending on
        // the definition they end up having, the constraint might be trivial.
        let tterms = match self.terms_of_lhs_part(
            instance,
            var_info,
            (lhs_terms, lhs_preds),
            (pred, args),
            false,
        )? {
            ExtractRes::Success((tterms, _, pred_argss)) => {
                if pred_argss.map(|argss| argss.is_empty()).unwrap_or(true) {
                    tterms
                } else {
                    bail!(
                        "illegal call to `terms_of_rhs_app`, \
                         predicate {} appears in the lhs",
                        instance[pred]
                    )
                }
            }

            ExtractRes::SuccessTrue => return Ok(ExtractRes::SuccessTrue),
            ExtractRes::SuccessFalse => return Ok(ExtractRes::SuccessFalse),

            ExtractRes::Trivial => return Ok(ExtractRes::Trivial),

            ExtractRes::Failed => {
                log! { @5
                  "could not extract terms of predicate app ({})", instance[pred]
                }
                return Ok(ExtractRes::Failed);
            }
        };

        debug_assert! { self.quantifiers || self.qvars.is_empty() }

        if tterms.is_empty() {
            Ok(ExtractRes::SuccessTrue)
        } else {
            let qvars = self.get_qvars();
            Ok(ExtractRes::Success((qvars, tterms)))
        }
    }
}

/// Results of term extraction.
pub enum TExtractRes<T> {
    /// Success.
    Success(T),
    /// Failure: need qualifiers.
    Failed,
}

/// Registers statistics of the original instance.
///
/// Dumps the instance if asked to do so.
pub fn register_stats(instance: &Instance, _profiler: &Profiler, count: usize) -> Res<()> {
    preproc_dump!(
        instance =>
            format!("preproc_{:0>4}_original_instance", count),
            "Instance before pre-processing."
    )?;
    profile! {
        |_profiler|
        "clause count original" => add instance.clauses().len()
    }
    profile! {
        |_profiler|
        "nl clause count original" => add {
            let mut count = 0 ;
            'clause_iter: for clause in instance.clauses() {
                for (_, argss) in clause.lhs_preds() {
                    if argss.len() > 1 {
                        count += 1 ;
                        continue 'clause_iter
                    }
                }
            }
            count
        }
    }
    profile! {
        |_profiler|
            "pred count original" => add {
                let mut count = 0 ;
                for pred in instance.pred_indices() {
                    if ! instance[pred].is_defined() {
                        count += 1
                    }
                }
                count
            }
    }
    profile! {
        |_profiler|
            "arg count original" => add {
                let mut args = 0 ;
                for info in instance.preds() {
                    if ! instance[info.idx].is_defined() {
                        args += info.sig.len()
                    }
                }
                args
            }
    }

    Ok(())
}

/// Registers some info for a preprocessor.
pub fn register_info(
    instance: &Instance,
    _profiler: &Profiler,
    preproc: &'static str,
    _red_info: &RedInfo,
    count: usize,
) -> Res<()> {
    preproc_dump!(
      instance =>
      format!("preproc_{:0>4}_{}", count, preproc),
      format!("Instance after running `{}`.", preproc)
    )?;

    profile! {
      |_profiler| format!(
        "{:>10}   pred red", preproc
      ) => add _red_info.preds
    }
    profile! {
      |_profiler| format!(
        "{:>10} clause red", preproc
      ) => add _red_info.clauses_rmed
    }
    profile! {
      |_profiler| format!(
        "{:>10} clause add", preproc
      ) => add _red_info.clauses_added
    }
    profile! {
      |_profiler| format!(
        "{:>10}    arg red", preproc
      ) => add _red_info.args_rmed
    }
    log! { @verb
      "{}: {}", conf.emph( preproc ), _red_info
    }
    Ok(())
}

/// Registers the final info, after preprocessing.
pub fn register_final_stats(instance: &Instance, _profiler: &Profiler) -> Res<()> {
    preproc_dump!(
      instance =>
        "preproc_0000_fixed_point",
        "Instance after reaching preproc fixed-point."
    )?;

    profile! {
      |_profiler|
        "clause count    final" => add instance.clauses().len()
    }
    profile! {
      |_profiler|
        "nl clause count    final" => add {
          let mut count = 0 ;
          'clause_iter: for clause in instance.clauses() {
            for (_, argss) in clause.lhs_preds() {
              if argss.len() > 1 {
                count += 1 ;
                continue 'clause_iter
              }
            }
          }
          count
        }
    }

    profile! {
      |_profiler|
        "pred count    final" => add {
          let mut count = 0 ;
          for pred in instance.pred_indices() {
            if ! instance[pred].is_defined() {
              count += 1
            }
          }
          count
        }
    }

    profile! {
      |_profiler|
        "arg count    final" => add {
          let mut args = 0 ;
          for info in instance.preds() {
            if ! instance[info.idx].is_defined() {
              args += info.sig.len()
            }
          }
          args
        }
    }

    Ok(())
}

/// Processes the information generated after a preprocessor run.
pub fn process_red_info(
    instance: &Instance,
    _profiler: &Profiler,
    preproc: &'static str,
    count: &mut usize,
    red_info: &RedInfo,
) -> Res<()> {
    if red_info.non_zero() {
        *count += 1;
        register_info(instance, _profiler, preproc, &red_info, *count)?;
        conf.check_timeout()?
    } else {
        log! { @verb "{}: did nothing", conf.emph(preproc) }
    }
    Ok(())
}

/// Checks whether an instance is solved.
///
/// Can return `Error::Unsat` if unsat, else returns a boolean indicating
/// whether the instance is solved.
pub fn check_solved(instance: &mut PreInstance, _profiler: &Profiler) -> Res<bool> {
    let res = if instance.is_solved() {
        if !instance.is_unsat() {
            profile! {
              |_profiler| tick "preproc", "final simplify"
            }
            // Check remaining clauses, maybe some of them are unsat.
            // println!("simplify all ({})", instance.clauses().len());
            match instance.simplify_all() {
                Ok(_) => (),
                Err(ref e) if e.is_unsat() => instance.set_unsat(),
                Err(e) => bail!(e),
            }
            profile! {
              |_profiler| mark "preproc", "final simplify"
            }
        }
        true
    } else {
        false
    };
    Ok(res)
}

/// Runs a technique, returns it's info.
///
/// Returns `None` if the instance is solved.
pub fn run_preproc<Strat: RedStrat>(
    instance: &mut PreInstance,
    _profiler: &Profiler,
    preproc: &mut Strat,
    count: &mut usize,
) -> Res<Option<RedInfo>> {
    profile! {
      |_profiler| tick "preproc", preproc.name()
    }
    log! { @verb
      "running {}", conf.emph( preproc.name() )
    }
    let red_info = preproc
        .apply(instance)
        .chain_err(|| format!("while running preprocessor {}", conf.bad(preproc.name())));
    profile! {
      |_profiler| mark "preproc", preproc.name()
    }

    let red_info = red_info?;

    process_red_info(instance, _profiler, preproc.name(), count, &red_info)?;

    if check_solved(instance, _profiler)? {
        Ok(None)
    } else {
        Ok(Some(red_info))
    }
}

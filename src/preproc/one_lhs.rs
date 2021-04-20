//! One lhs module.

use crate::{
    common::*,
    preproc::{utils::ExtractRes, PreInstance, RedStrat},
};

/// Tries to reduce predicates that appear as an antecedent in exactly one
/// clause.
///
/// For a predicate `p`, if the clause in question is
///
/// ```bash
/// lhs(v_1, ..., v_n) and p(v_1, ..., v_n) => rhs(v_1, ..., v_n)
/// ```
///
/// then `p` is reduced to
///
/// ```bash
/// (not lhs(v_1, ..., v_n)) or rhs(v_1, ..., v_n)
/// ```
///
/// **iff** `p` is the only predicate application in the clause, `lhs` is sat
/// and `(not rhs)` is sat.
///
/// If `lhs` or `(not rhs)` is unsat, then the clause is dropped and `p` is
/// reduced to `true` since it does not appear as an antecedent anywhere
/// anymore.
///
/// # Examples
///
/// ```
/// # use hoice::{ common::{ PrdIdx, PrdHMap }, parse, preproc::{ PreInstance, RedStrat, OneLhs } };
/// let mut instance = parse::instance("
///   (declare-fun p_1 ( Int ) Bool)
///   (assert
///     (forall ( (n Int) )
///       (=>
///         (p_1 n)
///         (> n 0)
///       )
///     )
///   )
/// ");
///
/// let mut one_lhs = OneLhs::new(& instance);
/// let mut instance = PreInstance::new(& mut instance).unwrap();
/// let info = one_lhs.apply(& mut instance).unwrap();
/// instance.finalize().unwrap();
/// assert_eq! { info.preds, 1 }
///
/// let pred: PrdIdx = 0.into();
/// assert_eq! { "p_1", & instance[pred].name }
///
/// let model = PrdHMap::new();
/// let model = instance.extend_model(model).unwrap();
/// let mut s: Vec<u8> = vec![];
/// instance.write_model(& model, & mut s).unwrap();
///
/// assert_eq! {
///     "\
/// (model
///   (define-fun p_1
///     ( (v_0 Int) ) Bool
///     (>= v_0 1)
///   )
/// )
/// \
///     ",
///     &String::from_utf8_lossy(&s)
/// }
/// ```
pub struct OneLhs {
    /// True if introducing quantifiers is okay.
    quantifiers: bool,
}

impl OneLhs {
    /// Logs an extraction result.
    fn log_extraction(
        &self,
        _instance: &Instance,
        _quantfed: &Quantfed,
        _pred_app: &Option<PredApp>,
        _tterms: &TTermSet,
    ) {
        if_log! { @4
            let mut s = "(".to_string() ;

            if ! _quantfed.is_empty() {
                s.push_str("exists (") ;
                for (var, sort) in _quantfed {
                    s.push_str(
                        & format!(" ({} {})", var.default_str(), sort)
                    )
                }
                s.push_str(" )\n(")
            }

            s.push_str("or\n") ;

            if let Some((pred, args)) = _pred_app {
                s.push_str("(") ;
                s.push_str(& _instance[* pred].name) ;
                for arg in args.iter() {
                    s.push_str( & format!(" {}", arg) )
                }
                s.push_str(")")
            }

            s.push_str("\n  (not\n    (and") ;

            for (pred, argss) in _tterms.preds() {
                for args in argss {
                    s.push_str(
                        & format!("\n      ({} {})", _instance[* pred], args)
                    )
                }
            }
            for term in _tterms.terms() {
                s.push_str(
                    & format!("\n      {}", term)
                )
            }

            s.push_str("\n    )\n  )") ;

            if ! _quantfed.is_empty() {
                s.push_str("\n)")
            }

            log!{ @4 "{}", s }
        }
    }

    /// Attemps to unfold a predicate that appears in exactly one LHS.
    ///
    /// Returns `None` if unfolding failed.
    fn work_on(
        &mut self,
        pred: PrdIdx,
        clause: ClsIdx,
        instance: &mut PreInstance,
    ) -> Res<Option<RedInfo>> {
        let extraction_res = {
            let (extraction, instance) = instance.extraction();
            let clause = &instance[clause];

            let args = if let Some(argss) = clause.lhs_preds().get(&pred) {
                let mut iter = argss.iter();
                // let args = iter.next().expect(
                //   "illegal clause lhs_preds, argument set is empty"
                // ) ;
                iter.next()
                    .expect("illegal clause lhs_preds, argument set is empty")

            // Predicate appears more than once in the LHS, aborting.
            // if false && iter.next().is_some() {
            //   return Ok(None)
            // } else {
            //   args
            // }
            } else {
                bail!("inconsistent instance state")
            };

            // Is the rhs an application of `pred`?
            match clause.rhs() {
                Some((p, _)) if p == pred => ExtractRes::SuccessTrue,
                _ => extraction.terms_of_lhs_app(
                    self.quantifiers,
                    instance,
                    clause.vars(),
                    (clause.lhs_terms(), clause.lhs_preds()),
                    clause.rhs(),
                    (pred, args),
                    true,
                )?,
            }
        };

        log! { @4
            "from {}",
            instance.clauses()[clause].to_string_info(instance.preds())?
        }
        log! { @2 | "unfolding {}", conf.emph(& instance[pred].name) }

        use self::ExtractRes::*;
        let info = match extraction_res {
            SuccessTrue => {
                log! { @4 "=> true" }
                instance.force_true(pred)?
            }
            SuccessFalse => {
                log! { @4 "=> false" }
                instance.force_false(pred)?
            }
            Trivial => {
                log! { @4 "=> trivial" }
                instance.force_true(pred)?
            }
            Success((qualfed, pred_app, tterms)) => {
                if pred_app.is_none() && tterms.is_empty() {
                    log! { @4 "=> false" }
                    instance.force_false(pred)?
                } else {
                    self.log_extraction(instance, &qualfed, &pred_app, &tterms);
                    instance.force_pred_right(pred, qualfed, pred_app, tterms)?
                }
            }
            Failed => return Ok(None),
        };

        Ok(Some(info))
    }
}

impl RedStrat for OneLhs {
    fn name(&self) -> &'static str {
        "one_lhs"
    }

    fn new(_: &Instance) -> Self {
        OneLhs { quantifiers: false }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut red_info = RedInfo::new();

        'all_preds: for pred in instance.pred_indices() {
            if instance[pred].is_defined() || instance.clauses_of(pred).0.len() > 1 {
                continue 'all_preds;
            }

            conf.check_timeout()?;

            let clause = if let Some(clause) = instance.clauses_of(pred).0.iter().next().cloned() {
                // Appears in exactly one lhs, let's do this.
                clause
            } else {
                log! {
                  @3 "{} does not appear in any lhs, forcing true", instance[pred]
                }
                red_info.preds += 1;
                red_info += instance.force_true(pred)?;
                continue 'all_preds;
            };

            // Skip if more than one application of the predicate.
            if instance[clause]
                .lhs_preds()
                .get(&pred)
                .map(|argss| argss.len() != 1)
                .unwrap_or(true)
            {
                continue 'all_preds;
            }

            log! { @3
              "looking at {} ({}, {})",
              instance[pred],
              instance.clauses_of(pred).0.len(),
              instance.clauses_of(pred).1.len(),
            }

            if let Some(info) = self.work_on(pred, clause, instance)? {
                red_info.preds += 1;
                red_info += info;
                instance.check("after unfolding (one_lhs)")?;
                debug_assert! { instance[pred].is_defined() }
            } else {
                log! { @4 "failed to unfold {}", instance[pred] }
            }
        }

        self.quantifiers = !self.quantifiers;

        Ok(red_info)
    }
}

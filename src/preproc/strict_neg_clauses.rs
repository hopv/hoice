//! Works on strict negative clause.

use common::*;
use preproc::{utils::ExtractRes, PreInstance, RedStrat};

/// Works on strict negative clause.
///
/// Extracts strengthening terms from strict negative clauses.
///
/// # Examples
///
/// ```
/// # use hoice::{ common::PrdIdx, parse, preproc::{ PreInstance, RedStrat, StrictNeg } };
/// let mut instance = parse::instance("
///   (declare-fun pred ( Int Int Int Int ) Bool)
///   (assert
///     (forall ( (x2 Int) (x3 Int) )
///       (=>
///         (and
///           (>= x2 1) (>= (+ x2 (* (- 1) x3)) 1)
///           (pred x2 0 (- 1) x3)
///         )
///         false
///       )
///     )
///   )
/// ");
///
/// let mut strict_neg = StrictNeg::new(& instance);
/// let mut instance = PreInstance::new(& mut instance).unwrap();
/// let info = strict_neg.apply(& mut instance).unwrap();
/// debug_assert! { ! info.non_zero() }
///
/// let pred: PrdIdx = 0.into();
/// debug_assert_eq! { "pred", & instance[pred].name }
///
/// let strengthening = instance[pred].strength().unwrap();
/// debug_assert_eq! {
///     "(or \
///         (>= (* (- 1) v_0) 0) \
///         (>= (+ v_3 (* (- 1) v_0)) 0) \
///         (not (= (+ (- 1) (* (- 1) v_2)) 0)) \
///         (not (= v_1 0))\
///     )", & format!("{}", strengthening)
/// }
/// ```
pub struct StrictNeg {
    /// Stores partial definitions for the predicates.
    partial_defs: PrdHMap<Option<Vec<Term>>>,
    /// Clauses to remove.
    clauses_to_rm: Vec<ClsIdx>,
}

impl StrictNeg {
    /// Builds the partial definitions by going through strict negative clauses.
    fn build_partial_defs(&mut self, instance: &mut PreInstance) -> Res<()> {
        debug_assert! { self.partial_defs.is_empty() }
        debug_assert! { self.clauses_to_rm.is_empty() }

        macro_rules! pdef {
            ($pred:expr => set false) => {{
                self.partial_defs.remove(&$pred);
                self.partial_defs.insert($pred, None);
                ()
            }};

            ($pred:expr => add $term:expr) => {{
                if let Some(vec) = self
                    .partial_defs
                    .entry($pred)
                    .or_insert_with(|| Some(Vec::new()))
                    .as_mut()
                {
                    vec.push($term)
                }
            }};
        }

        let (extractor, instance, strict_clauses) = instance.strict_neg_clauses();

        for (idx, clause) in strict_clauses {
            log! { @3 | "working on clause #{}", idx }
            log! { @5 "{}", clause.to_string_info(instance.preds()).unwrap() }

            let (pred, args) = if let Some((pred, argss)) = clause.lhs_preds().iter().next() {
                if let Some(args) = argss.iter().next() {
                    (*pred, args)
                } else {
                    bail!("inconsistent instance state")
                }
            } else {
                bail!("inconsistent instance state")
            };

            log! { @3 "rewriting clause" }

            let clause = clause
                .rewrite_clause_for_app(pred, args, 0.into())
                .chain_err(|| "during clause rewriting")?;
            log! { @3 | "rewriting successful" }
            log! { @5 "{}", clause.to_string_info(instance.preds()).unwrap() }

            let (pred, args) = if let Some((pred, argss)) = clause.lhs_preds().iter().next() {
                if let Some(args) = argss.iter().next() {
                    (*pred, args)
                } else {
                    bail!("inconsistent instance state")
                }
            } else {
                bail!("inconsistent instance state")
            };

            match extractor.terms_of_lhs_app(
                false,
                instance,
                clause.vars(),
                (clause.lhs_terms(), clause.lhs_preds()),
                clause.rhs(),
                (pred, args),
            )? {
                ExtractRes::Trivial | ExtractRes::SuccessTrue => self.clauses_to_rm.push(idx),

                ExtractRes::SuccessFalse => pdef!(pred => set false),

                ExtractRes::Success((qvars, pred_app, tterms)) => if qvars.is_empty() {
                    if pred_app.is_some() || !tterms.preds().is_empty() {
                        bail!("inconsistent instance state")
                    }

                    let terms = tterms.terms();

                    if terms.is_empty() {
                        pdef!(pred => set false)
                    } else {
                        let term =
                            term::or(terms.iter().map(|term| term::not(term.clone())).collect());
                        pdef!(pred => add term)
                    }
                },

                ExtractRes::Failed => (),
            }
        }

        Ok(())
    }
}

impl RedStrat for StrictNeg {
    fn name(&self) -> &'static str {
        "strict_neg"
    }

    fn new(_: &Instance) -> Self {
        StrictNeg {
            partial_defs: PrdHMap::new(),
            clauses_to_rm: Vec::new(),
        }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        self.build_partial_defs(instance)?;

        if !self.clauses_to_rm.is_empty() {
            info.clauses_rmed += self.clauses_to_rm.len();
            instance.forget_clauses(&mut self.clauses_to_rm)?
        }

        for (pred, terms_opt) in self.partial_defs.drain() {
            if let Some(mut terms) = terms_opt {
                log! { @3 "success ({} term(s))", terms.len() }
                if_log! { @4
                    for term in & terms {
                        log! { @4 |=> "{}", term }
                    }
                }
                if let Some(term) = instance.unset_strength(pred) {
                    terms.push(term.clone())
                }
                let conj = term::and(terms);
                match conj.bool() {
                    Some(true) => (),
                    Some(false) => {
                        info.preds += 1;
                        info += instance.force_false(pred)?
                    }
                    None => {
                        instance.set_strength(pred, conj)?;
                    }
                }
            } else {
                info.preds += 1;
                info += instance.force_false(pred)?
            }
        }

        Ok(info)
    }
}

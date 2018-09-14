//! Strict negative clause.

use common::*;
use instance::{
    instance::PreInstance,
    preproc::{utils::ExtractRes, RedStrat},
};

pub struct StrictNeg;

impl RedStrat for StrictNeg {
    fn name(&self) -> &'static str {
        "strict_neg"
    }

    fn new(_: &Instance) -> Self {
        StrictNeg
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        let mut partial_defs = PrdHMap::new();
        let mut clauses_to_rm = Vec::new();

        macro_rules! pdef {
            ($pred:expr => set false) => {{
                partial_defs.remove(&$pred);
                partial_defs.insert($pred, None);
                ()
            }};

            ($pred:expr => add $term:expr) => {{
                if let Some(vec) = partial_defs
                    .entry($pred)
                    .or_insert_with(|| Some(Vec::new()))
                    .as_mut()
                {
                    vec.push($term)
                }
            }};
        }

        {
            let (extractor, instance, strict_clauses) = instance.strict_neg_clauses();

            for (idx, clause) in strict_clauses {
                log! { @3 "working on clause #{}", idx }
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

                let clause = clause
                    .rewrite_clause_for_app(pred, args, 0.into())
                    .chain_err(|| "during clause rewriting")?;
                log! { @3 "rewriting successful" }
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
                    ExtractRes::Trivial | ExtractRes::SuccessTrue => clauses_to_rm.push(idx),

                    ExtractRes::SuccessFalse => pdef!(pred => set false),

                    ExtractRes::Success((qvars, pred_app, tterms)) => if qvars.is_empty() {
                        if pred_app.is_some() || !tterms.preds().is_empty() {
                            bail!("inconsistent instance state")
                        }

                        let terms = tterms.terms();

                        if terms.is_empty() {
                            pdef!(pred => set false)
                        } else {
                            let term = term::or(
                                terms.iter().map(|term| term::not(term.clone())).collect(),
                            );
                            pdef!(pred => add term)
                        }
                    },

                    ExtractRes::Failed => (),
                }
            }
        }

        if !clauses_to_rm.is_empty() {
            info.clauses_rmed += clauses_to_rm.len();
            instance.forget_clauses(&mut clauses_to_rm)?
        }

        for (pred, terms_opt) in partial_defs {
            if let Some(mut terms) = terms_opt {
                log! { @3 "success ({} term(s))", terms.len() }
                if_log! { @4
                    for term in & terms {
                        log! { @4 |=> "{}", term }
                    }
                }
                if let Some(term) = instance.get_str(pred) {
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
                        instance.set_str(pred, conj);
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

//! One rhs module.

use crate::{
    common::*,
    preproc::{utils::ExtractRes, PreInstance, RedStrat},
};

/// Works on predicates that appear in only one rhs.
///
/// # Examples
///
/// | Clause                             | `p v_0 v_1 =`               |
/// |:-----------------------------------|:----------------------------|
/// | `(v > v'  + 2)        => (p v v')` | `(v_0 > v_1 + 2)`           |
/// | `(v > 0)              => (p 7 v )` | `(v_0 = 7) and (v_1 > 0)`   |
/// | `(v > 0)              => (p 7 v')` | `(v_0 = 7)`                 |
/// | `(v > 0)              => (p v v )` | `(v_0 = v_1) and (v_0 > 0)` |
/// | `(v > 0) and (v <= 0) => (p 7 v')` | `false` (by check-sat)      |
///
/// ```
/// # use hoice::{ common::{ PrdIdx, PrdHMap }, parse, preproc::{ PreInstance, RedStrat, OneRhs } };
/// let mut instance = parse::instance("
///   (declare-fun p_1 ( Int ) Bool)
///   (assert
///     (forall ( (n Int) )
///       (=>
///         (> n 0)
///         (p_1 n)
///       )
///     )
///   )
/// ");
///
/// let mut one_rhs = OneRhs::new(& instance);
/// let mut instance = PreInstance::new(& mut instance).unwrap();
/// let info = one_rhs.apply(& mut instance).unwrap();
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
pub struct OneRhs {
    /// True if introducing quantifiers is okay.
    quantifiers: bool,
}

impl OneRhs {
    /// Logs an extraction result.
    fn log_extraction(&self, _instance: &Instance, _quantfed: &Quantfed, _tterms: &TTermSet) {
        if_log! { @4
          let mut s = "(".to_string() ;

          if ! _quantfed.is_empty() {
            s.push_str("exists") ;
            for (var, sort) in _quantfed {
              s.push_str(
                & format!(" ({} {})", var.default_str(), sort)
              )
            }
            s.push_str(" )\n(")
          }

          s.push_str("and\n") ;

          for (pred, argss) in _tterms.preds() {
            for args in argss {
              s.push_str(
                & format!("  ({} {})\n", _instance[* pred], args)
              )
            }
          }
          for term in _tterms.terms() {
            s.push_str( & format!("  {}\n", term) )
          }

          if ! _quantfed.is_empty() {
            s.push_str(") ")
          }
          s.push_str(")") ;

          log! { @4 "{}", s }
        }
    }

    /// Attemps to unfold a predicate that appears in exactly one RHS.
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

            if let Some((_this_pred, args)) = clause.rhs() {
                debug_assert_eq!(pred, _this_pred);

                // Does `pred` appear in the lhs?
                match clause.lhs_preds().get(&pred) {
                    Some(apps) if !apps.is_empty() => ExtractRes::SuccessFalse,
                    _ => extraction.terms_of_rhs_app(
                        self.quantifiers,
                        instance,
                        clause.vars(),
                        clause.lhs_terms(),
                        clause.lhs_preds(),
                        (pred, args),
                    )?,
                }
            } else {
                bail!("inconsistent instance state")
            }
        };

        log! { @4
            "from {}",
            instance.clauses()[clause].to_string_info(instance.preds()).unwrap()
        }
        log! { @2 | "unfolding {}", conf.emph(& instance[pred].name) }

        use self::ExtractRes::*;
        let info = match extraction_res {
            Trivial => {
                log! { @ 4 | "=> trivial" }
                instance.force_false(pred)?
            }

            SuccessTrue => {
                log! { @ 4 | "=> true" }
                instance.force_true(pred)?
            }
            SuccessFalse => {
                log! { @ 4 | "=> false" }
                instance.force_false(pred)?
            }

            Success((qvars, tterms)) => {
                self.log_extraction(instance, &qvars, &tterms);
                instance.force_pred_left(pred, qvars, tterms)?
            }

            Failed => return Ok(None),
        };

        Ok(Some(info))
    }
}

impl RedStrat for OneRhs {
    fn name(&self) -> &'static str {
        "one_rhs"
    }

    fn new(_: &Instance) -> Self {
        OneRhs { quantifiers: false }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut red_info = RedInfo::new();

        'all_preds: for pred in instance.pred_indices() {
            if instance[pred].is_defined() || instance.clauses_of(pred).1.len() > 1 {
                continue 'all_preds;
            }

            conf.check_timeout()?;

            let clause = if let Some(clause) = instance.clauses_of(pred).1.iter().next().cloned() {
                // Appears in exactly on lhs, let's do this.
                clause
            } else {
                log! {
                  @3 "{} does not appear in any rhs, forcing false", instance[pred]
                }
                red_info.preds += 1;
                red_info += instance.force_false(pred)?;
                continue 'all_preds;
            };

            log! { @3
              "looking at {} ({}, {})",
              instance[pred],
              instance.clauses_of(pred).0.len(),
              instance.clauses_of(pred).1.len(),
            }

            if let Some(info) = self.work_on(pred, clause, instance)? {
                red_info.preds += 1;
                red_info += info;
                instance.check("after unfolding (one_rhs)")?;
                debug_assert! { instance[pred].is_defined() }
            } else {
                log! { @4 "failed to unfold {}", instance[pred] }
            }
        }

        self.quantifiers = !self.quantifiers;

        Ok(red_info)
    }
}

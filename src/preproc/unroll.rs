//! Bias unrolling module.

use crate::{
    common::*,
    preproc::{
        utils::{ExtractRes, ExtractionCxt},
        PreInstance, RedStrat,
    },
};

// /// Unrolls positive constraints once.
// pub struct Unroll {
//   max_new_clauses: usize,
//   ignore: PrdSet,
// }

// impl RedStrat for Unroll {
//   fn name(& self) -> & 'static str { "unroll" }

//   fn new(instance: & Instance) -> Self {
//     Unroll {
//       max_new_clauses: ::std::cmp::max(
//         5, instance.preds().len() + instance.clauses().len() * 5 / 100
//       ),
//       ignore: PrdSet::new(),
//     }
//   }

//   fn apply<'a>(
//     & mut self, instance: & mut PreInstance<'a>
//   ) -> Res<RedInfo> {

//     let mut prd_map: PrdHMap<
//       Vec<(Option<Quant>, TTermSet)>
//     > = PrdHMap::with_capacity(17) ;

//     scoped! {

//       let (extractor, instance) = instance.extraction() ;

//       'pos_clauses: for clause in instance.clauses() {

//         if ! clause.lhs_preds().is_empty() {
//           continue 'pos_clauses
//         }

//         conf.check_timeout() ? ;

//         if let Some((pred, args)) = clause.rhs() {
//           if self.ignore.contains(& pred) {
//             continue 'pos_clauses
//           }
//           match extractor.terms_of_rhs_app(
//             true, instance, & clause.vars,
//             clause.lhs_terms(), clause.lhs_preds(),
//             (pred, args)
//           ) ? {
//             ExtractRes::Success((q, ts)) => insert(
//               pred, Quant::forall(q), ts
//             ),
//             ExtractRes::SuccessTrue => {
//               let mut set = TTermSet::new() ;
//               set.insert_term( term::tru() ) ;
//               insert(
//                 pred, None, set
//               )
//             },
//             ExtractRes::Failed => continue 'pos_clauses,
//             ExtractRes::Trivial => bail!(
//               "found a trivial clause during unrolling"
//             ),
//             ExtractRes::SuccessFalse => bail!(
//               "found a predicate equivalent to false during unrolling"
//             ),
//           }
//         }

//       }
//     }

//     let mut info = RedInfo::new() ;
//     for (pred, terms) in prd_map {
//       // Anticipate blowup.
//       let appearances = instance.clauses_of(pred).0.len() ;
//       if terms.len() * appearances >= self.max_new_clauses {
//         let is_new = self.ignore.insert(pred) ;
//         debug_assert! { is_new }
//         log! { @verb
//           "not unrolling {}, {} variant(s), estimation: {} new clauses",
//           conf.emph(& instance[pred].name),
//           terms.len(),
//           terms.len() * appearances
//         }
//       } else {
//         log! { @verb
//           "unrolling {}, {} variant(s)",
//           conf.emph(& instance[pred].name),
//           terms.len()
//         }
//         info += instance.unroll(pred, & terms) ?
//       }
//     }
//     Ok(info)
//   }
// }

/// Reverse-unrolls negative constraints once.
pub struct RUnroll {
    max_new_clauses: usize,
    ignore: PrdSet,
}

impl RUnroll {
    /// Reverse unrolls a clause.
    fn runroll_clause(
        &mut self,
        instance: &Instance,
        clause: &Clause,
        extractor: &mut ExtractionCxt,
        pred_map: &mut PrdHMap<Vec<(Option<Quant>, TermSet)>>,
    ) -> Res<()> {
        macro_rules! insert {
            ($pred:expr, $q:expr, $ts:expr) => {
                pred_map
                    .entry($pred)
                    .or_insert_with(Vec::new)
                    .push(($q, $ts))
            };
        }

        if clause.rhs().is_some() {
            return Ok(());
        }

        conf.check_timeout()?;

        let mut apps = clause.lhs_preds().iter();

        let (pred, argss) = if let Some((pred, argss)) = apps.next() {
            (pred, argss)
        } else {
            return Ok(());
        };

        if self.ignore.contains(&pred) {
            return Ok(());
        }

        let pred = *pred;
        let mut argss = argss.iter();
        let args = if let Some(args) = argss.next() {
            args
        } else {
            bail!("illegal clause, predicate application leads to nothing")
        };

        if argss.next().is_some() || apps.next().is_some() {
            return Ok(());
        }

        // Negative constraint with only one pred app, reverse-unrolling.
        match extractor.terms_of_lhs_app(
            true,
            instance,
            &clause.vars,
            (clause.lhs_terms(), &PredApps::with_capacity(0)),
            None,
            (pred, args),
            false,
        )? {
            ExtractRes::Success((q, apps, ts)) => {
                debug_assert! { apps.is_none() }
                let (terms, pred_apps) = ts.destroy();
                if_log! { @3
                    let mut s = format!(
                        "from {}\n", clause.to_string_info(instance.preds()).unwrap()
                    ) ;
                    s.push_str("terms {\n") ;

                    for term in & terms {
                        s.push_str( & format!("  {}\n", term) )
                    }
                    s.push_str("}\npred apps {{") ;

                    for (pred, argss) in & pred_apps {
                        for args in argss {
                            s.push_str( & format!("  ({}", instance[* pred]) ) ;
                            for arg in args.iter() {
                                s.push_str( & format!(" {}", arg) )
                            }
                            s.push_str(")\n")
                        }
                    }
                    s.push_str(")") ;
                    log! { @3 "{}", s }
                }
                debug_assert! { pred_apps.is_empty() }
                insert!(pred, Quant::exists(q), terms)
            }
            ExtractRes::SuccessFalse => {
                let set = TermSet::new();
                insert!(pred, None, set)
            }
            ExtractRes::Failed => log! {
              @3 "extraction failed, skipping"
            },
            ExtractRes::Trivial => bail!("found a trivial clause during unrolling"),
            ExtractRes::SuccessTrue => {
                bail!("found a predicate equivalent to true during reverse-unrolling")
            }
        }

        Ok(())
    }
}

impl RedStrat for RUnroll {
    fn name(&self) -> &'static str {
        "runroll"
    }

    fn new(instance: &Instance) -> Self {
        RUnroll {
            max_new_clauses: ::std::cmp::max(
                5,
                instance.preds().len() + instance.clauses().len() * 5 / 100,
            ),
            ignore: PrdSet::new(),
        }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut prd_map: PrdHMap<Vec<(Option<Quant>, TermSet)>> = PrdHMap::with_capacity(17);

        scoped! {
          let (extractor, instance) = instance.extraction() ;
          for clause in instance.clauses() {
            self.runroll_clause(
              instance, clause, extractor, & mut prd_map
            ) ?
          }
        }

        let mut info = RedInfo::new();
        for (pred, terms) in prd_map {
            // Anticipate blowup.
            let appearances = instance.clauses_of(pred).0.len();
            if appearances >= self.max_new_clauses {
                let is_new = self.ignore.insert(pred);
                debug_assert! { is_new }
                log! { @verb
                  "not r_unrolling {}, {} occurence(s), \
                  estimation: {} new clauses (>= {})",
                  conf.emph(& instance[pred].name),
                  appearances,
                  terms.len() * appearances,
                  self.max_new_clauses,
                }
            } else {
                log! { @verb
                  "r_unrolling {}, {} variant(s)",
                  conf.emph(& instance[pred].name),
                  terms.len()
                }
                info += instance.reverse_unroll(pred, &terms)?
            }
        }
        Ok(info)
    }
}

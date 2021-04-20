//! Works on strict negative clause.

use crate::{
    common::*,
    preproc::{utils::ExtractRes, PreInstance, RedStrat},
};

/// Works on strict negative clause.
///
/// Extracts strengthening terms from strict negative clauses. Note that in some cases, this
/// preprocessor can completely solve the instance. See examples below.
///
/// This preprocessor goes through the strict negative clauses (negative clauses with only one
/// predicate application) for each predicate `p` and extracts a term where `p v_0 ... v_n` needs
/// to be false according to the clause. Such a term `t` is called *strengthening* since, during
/// the learning process, any candidate `c` created by the learner will be strengthened to `(and t
/// c)`.
///
/// Then, if we have strengthening terms for all predicates, this preprocessor will check whether
/// these terms taken as definitions verify all the clauses. If they do then the instance is solved
/// (see second example below).
///
/// # Examples
///
/// ```
/// # use hoice::{ common::*, parse, preproc::{ PreInstance, RedStrat, StrictNeg } };
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
///   (assert
///     (forall ( (x0 Int) (x1 Int) (x2 Int) (x3 Int) )
///       (=>
///         (and
///             true
///         )
///         (pred x0 x1 x2 x3)
///       )
///     )
///   )
///   (assert
///     (forall ( (x2 Int) (x3 Int) )
///       (=>
///         (and
///             (pred 0 0 x2 x3)
///             (>= (+ x2 x3) 0)
///         )
///         (pred 7 7 7 x3)
///       )
///     )
///   )
/// ");
///
/// let mut strict_neg = StrictNeg::new(& instance);
/// let mut instance = PreInstance::new(& mut instance).unwrap();
/// let info = strict_neg.apply(& mut instance).unwrap();
/// assert! { info.non_zero() }
///
/// let pred: PrdIdx = 0.into();
/// assert_eq! { "pred", & instance[pred].name }
///
/// println!("is solved: {}", instance.is_solved());
/// let strengthening = instance[pred].strength().unwrap();
/// println!("aaa");
/// let expected = "(or \
///     (>= (* (- 1) v_0) 0) \
///     (not (= v_1 0)) \
///     (>= (+ (* (- 1) v_0) v_3) 0) \
///     (not (= (+ (- 1) (* (- 1) v_2)) 0))\
/// )";
/// let info: VarMap<_> = vec![
///     ::hoice::info::VarInfo::new("v_0", typ::int(), 0.into()),
///     ::hoice::info::VarInfo::new("v_1", typ::int(), 1.into()),
///     ::hoice::info::VarInfo::new("v_2", typ::int(), 2.into()),
///     ::hoice::info::VarInfo::new("v_3", typ::int(), 3.into()),
/// ].into_iter().collect();
/// let expected = &::hoice::parse::term(expected, &info, &instance);
/// assert_eq! { expected, strengthening }
/// ```
///
/// Example where the strengthening term is enough to conclude:
///
/// ```
/// # use hoice::{ parse, preproc::{ PreInstance, RedStrat, StrictNeg } };
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
///   (assert
///     (forall ( (x3 Int) )
///       (=>
///         (and
///             (>= x3 0)
///         )
///         (pred 7 7 7 x3)
///       )
///     )
///   )
///   (assert
///     (forall ( (x2 Int) (x3 Int) )
///       (=>
///         (and
///             (pred 0 0 x2 x3)
///             (>= (+ x2 x3) 0)
///         )
///         (pred 7 7 7 x3)
///       )
///     )
///   )
/// ");
///
/// let mut strict_neg = StrictNeg::new(& instance);
/// let mut instance = PreInstance::new(& mut instance).unwrap();
/// let info = strict_neg.apply(& mut instance).unwrap();
/// assert! { info.non_zero() }
/// assert! { instance.is_solved() }
/// ```
pub struct StrictNeg {
    /// Stores partial definitions for the predicates.
    partial_defs: PrdHMap<Option<Vec<(Quantfed, Term)>>>,
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

            ($pred:expr => add $quant:expr, $term:expr) => {{
                if let Some(vec) = self
                    .partial_defs
                    .entry($pred)
                    .or_insert_with(|| Some(Vec::new()))
                    .as_mut()
                {
                    vec.push(($quant, $term))
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
                true,
                instance,
                clause.vars(),
                (clause.lhs_terms(), clause.lhs_preds()),
                clause.rhs(),
                (pred, args),
                false,
            )? {
                ExtractRes::Trivial | ExtractRes::SuccessTrue => self.clauses_to_rm.push(idx),

                ExtractRes::SuccessFalse => pdef!(pred => set false),

                ExtractRes::Success((qvars, pred_app, tterms)) => {
                    if pred_app.is_some() || !tterms.preds().is_empty() {
                        bail!("inconsistent instance state")
                    }

                    let terms = tterms.terms();

                    if terms.is_empty() {
                        pdef!(pred => set false)
                    } else {
                        let term =
                            term::or(terms.iter().map(|term| term::not(term.clone())).collect());
                        pdef!(pred => add qvars, term)
                    }
                }

                ExtractRes::Failed => (),
            }
        }

        Ok(())
    }

    /// Checks whether the partial definitions are legal definitions for the predicates.
    ///
    /// If successful, meaning the instance is solved, forces all the predicates and returns
    /// `true`. Returns `false` otherwise.
    fn check_defs(&mut self, instance: &mut PreInstance) -> Res<(bool, RedInfo)> {
        let mut info = RedInfo::new();

        if instance
            .preds()
            .iter()
            .any(|pred| !pred.is_defined() && !self.partial_defs.get(&pred.idx).is_some())
        {
            return Ok((false, info));
        }

        // println!("clause count: {}", instance.clauses().len());

        log! { @3 "partial definitions cover all predicates" }
        info.preds += self.partial_defs.len();

        // let mut all_clauses: Vec<_> = instance
        //     .clauses()
        //     .index_iter()
        //     .map(|(idx, _)| idx)
        //     .collect();

        // instance.forget_clauses(&mut all_clauses)?;

        // println!(
        //     "clause count: {}, def count: {}",
        //     instance.clauses().len(),
        //     self.partial_defs.len()
        // );

        let solved = instance
            .check_pred_partial_defs(
                self.partial_defs
                    .iter()
                    .map(|(pred, opt)| (*pred, opt.as_ref().unwrap())),
            )
            .chain_err(|| "while checking partial definitions")?;

        if !solved {
            return Ok((false, info));
        }

        // Building the actual definitions.
        let mut defs = Vec::with_capacity(self.partial_defs.len());

        for (pred, def) in self.partial_defs.drain() {
            let mut fresh: VarIdx = instance[pred].sig().len().into();
            let def = def.unwrap();
            let mut qvars = VarHMap::new();
            let mut term = term::tru();

            // macro_rules! display {
            //     () => {{
            //         print!("  (forall (");
            //         for (var, typ) in &qvars {
            //             print!(" ({} {})", var.default_str(), typ)
            //         }
            //         println!(" )");
            //         println!("    {}", term);
            //         println!("  )")
            //     }};
            // }

            // println!("definition for {}", instance[pred]);
            for (q, t) in def {
                let mut map = VarHMap::new();
                // print!("  (forall (");
                for (var, typ) in q {
                    // print!(" ({} {})", var.default_str(), typ);
                    map.insert(var, term::var(fresh, typ.clone()));
                    let var = fresh;
                    fresh.inc();
                    // print!("->{}", var.default_str());
                    let prev = qvars.insert(var, typ);
                    debug_assert_eq! { prev, None }
                }
                // println!(" )");
                // println!("    {}", t);
                // println!("  )");

                let t = if !map.is_empty() { t.subst(&map).0 } else { t };
                term = term::and(vec![term, t]);

                // display!()
            }

            let mut tterms = TTermSet::new();
            let is_new = tterms.insert_term(term);
            debug_assert! { is_new }
            defs.push((pred, vec![(qvars, tterms)]));
            // instance.force_pred_right(pred, qvars, None, tterms)?;

            // println!("rewritten as");
            // display!()
        }

        if solved {
            let (okay, nu_info) = instance
                .force_all_preds(defs, true)
                .chain_err(|| "while forcing all predicates")?;
            info += nu_info;
            debug_assert! { okay }
        }

        Ok((solved, info))
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

        let mut false_preds = None;
        self.partial_defs.retain(|pred, opt| {
            if opt.is_none() {
                false_preds.get_or_insert_with(|| vec![]).push(*pred);
                false
            } else {
                true
            }
        });

        if let Some(false_preds) = false_preds {
            for pred in false_preds {
                info.preds += 1;
                info += instance.force_false(pred)?
            }
        }

        // Do we have partial definitions for all the predicates?
        let (solved, nu_info) = self.check_defs(instance)?;
        info += nu_info;
        if solved {
            return Ok(info);
        }

        for (pred, terms_opt) in self.partial_defs.drain() {
            if let Some(mut terms) = terms_opt {
                log! { @3 "success ({} term(s))", terms.len() }
                if_log! { @4
                    for (quant, term) in & terms {
                        log! { @4 |=> "{} ({} quantified variable(s))", term, quant.len() }
                    }
                }
                if let Some(term) = instance.unset_strength(pred) {
                    terms.push((Quantfed::new(), term.clone()))
                }
                let mut conj = Vec::with_capacity(terms.len());
                for (q, t) in terms {
                    if q.is_empty() {
                        conj.push(t)
                    }
                }
                let conj = term::and(conj);
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

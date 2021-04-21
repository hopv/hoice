//! Bias unrolling module.

use crate::{
    common::*,
    preproc::{
        utils::{ExtractRes, ExtractionCxt},
        PreInstance, RedStrat,
    },
};

type NegDef = (Quantfed, TermSet);
type NegDefs = Vec<NegDef>;
type PosDef = (Quantfed, TermSet);
type PosDefs = Vec<PosDef>;
type IndexedArgs = Vec<(VarTerms, usize)>;

/// Unrolls negative and positive constraints with a bias.
///
/// # TODO
///
/// - when creating new clauses for `p`, remember that `p` has new pos/neg
///   definitions ; then, only check clauses that mention new predicates (old
///   ones have already been tried)
pub struct BiasedUnroll {
    /// Predicates appearing in positive clauses.
    in_pos_clauses: PrdSet,
    /// Predicates appearing in negative clauses.
    in_neg_clauses: PrdSet,
    /// Predicates not appearing in positive clauses.
    not_in_pos_clauses: PrdSet,
    /// Predicates not appearing in negative clauses.
    not_in_neg_clauses: PrdSet,
    /// Positive definitions retrieved from positive clauses.
    pos_defs: PrdHMap<PosDefs>,
    /// Negative definitions retrieved from negative clauses.
    neg_defs: PrdHMap<NegDefs>,
    ///
    pos_new_preds: PrdHMap<(PrdSet, PrdSet)>,
    neg_new_preds: PrdHMap<(PrdSet, PrdSet)>,
    /// Maximum number of new clauses we can create by predicate.
    max_new_clauses: usize,
}

impl BiasedUnroll {
    /// Adds a positive definition for something.
    fn add_pos_def_for(&mut self, pred: PrdIdx, def: PosDef) {
        let defs = self.pos_defs.entry(pred).or_insert_with(|| vec![]);
        if defs.iter().all(|d| d != &def) {
            defs.push(def)
        }
    }

    /// Adds a negative definition for something.
    fn add_neg_def_for(&mut self, pred: PrdIdx, def: NegDef) {
        let defs = self.neg_defs.entry(pred).or_insert_with(|| vec![]);
        if defs.iter().all(|d| d != &def) {
            defs.push(def)
        }
    }

    /// Prints itself.
    #[allow(dead_code)]
    fn print(&self, instance: &Instance) {
        println!("pos {{");
        for pred in &self.in_pos_clauses {
            println!("  + {}", instance[*pred])
        }
        for pred in &self.not_in_pos_clauses {
            println!("  - {}", instance[*pred])
        }
        println!("}}");
        println!("neg {{");
        for pred in &self.in_neg_clauses {
            println!("  + {}", instance[*pred])
        }
        for pred in &self.not_in_neg_clauses {
            println!("  - {}", instance[*pred])
        }
        println!("}}");

        for (pred, defs) in &self.pos_defs {
            if !defs.is_empty() {
                println!("+ {} {{", instance[*pred]);
                for (qvars, terms) in defs {
                    let (pref, end) = if qvars.is_empty() {
                        ("", "")
                    } else {
                        print!("  (exists (");
                        for (qvar, typ) in qvars {
                            print!(" ({} {})", qvar.default_str(), typ)
                        }
                        println!(" )");
                        ("  ", "  )\n")
                    };
                    print!("  {}(and", pref);
                    for term in terms {
                        print!(" {}", term)
                    }
                    println!(")");
                    print!("{}", end)
                }
                println!("}}")
            }
        }

        for (pred, defs) in &self.neg_defs {
            if !defs.is_empty() {
                println!("- {} {{", instance[*pred]);
                for (qvars, terms) in defs {
                    let (pref, end) = if qvars.is_empty() {
                        ("", "")
                    } else {
                        print!("  (forall (");
                        for (qvar, typ) in qvars {
                            print!(" ({} {})", qvar.default_str(), typ)
                        }
                        println!(" )");
                        ("  ", "  )\n")
                    };
                    print!("  {}(not (and", pref);
                    for term in terms {
                        print!(" {}", term)
                    }
                    println!(") )");
                    print!("{}", end)
                }
                println!("}}")
            }
        }

        println!("pos_new_preds {{");
        for (pred, (pos, neg)) in &self.pos_new_preds {
            print!("  {} +{{", instance[*pred]);
            for p in pos {
                print!(" {}", instance[*p])
            }
            print!(" }}, -{{");
            for p in neg {
                print!(" {}", instance[*p])
            }
            println!(" }}")
        }
        println!("}}");

        println!("neg_new_preds {{");
        for (pred, (pos, neg)) in &self.neg_new_preds {
            print!("  {} +{{", instance[*pred]);
            for p in pos {
                print!(" {}", instance[*p])
            }
            print!(" }}, -{{");
            for p in neg {
                print!(" {}", instance[*p])
            }
            println!(" }}")
        }
        println!("}}");
        println!();
        println!();
        println!();
    }

    /// Sets up the unroller by scanning the instance.
    ///
    /// Returns `true` if there's nothing to do.
    fn setup(&mut self, instance: &mut PreInstance) -> Res<bool> {
        self.max_new_clauses = ::std::cmp::min(10, instance.clauses().len() / 20);

        for (pred, _) in instance.preds().index_iter() {
            if instance[pred].is_defined() {
                continue;
            }
            let (lhs_clauses, rhs_clauses) = instance.clauses_of(pred);

            let mut in_pos = false;
            for clause in rhs_clauses {
                if instance[*clause].lhs_pred_apps_len() == 0 {
                    in_pos = true;
                    break;
                }
            }
            if in_pos {
                let is_new = self.in_pos_clauses.insert(pred);
                debug_assert! { is_new }
            } else {
                let is_new = self.not_in_pos_clauses.insert(pred);
                debug_assert! { is_new }
            }

            let mut in_neg = false;
            for clause in lhs_clauses {
                let rhs_none = instance[*clause].rhs().is_none();
                let one_app = instance[*clause].lhs_pred_apps_len() == 1;

                if rhs_none && one_app {
                    in_neg = true;
                    break;
                }
            }
            if in_neg {
                let is_new = self.in_neg_clauses.insert(pred);
                debug_assert! { is_new }
            } else {
                let is_new = self.not_in_neg_clauses.insert(pred);
                debug_assert! { is_new }
            }
        }

        let do_nothing = self.not_in_pos_clauses.is_empty() && self.not_in_neg_clauses.is_empty();

        if !do_nothing {
            let (extractor, instance) = instance.extraction();
            self.retrieve_all_pos_defs(instance, extractor)?;
            self.retrieve_all_neg_defs(instance, extractor)?;

            let pos_neg = (self.in_pos_clauses.clone(), self.in_neg_clauses.clone());

            for pred in &self.not_in_pos_clauses {
                self.pos_new_preds
                    .entry(*pred)
                    .or_insert_with(|| pos_neg.clone());
            }

            for pred in &self.not_in_neg_clauses {
                self.neg_new_preds
                    .entry(*pred)
                    .or_insert_with(|| pos_neg.clone());
            }
        }

        Ok(do_nothing)
    }

    /// Retrieves a predicate positive definition from some clause.
    ///
    /// The clause has to be positive.
    pub fn retrieve_pos_def(
        &mut self,
        instance: &Instance,
        extractor: &mut ExtractionCxt,
        pred: PrdIdx,
        clause: &Clause,
    ) -> Res<()> {
        // Check what we're asked to do makes sense.
        let args = if let Some((p, args)) = clause.rhs() {
            if p != pred {
                bail!(
                    "trying to retrieve_pos for {} in clause with different rhs",
                    instance[pred]
                )
            }
            args
        } else {
            bail!(
                "trying to retrieve_pos for {} in non-positive clause (rhs)",
                instance[pred]
            )
        };
        if !clause.lhs_preds().is_empty() {
            bail!(
                "trying to retrieve_pos for {} in non-positive clause (lhs)",
                instance[pred]
            )
        }

        // println!(
        //   "from clause {}", clause.to_string_info(instance.preds()).unwrap()
        // ) ;

        match extractor.terms_of_rhs_app(
            true,
            instance,
            clause.vars(),
            clause.lhs_terms(),
            clause.lhs_preds(),
            (pred, args),
        )? {
            ExtractRes::Failed => bail!("term extraction failed for {}", instance[pred]),
            ExtractRes::Trivial | ExtractRes::SuccessTrue | ExtractRes::SuccessFalse => bail!(
                "unexpected result for term extraction for {} (false)",
                instance[pred]
            ),
            ExtractRes::Success((qvars, tterms)) => {
                let (terms, preds) = tterms.destroy();
                debug_assert! { preds.is_empty() }
                self.add_pos_def_for(pred, (qvars, terms))
            }
        }

        Ok(())
    }

    /// Retrieves all the partial positive definitions for some predicate.
    fn retrieve_pos_defs(
        &mut self,
        instance: &Instance,
        extractor: &mut ExtractionCxt,
        pred: PrdIdx,
    ) -> Res<usize> {
        log! {
          @verb "retrieving positive partial definitions for {}",
          conf.emph(& instance[pred].name)
        }
        let mut count = 0;
        for clause in instance.clauses_of(pred).1 {
            let clause = &instance[*clause];
            if clause.lhs_preds().is_empty() {
                self.retrieve_pos_def(instance, extractor, pred, clause)?;
                count += 1
            }
        }
        Ok(count)
    }

    /// Retrieves all partial positive definitions.
    fn retrieve_all_pos_defs(
        &mut self,
        instance: &Instance,
        extractor: &mut ExtractionCxt,
    ) -> Res<()> {
        log! { @4 "retrieve all positive definitions" }
        for pred in self.in_pos_clauses.clone() {
            log! { @4 "-> {}", instance[pred] }
            let count = self.retrieve_pos_defs(instance, extractor, pred)?;
            if count == 0 {
                bail!(
                    "failed to retrieve positive definition for {}",
                    instance[pred]
                )
            }
        }
        Ok(())
    }

    /// Retrieves a predicate negative definition from some clause.
    ///
    /// The clause has to be strictly negative.
    pub fn retrieve_neg_def(
        &mut self,
        instance: &Instance,
        extractor: &mut ExtractionCxt,
        pred: PrdIdx,
        clause: &Clause,
    ) -> Res<()> {
        // Check what we're asked to do makes sense.
        if clause.rhs().is_some() {
            bail!(
                "trying to retrieve_neg for {} in non-negative clause (rhs)",
                instance[pred]
            )
        }
        let args = {
            let mut preds = clause.lhs_preds().iter();
            let mut argss = if let Some((p, argss)) = preds.next() {
                debug_assert_eq! { p, & pred }
                if preds.next().is_some() {
                    bail!(
                        "trying to retrieve_neg for {} in a non-strict clause (preds)",
                        instance[pred]
                    )
                }
                argss.iter()
            } else {
                bail!(
                    "trying to retrieve_neg for {} in empty clause",
                    instance[pred]
                )
            };

            if let Some(args) = argss.next() {
                debug_assert! { argss.next().is_none() }
                args
            } else {
                bail!("trying to retrieve_neg for {} in a non-strict clause (argss)")
            }
        };

        // println!(
        //   "from clause {}", clause.to_string_info(instance.preds()).unwrap()
        // ) ;

        match extractor.terms_of_lhs_app(
            true,
            instance,
            clause.vars(),
            (clause.lhs_terms(), clause.lhs_preds()),
            None,
            (pred, args),
            false,
        )? {
            ExtractRes::Failed => bail!("term extraction failed for {}", instance[pred]),
            ExtractRes::Trivial | ExtractRes::SuccessTrue | ExtractRes::SuccessFalse => bail!(
                "unexpected result for term extraction for {} (false)",
                instance[pred]
            ),
            ExtractRes::Success((qvars, rhs, tterms)) => {
                debug_assert! { rhs.is_none() }
                let (terms, preds) = tterms.destroy();
                debug_assert! { preds.is_empty() }
                let mut neg_terms = TermSet::new();
                for term in terms {
                    neg_terms.insert(term);
                }
                self.add_neg_def_for(pred, (qvars, neg_terms))
            }
        }

        Ok(())
    }

    /// Retrieves all the partial negative definitions for some predicate.
    fn retrieve_neg_defs(
        &mut self,
        instance: &Instance,
        extractor: &mut ExtractionCxt,
        pred: PrdIdx,
    ) -> Res<usize> {
        log! {
          @verb "retrieving negative partial definitions for {}",
          conf.emph(& instance[pred].name)
        }
        let mut count = 0;
        for clause in instance.clauses_of(pred).0 {
            let clause = &instance[*clause];
            if clause.lhs_preds().len() == 1
                && clause.rhs().is_none()
                && clause
                    .lhs_preds()
                    .iter()
                    .next()
                    .map(|(_, argss)| argss.len() == 1)
                    .unwrap_or(false)
            {
                self.retrieve_neg_def(instance, extractor, pred, clause)?;
                count += 1
            }
        }
        Ok(count)
    }

    /// Retrieves all partial negative definitions.
    fn retrieve_all_neg_defs(
        &mut self,
        instance: &Instance,
        extractor: &mut ExtractionCxt,
    ) -> Res<()> {
        for pred in self.in_neg_clauses.clone() {
            let count = self.retrieve_neg_defs(instance, extractor, pred)?;
            if count == 0 {
                bail!(
                    "failed to retrieve negative definition for {}",
                    instance[pred]
                )
            }
        }
        Ok(())
    }

    /// Forces some terms in a clause by inserting a predicate application.
    ///
    /// `terms` is understood as a conjunction.
    fn insert_terms(
        &self,
        clause: &mut Clause,
        args: &VarTerms,
        qvars: &Quantfed,
        terms: &TermSet,
    ) -> Res<()> {
        // Generate fresh variables for the clause if needed.
        let qual_map = clause.fresh_vars_for(qvars);

        for term in terms {
            if let Some((term, _)) = term.subst_total(&(args, &qual_map)) {
                clause.insert_term(term);
            } else {
                bail!("error during total substitution in `insert_terms`")
            }
        }

        Ok(())
    }

    /// Tries to generate some positive clauses for a predicate.
    fn generate_pos_clauses_for(
        &mut self,
        pred: PrdIdx,
        instance: &mut PreInstance,
    ) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        'all_clauses: for rhs_clause in instance.clauses_of(pred).1.clone() {
            let mut one_pred_is_new = false;

            let mut estimation = 1;

            for (p, argss) in instance[rhs_clause].lhs_preds() {
                if let Some(defs) = self.pos_defs.get(p) {
                    for _ in argss {
                        estimation *= defs.len();
                        if estimation > self.max_new_clauses {
                            continue 'all_clauses;
                        }
                    }
                } else {
                    continue 'all_clauses;
                }

                if let Some((pos, _)) = self.pos_new_preds.get(&pred) {
                    if pos.contains(p) {
                        one_pred_is_new = true
                    }
                }
            }
            if !one_pred_is_new {
                continue 'all_clauses;
            }

            log! { @4
                "generating positive clause(s) for {} from {} ({})",
                instance[pred],
                instance[rhs_clause].to_string_info(instance.preds())?,
                estimation
            }

            let mut nu_clauses = vec![];

            {
                let mut clause = instance[rhs_clause].clone();

                let lhs_preds: Vec<_> = clause.drain_lhs_preds().collect();
                let mut map = Vec::with_capacity(lhs_preds.len());

                for (pred, argss) in lhs_preds {
                    let mut arg_map = Vec::with_capacity(argss.len());

                    if let Some(defs) = self.pos_defs.get(&pred) {
                        for args in argss {
                            arg_map.push((args, 0))
                        }

                        map.push((pred, defs, arg_map))
                    } else {
                        bail!("no definition for {} (positive, lhs)", instance[pred])
                    }
                }

                macro_rules! map_inc {
                    () => {{
                        let mut done = true;
                        'all_apps: for &mut (_, defs, ref mut argss) in &mut map {
                            for (_, ref mut index) in argss {
                                *index += 1;
                                if *index < defs.len() {
                                    done = false;
                                    break 'all_apps;
                                } else {
                                    *index = 0
                                }
                            }
                        }
                        done
                    }};
                }

                let mut done = false;
                while !done {
                    let mut clause = clause.clone();

                    for (_, defs, argss) in &map {
                        for (args, index) in argss {
                            self.insert_terms(&mut clause, args, &defs[*index].0, &defs[*index].1)?
                        }
                    }

                    if let Some(trivial) = instance.is_this_clause_trivial(&mut clause)? {
                        if !trivial {
                            nu_clauses.push(clause)
                        }
                    } else {
                        unimplemented!("unsat in biased unrolling")
                    }

                    done = map_inc!()
                }
            }

            for mut clause in nu_clauses {
                clause.from_unrolling = true;
                if let Some(index) = instance.push_clause(clause)? {
                    let (extractor, instance) = instance.extraction();
                    self.retrieve_pos_def(instance, extractor, pred, &instance[index])?;
                    info.clauses_added += 1
                }
            }
        }

        Ok(info)
    }

    fn init_for_neg_clause_generation(
        &self,
        pred: PrdIdx,
        instance: &mut PreInstance,
        lhs_clause: ClsIdx,
    ) -> Res<NegGenInit> {
        let mut clause = instance[lhs_clause].clone();

        let mut this_pred = None;
        let rhs_pred = clause.unset_rhs();
        let lhs_preds: Vec<_> = clause.drain_lhs_preds().collect();

        let mut map = Vec::with_capacity(lhs_preds.len());

        for (p, argss) in lhs_preds {
            let mut arg_map = Vec::with_capacity(argss.len());

            if let Some(defs) = self.pos_defs.get(&p) {
                for args in argss {
                    arg_map.push((args, 0))
                }

                if p == pred {
                    this_pred = Some((defs, arg_map))
                } else {
                    map.push((p, defs, arg_map))
                }
            } else if p == pred {
                debug_assert_eq! { argss.len(), 1 }
                let is_new = clause.insert_pred_app(pred, argss.into_iter().next().unwrap());
                debug_assert! { is_new }
            } else {
                bail!("no definition for {} (negative, lhs)", instance[p])
            }
        }

        if let Some((pred, args)) = rhs_pred {
            if let Some(defs) = self.neg_defs.get(&pred) {
                map.push((pred, defs, vec![(args, 0)]))
            } else {
                bail!("no definition for {} (negative, rhs)", instance[pred])
            }
        }

        Ok((clause, this_pred, map))
    }

    ///
    fn generate_neg_clause_for(
        &self,
        pred: PrdIdx,
        instance: &mut PreInstance,
        lhs_clause: ClsIdx,
        clauses: &mut Vec<Clause>,
    ) -> Res<()> {
        let (clause, mut this_pred, mut map) =
            self.init_for_neg_clause_generation(pred, instance, lhs_clause)?;

        let mut active_lhs_pred_app = 0;

        macro_rules! map_inc {
            () => {{
                let mut done = true;
                for &mut (_, defs, ref mut argss) in &mut map {
                    map_inc!(@argss done, defs, argss ; true);
                    if !done {
                        break;
                    }
                }

                // println!("inc: {}", done) ;

                if done {
                    if let Some(&mut (defs, ref mut argss)) = this_pred.as_mut() {
                        let argss_len = argss.len();
                        if active_lhs_pred_app < argss_len {
                            let mut index = 0;
                            map_inc! {
                                @argss done, defs, argss ; {
                                    let iff = index != active_lhs_pred_app ;
                                    index += 1 ;
                                    iff
                                }
                            }
                        }

                        if done {
                            active_lhs_pred_app += 1;
                            done = active_lhs_pred_app >= argss_len
                        }
                    }
                }

                done
            }};

            (@argss $done:ident, $defs:expr, $argss:expr ; $iff:expr) => {
                for (_, ref mut index) in $argss {
                    if $iff {
                        *index += 1;
                        if *index < $defs.len() {
                            $done = false;
                            break;
                        } else {
                            *index = 0
                        }
                    }
                }
            };
        }

        let mut done = false;
        while !done {
            // println!("running: {}", active_lhs_pred_app) ;

            let mut clause = clause.clone();
            if let Some((defs, argss)) = this_pred.as_ref() {
                let mut current = 0;

                while current < argss.len() {
                    let (ref args, index) = argss[current];
                    if current == active_lhs_pred_app {
                        let is_new = clause.insert_pred_app(pred, args.clone());
                        debug_assert! { is_new }
                    } else {
                        self.insert_terms(&mut clause, args, &defs[index].0, &defs[index].1)?
                    }
                    current += 1
                }
            }

            for (_, defs, argss) in &map {
                for (args, index) in argss {
                    self.insert_terms(&mut clause, args, &defs[*index].0, &defs[*index].1)?
                }
            }

            // println!(
            //   "negative clause: {}",
            //   clause.to_string_info(instance.preds()).unwrap()
            // ) ;

            if let Some(trivial) = instance.is_this_clause_trivial(&mut clause)? {
                if !trivial {
                    // println!("non-trivial...") ;
                    clauses.push(clause)
                } else {
                    // println!("trivial...")
                }
            } else {
                unsat!("in biased unrolling")
            }

            done = map_inc!()
        }

        Ok(())
    }

    /// Tries to generate a negative clause for a predicate.
    fn generate_neg_clauses_for(
        &mut self,
        pred: PrdIdx,
        instance: &mut PreInstance,
    ) -> Res<RedInfo> {
        // self.print(instance) ;

        let mut info = RedInfo::new();

        'all_clauses: for lhs_clause in instance.clauses_of(pred).0.clone() {
            let mut one_pred_is_new = false;

            let mut estimation = 1;

            if let Some((p, _)) = instance[lhs_clause].rhs() {
                if let Some(defs) = self.neg_defs.get(&p) {
                    estimation *= defs.len();
                    if estimation > self.max_new_clauses {
                        continue 'all_clauses;
                    }
                } else {
                    continue 'all_clauses;
                }
                if let Some((_, neg)) = self.neg_new_preds.get(&pred) {
                    if neg.contains(&p) {
                        one_pred_is_new = true
                    }
                }
            }

            for (p, argss) in instance[lhs_clause].lhs_preds() {
                if *p == pred {
                    if argss.len() == 1 {
                        ()
                    } else if let Some(defs) = self.pos_defs.get(p) {
                        estimation *= defs.len();
                        if estimation > self.max_new_clauses {
                            continue 'all_clauses;
                        }
                    } else {
                        continue 'all_clauses;
                    }
                } else if let Some(defs) = self.pos_defs.get(p) {
                    for _ in argss {
                        estimation *= defs.len();
                        if estimation > self.max_new_clauses {
                            continue 'all_clauses;
                        }
                    }
                } else {
                    // log! { @6 "{} not in pos clauses", instance[* p] }
                    continue 'all_clauses;
                }

                if let Some((pos, _)) = self.neg_new_preds.get(&pred) {
                    if pos.contains(p) {
                        one_pred_is_new = true
                    }
                }
            }

            // log! { @6 "one pred new: {}", one_pred_is_new }

            if !one_pred_is_new {
                continue 'all_clauses;
            }

            log! { @4
                "generating negative clause(s) for {} from {}",
                instance[pred],
                instance[lhs_clause].to_string_info( instance.preds() ) ?
            }

            let mut nu_clauses = vec![];

            self.generate_neg_clause_for(pred, instance, lhs_clause, &mut nu_clauses)?;

            for mut clause in nu_clauses {
                log! { @6
                    "new clause: {}",
                    clause.to_string_info( instance.preds() ) ?
                }

                clause.from_unrolling = true;
                if let Some(index) = instance.push_clause(clause)? {
                    let (extractor, instance) = instance.extraction();
                    self.retrieve_neg_def(instance, extractor, pred, &instance[index])?;
                    info.clauses_added += 1
                }
            }
        }

        Ok(info)
    }

    fn neg_unroll(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        for pred in self.not_in_neg_clauses.clone() {
            log! { @4
                "trying to generate negative clauses for {}", instance[pred]
            }
            // self.print(instance) ;

            if self
                .neg_new_preds
                .get(&pred)
                .map(|(pos, neg)| !pos.is_empty() || !neg.is_empty())
                .unwrap_or(false)
            {
                let this_info = self.generate_neg_clauses_for(pred, instance)?;

                if this_info.non_zero() {
                    let was_there = self.not_in_neg_clauses.remove(&pred);
                    debug_assert! { was_there }

                    let is_new = self.in_neg_clauses.insert(pred);
                    debug_assert! { is_new }

                    let prev = self.neg_new_preds.remove(&pred);
                    debug_assert! { prev.is_some() }

                    for (_, (_, neg)) in self
                        .pos_new_preds
                        .iter_mut()
                        .chain(self.neg_new_preds.iter_mut())
                    {
                        let is_new = neg.insert(pred);
                        debug_assert! { is_new }
                    }
                    log! { @4 | "-> success" }

                    log! { @verb |
                        "generated {} negative clauses for {}",
                        this_info.clauses_added, conf.emph(& instance[pred].name)
                    }

                    info += this_info;
                } else {
                    if let Some((pos, neg)) = self.neg_new_preds.get_mut(&pred) {
                        pos.clear();
                        neg.clear()
                    } else {
                        bail!("inconsistent BiasedUnroll state")
                    }
                    log! { @4 | "-> failure" }
                }
            } else {
                log! { @4 | "-> nothing new, skipping" }
            }
        }

        Ok(info)
    }

    fn pos_unroll(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        for pred in self.not_in_pos_clauses.clone() {
            log! { @4 |
                "trying to generate positive clauses for {}", instance[pred]
            }
            // self.print(instance) ;

            if self
                .pos_new_preds
                .get(&pred)
                .map(|(pos, _)| !pos.is_empty())
                .unwrap_or(false)
            {
                let this_info = self.generate_pos_clauses_for(pred, instance)?;

                if this_info.non_zero() {
                    let was_there = self.not_in_pos_clauses.remove(&pred);
                    debug_assert! { was_there }

                    let is_new = self.in_pos_clauses.insert(pred);
                    debug_assert! { is_new }

                    let prev = self.pos_new_preds.remove(&pred);
                    debug_assert! { prev.is_some() }

                    for (_, (pos, _)) in self
                        .pos_new_preds
                        .iter_mut()
                        .chain(self.neg_new_preds.iter_mut())
                    {
                        let is_new = pos.insert(pred);
                        debug_assert! { is_new }
                    }
                    log! { @4 | "-> success" }

                    log! { @verb |
                        "generated {} positive clauses for {}",
                        this_info.clauses_added, conf.emph(& instance[pred].name)
                    }

                    info += this_info;
                } else {
                    if let Some((pos, neg)) = self.pos_new_preds.get_mut(&pred) {
                        pos.clear();
                        neg.clear()
                    } else {
                        bail!("inconsistent BiasedUnroll state")
                    }
                    log! { @4 | "-> failure" }
                }
            } else {
                log! { @4 | "-> nothing new, skipping" }
            }
        }

        Ok(info)
    }
}

impl RedStrat for BiasedUnroll {
    fn name(&self) -> &'static str {
        "biased_unroll"
    }

    fn new(_: &Instance) -> Self {
        let (in_pos_clauses, in_neg_clauses, not_in_pos_clauses, not_in_neg_clauses) =
            (PrdSet::new(), PrdSet::new(), PrdSet::new(), PrdSet::new());

        BiasedUnroll {
            in_pos_clauses,
            in_neg_clauses,
            not_in_pos_clauses,
            not_in_neg_clauses,
            pos_defs: PrdHMap::new(),
            neg_defs: PrdHMap::new(),
            pos_new_preds: PrdHMap::new(),
            neg_new_preds: PrdHMap::new(),
            max_new_clauses: 0,
        }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        let nothing_to_do = self.setup(instance)?;

        if nothing_to_do {
            return Ok(info);
        }

        // println!("done with setup") ;
        // self.print(instance) ;
        // println!() ;

        let mut new_stuff = true;

        while new_stuff {
            new_stuff = false;

            if conf.preproc.pos_unroll {
                let this_info = self.pos_unroll(instance)?;
                if this_info.non_zero() {
                    new_stuff = true;
                    info += this_info
                }
            }

            if conf.preproc.neg_unroll {
                let this_info = self.neg_unroll(instance)?;
                if this_info.non_zero() {
                    new_stuff = true;
                    info += this_info
                }
            }
        }

        info += instance.simplify_all()?;

        Ok(info)
    }
}

type NegGenInit<'a> = (
    Clause,
    Option<(&'a PosDefs, IndexedArgs)>,
    Vec<(PrdIdx, &'a PosDefs, IndexedArgs)>,
);

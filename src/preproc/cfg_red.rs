//! Module in charge of constructing an analyzing the graph of dependencies
//! between predicates.

use crate::{
    common::*,
    preproc::{utils, utils::ExtractionCxt, PreInstance, RedStrat},
    var_to::terms::VarTermsSet,
};

/// Result of a DNF merge.
struct MergeRes {
    /// The dnf.
    def: Dnf,
    /// Clause generation estimation.
    estimation: usize,
}
impl MergeRes {
    /// Constructor.
    fn new(def: Dnf, estimation: usize) -> Self {
        MergeRes { def, estimation }
    }
}

/// Maps predicates to the predicates they depend on.
pub type Dep = PrdMap<PrdMap<usize>>;

/// Graph of dependencies.
#[derive(Clone)]
pub struct Graph {
    /// Forward dependencies.
    forward: Dep,
    /// Backward dependencies.
    bakward: Dep,
    /// Predicates appearing in a negative constraint.
    neg: PrdMap<usize>,
    /// Predicates appearing in a positive constraint.
    pos: PrdMap<usize>,
}
impl Graph {
    /// Constructs an empty graph.
    pub fn new(instance: &Instance) -> Self {
        let forward: Dep =
            vec![vec![0; instance.preds().len()].into(); instance.preds().len()].into();
        let bakward = forward.clone();
        let neg: PrdMap<_> = vec![0; instance.preds().len()].into();
        let pos: PrdMap<_> = vec![0; instance.preds().len()].into();
        Graph {
            forward,
            bakward,
            neg,
            pos,
        }
    }

    /// Resets the graph.
    fn reset(&mut self) {
        for forward in self.forward.iter_mut() {
            for count in forward.iter_mut() {
                *count = 0
            }
        }
        for bakward in self.bakward.iter_mut() {
            for count in bakward.iter_mut() {
                *count = 0
            }
        }
        for count in self.pos.iter_mut() {
            *count = 0
        }
        for count in self.neg.iter_mut() {
            *count = 0
        }
    }

    /// Clears itself and sets everything up for the input instance.
    pub fn setup(&mut self, instance: &Instance) {
        self.reset();

        for clause in instance.clauses() {
            if let Some((tgt, _)) = clause.rhs() {
                if clause.lhs_preds().is_empty() {
                    self.pos[tgt] += 1;
                } else {
                    for (prd, _) in clause.lhs_preds() {
                        self.bakward[tgt][*prd] += 1;
                        self.forward[*prd][tgt] += 1;
                    }
                }
            } else {
                for (prd, _) in clause.lhs_preds() {
                    self.neg[*prd] += 1;
                }
            }
        }
    }

    /// Dumps a graph in dot format.
    pub fn dot_write<W>(&self, w: &mut W, instance: &Instance, hi_lite: &PrdSet) -> Res<()>
    where
        W: Write,
    {
        writeln!(w, "digraph blah {{",)?;
        writeln!(w, "  rankdir=LR ;")?;
        writeln!(w, "  edge [arrowhead=onormal] ;")?;
        writeln!(
            w,
            "  top[\
        label = \"top\", peripheries = 2, color = darkolivegreen3, \
        style = filled, fontcolor = white
      ] ;"
        )?;
        writeln!(
            w,
            "  bot[\
        label = \"bot\", peripheries = 2, color = indianred1, \
        style = filled, fontcolor = white
      ] ;"
        )?;
        for (prd, info) in instance.preds().index_iter() {
            if !instance[prd].is_defined() {
                if hi_lite.contains(&prd) {
                    writeln!(
                        w,
                        "  p_{} [label = \"{}\", color = gray, style = filled] ;",
                        prd, info.name
                    )?
                } else {
                    writeln!(w, "  p_{} [label = \"{}\"] ;", prd, info.name)?
                }
            }
        }
        for (prd, count) in self.pos.index_iter() {
            if *count > 0 {
                writeln!(
                    w,
                    "  top -> p_{} [color = darkolivegreen3, label = \"{}\"] ;",
                    prd, count
                )?
            }
        }
        for (prd, count) in self.neg.index_iter() {
            if *count > 0 {
                writeln!(
                    w,
                    "  p_{} -> bot [color = indianred1, label = \"{}\"] ;",
                    prd, count
                )?
            }
        }
        for (prd, targets) in self.forward.index_iter() {
            for (tgt, count) in targets.index_iter() {
                let count = *count;
                if count > 0 {
                    writeln!(w, "  p_{} -> p_{} [label = \"{}\"] ;", prd, tgt, count)?
                }
            }
        }
        writeln!(w, "}}\n")?;
        Ok(())
    }

    /// Dumps a graph to a file as a graphviz graph, and runs `dot`.
    #[inline]
    pub fn to_dot<S>(&self, instance: &Instance, file: S, hi_lite: &PrdSet) -> Res<()>
    where
        S: AsRef<str>,
    {
        if let Some((mut pred_dep_file, path)) = conf.preproc.pred_dep_file(file, instance)? {
            use std::process::Command;
            self.dot_write(&mut pred_dep_file, instance, hi_lite)?;
            let mut pdf_path = path.clone();
            pdf_path.set_extension("pdf");
            let output = match Command::new("dot")
                .args(&["-Tpdf", "-o"])
                .arg(pdf_path)
                .arg(&path)
                .output()
            {
                Ok(output) => output,
                Err(ref e) if e.kind() == ::std::io::ErrorKind::NotFound => {
                    warn!(
                        "failed to run `{}` on predicate dependency graphviz file `{}`",
                        conf.sad("dot"),
                        conf.emph(path.to_string_lossy()),
                    );
                    return Ok(());
                }
                Err(e) => bail!(e),
            };
            if !output.status.success() {
                let mut blah = format!(
                    "while running `dot` on `{}`\n|=| stdout:",
                    path.to_string_lossy()
                );
                for line in String::from_utf8_lossy(&output.stdout).lines() {
                    blah.push_str("\n  | ");
                    blah.push_str(line)
                }
                blah.push_str("\n|=| stdout:");
                for line in String::from_utf8_lossy(&output.stderr).lines() {
                    blah.push_str("\n  | ");
                    blah.push_str(line)
                }
                blah.push_str("\n|=|");
                bail!(blah)
            }
        }
        Ok(())
    }

    /// Checks that the graph makes sense.
    #[cfg(not(debug_assertions))]
    #[inline(always)]
    pub fn check(&self, _: &Instance) -> Res<()> {
        Ok(())
    }

    /// Checks that the graph makes sense.
    #[cfg(debug_assertions)]
    pub fn check(&self, instance: &Instance) -> Res<()> {
        fn sub_check(slf: &Graph, instance: &Instance) -> Res<()> {
            for (prd, targets) in slf.forward.index_iter() {
                for (tgt, count) in targets.index_iter() {
                    let bak_count = &slf.bakward[tgt][prd];
                    if bak_count != count {
                        bail!(
                            "\
                             found {} forward dependencies for `{} -> {}`, \
                             but {} (!= {}) backward dependencies\
                             ",
                            count,
                            instance[prd],
                            instance[tgt],
                            bak_count,
                            count
                        )
                    }
                }
            }
            for (prd, targets) in slf.bakward.index_iter() {
                for (tgt, count) in targets.index_iter() {
                    let for_count = &slf.forward[tgt][prd];
                    if for_count != count {
                        bail!(
                            "\
                             found {} backward dependencies for `{} -> {}`, \
                             but {} (!= {}) forward dependencies\
                             ",
                            count,
                            instance[prd],
                            instance[tgt],
                            for_count,
                            count
                        )
                    }
                }
            }
            Ok(())
        }
        sub_check(self, instance).chain_err(|| "graph inconsistency:")
    }

    /// Follows a forward map. Returns the predicates it encountered and how many
    /// times it encountered them.
    pub fn follow(
        _instance: &Instance,
        start: PrdIdx,
        forward: &PrdHMap<PrdSet>,
    ) -> Res<PrdHMap<usize>> {
        let mut known = PrdSet::new();
        let mut to_do = PrdSet::new();
        to_do.insert(start);
        known.insert(start);

        let mut res = PrdHMap::new();
        res.insert(start, 1);

        macro_rules! update {
            ($known:ident $to_do:ident $map:ident < $set:expr) => {
                for prd in $set {
                    *$map.entry(*prd).or_insert(0) += 1;
                    let unknown = $known.insert(*prd);
                    if unknown {
                        let is_new = $to_do.insert(*prd);
                        debug_assert!(is_new)
                    }
                }
            };
        }

        while !to_do.is_empty() {
            conf.check_timeout()?;
            let pred = *to_do.iter().next().unwrap();
            to_do.remove(&pred);
            if let Some(tgts) = forward.get(&pred) {
                if_debug! {
                  log_debug! { "following {}", _instance[pred] } ;
                  for pred in tgts {
                    log_debug! { "- {}", _instance[* pred] }
                  }
                }

                update!( known to_do res < tgts )
            }
        }

        Ok(res)
    }

    /// Merges two DNFs with quantifiers.
    ///
    /// Also returns the clause generation estimation.
    ///
    /// Returns `None` if inlining would have generated more clauses than `max`
    /// (by `estimate`).
    ///
    /// Used when inlining a predicate application of `p`. `lft` is understood as
    /// (part of) the definition of `p` different from `pred`. `subst` are its
    /// arguments.
    ///
    /// The arguments of `p` are applied to `lft`, and the quantified variables
    /// are bumped to the first variable index used by neither the formal
    /// arguments of `pred` and the quantified variables in `rgt`.
    ///
    /// Renames the quantified variables so that they don't clash.
    ///
    /// # TODO
    ///
    /// - improve performance, `rgt` could just receive the result
    fn merge(
        instance: &Instance,
        pred: PrdIdx,
        substs: &VarTermsSet,
        lft: DnfRef,
        rgt: DnfRef,
        max: Option<usize>,
    ) -> Res<Option<MergeRes>> {
        log! {
            @6 | "merging for {}, {} substitutions", instance[pred], substs.len()
        }
        let fresh_index = instance[pred].fresh_var_idx();
        log! { @6 | "fresh index: {}", fresh_index }

        let mut result = Vec::with_capacity(lft.len() * rgt.len());
        let mut estimation = 0;

        // This will map `lft` quantified variables to fresh index to avoid
        // quantified variable clashes.
        let mut qvar_map = VarHMap::with_capacity(0);

        for &(ref r_qvars, ref r_conj) in rgt {
            // Retrieve first legal index for new quantified variables.
            let mut fresh_index = fresh_index;

            for (idx, _) in r_qvars {
                log! { @7 | "- rgt qvar {}", idx }
                if *idx >= fresh_index {
                    fresh_index = (1 + **idx).into()
                }
            }
            log! { @7 | "first legal index: {}", fresh_index }

            // All combinations of elements of `lft` of len `substs`.
            let mut all_lft_combinations = CombinationIter::new(lft.iter(), substs.len())
                .chain_err(|| {
                    format!(
                        "while generating all combinations during merge for predicate {}",
                        instance[pred]
                    )
                })?;

            // For each combination of elements of `lft` of len `substs`, add a new
            // definition to `r_conj`.
            while let Some(combination) = all_lft_combinations.next_combination() {
                // Done with this combination.
                if let Some(res) = Self::merge_combination(
                    r_conj,
                    r_qvars,
                    &mut qvar_map,
                    combination,
                    substs,
                    &mut fresh_index,
                )? {
                    // Only add if new (loose syntactic check).
                    if result.iter().all(|other| other != &res) {
                        result.push(res);

                        if let Some(max) = max {
                            if let Some(e) = Self::estimate(instance, pred, result.len(), max) {
                                estimation += e
                            } else {
                                return Ok(None);
                            }
                        }
                    }
                }
            }
        }

        Ok(Some(MergeRes::new(result, estimation)))
    }

    /// Handles a merge combination.
    fn merge_combination(
        r_conj: &TTermSet,
        r_qvars: &Quantfed,
        qvar_map: &mut VarHMap<Term>,
        combination: &[&(Quantfed, TTermSet)],
        substs: &VarTermsSet,
        fresh_index: &mut VarIdx,
    ) -> Res<Option<(Quantfed, TTermSet)>> {
        debug_assert_eq! { combination.len(), substs.len() }

        // Cloning `rgt`'s definition to add stuff from `lft` for this
        // combination.
        // Cloning `rgt`'s qvars to add the renamed qvars from `lft`.
        let (mut r_conj, mut r_qvars) = (r_conj.clone(), r_qvars.clone());

        // Work on the current combination: apply a substitution to a member of
        // `lft`.
        for ((l_qvars, l_conj), subst) in combination.iter().zip(substs.iter()) {
            conf.check_timeout()?;
            log! { @7 | "working on substitution..." }

            // Fresh map for this substitution.
            qvar_map.clear();

            // Generate fresh indices for `l_qvars` to avoid index clashes.
            qvar_map.reserve(l_qvars.len());
            r_qvars.reserve(l_qvars.len());
            for (qvar, typ) in l_qvars {
                let prev = qvar_map.insert(*qvar, term::var(*fresh_index, typ.clone()));
                debug_assert!(prev.is_none());
                // Update the new qvars for the result.
                let prev = r_qvars.insert(*fresh_index, typ.clone());
                debug_assert!(prev.is_none());
                // Increment the fresh_index.
                fresh_index.inc()
            }

            // Apply substitution and add to `r_conj`.

            r_conj.reserve(l_conj.terms().len(), l_conj.preds().len());
            // Working on terms.
            for term in l_conj.terms() {
                log! { @8 | "subst on {}", term }
                let (term, _) = term.subst(&(&*qvar_map, subst));
                log! { @8 | "-> {}", term }

                let is_false = term::simplify::conj_term_insert(term, r_conj.terms_mut());

                if is_false {
                    return Ok(None);
                }
            }

            // Working on pred applications.
            for (pred, argss) in l_conj.preds() {
                let mut nu_argss = VarTermsSet::with_capacity(argss.len());
                for args in argss {
                    let mut nu_args = VarMap::with_capacity(args.len());
                    for arg in args.iter() {
                        let (arg, _) = arg.subst(&(&*qvar_map, subst));
                        nu_args.push(arg)
                    }
                    nu_argss.insert(nu_args.into());
                }
                r_conj.insert_pred_apps(*pred, nu_argss)
            }
        }

        Ok(Some((r_qvars, r_conj)))
    }

    /// Retrieves the definition of a predicate from all its RHS occurences.
    ///
    /// Also returns the clause generation estimation.
    ///
    /// Returns `None` if inlining would have generated more clauses than `max`
    /// (by `estimate`).
    fn dnf_of(
        &mut self,
        instance: &Instance,
        extractor: &mut ExtractionCxt,
        pred: PrdIdx,
        max: Option<usize>,
        previous: &[(PrdIdx, Dnf)],
    ) -> Res<Option<MergeRes>> {
        log! { @4 | "dnf_of({}, {:?})", instance[pred], max }

        let forced_inlining = max.is_none();

        let mut estimation = 0;

        let clauses = instance.rhs_clauses_of(pred);
        let mut def = Vec::with_capacity(clauses.len());

        conf.check_timeout()?;

        'clause_iter: for clause in clauses {
            let mut to_merge: Vec<(PrdIdx, VarTermsSet, &Dnf)> = Vec::with_capacity(7);

            let clause = &instance[*clause];
            let args = if let Some((p, args)) = clause.rhs() {
                debug_assert_eq! { p, pred }
                args
            } else {
                bail!("instance inconsistency")
            };

            match extractor.terms_of_rhs_app(
                true,
                instance,
                &clause.vars,
                clause.lhs_terms(),
                clause.lhs_preds(),
                (pred, args),
            )? {
                utils::ExtractRes::Success((qvars, mut tterms)) => {
                    log! { @5
                        "from clause {}", clause.to_string_info(&instance.preds())?
                    }

                    if !forced_inlining && !tterms.preds().is_empty() {
                        for (pred, def) in previous {
                            if tterms.preds().is_empty() {
                                break;
                            }
                            if let Some(argss) = tterms.preds_mut().remove(pred) {
                                to_merge.push((*pred, argss, def))
                            }
                        }
                    }

                    if let Some(partial_def) = Self::handle_partial_def_of(
                        instance,
                        (def.len(), max),
                        &mut estimation,
                        pred,
                        &mut to_merge,
                        qvars,
                        tterms,
                    )? {
                        def.extend(partial_def)
                    } else {
                        return Ok(None);
                    }

                    if_log! { @5
                        log! { @5 |=> "current definition:" }
                        Self::log_definition(instance, & def)
                    }
                }
                utils::ExtractRes::SuccessTrue => bail!(
                    "unimplemented, predicate is true ({} {})",
                    instance[pred],
                    args
                ),
                utils::ExtractRes::Trivial | utils::ExtractRes::SuccessFalse => {
                    continue 'clause_iter
                }
                _ => bail!("failed to extract lhs terms"),
            }
        }

        Ok(Some(MergeRes::new(def, estimation)))
    }

    /// Prints a definition for some predicate.
    #[cfg(not(feature = "bench"))]
    fn log_definition(_instance: &Instance, _def: DnfRef) {
        for (qvars, tterms) in _def {
            log! { @5 |=> "and" }
            if !qvars.is_empty() {
                log! { @5 |=> "  qvars {{" }
                for (var, typ) in qvars {
                    log! { @5 |=> "    {}: {}", var.default_str(), typ }
                }
                log! { @5 |=> "  }}" }
            }
            for term in tterms.terms() {
                log! { @5 |=> "  {}", term }
            }
            for (pred, argss) in tterms.preds() {
                for args in argss {
                    log! { @5 |=> "  ({} {})", _instance[* pred], args }
                }
            }
        }
        log! { @5 |=> " " }
    }

    /// Handles a conjunction that's part of a definition for a predicate.
    fn handle_partial_def_of(
        instance: &Instance,
        (def_len, max): (usize, Option<usize>),
        estimation: &mut usize,
        pred: PrdIdx,
        to_merge: &mut Vec<(PrdIdx, VarTermsSet, &Dnf)>,
        qvars: Quantfed,
        tterms: TTermSet,
    ) -> Res<Option<Dnf>> {
        let res = if to_merge.is_empty() {
            if let Some(max) = max.map(|max: usize| {
                if *estimation > max {
                    0
                } else {
                    max - *estimation
                }
            }) {
                if let Some(e) = Self::estimate(instance, pred, def_len + 1, max) {
                    *estimation += e
                } else {
                    return Ok(None);
                }
            }
            Some(vec![(qvars, tterms)])
        } else if let Some(def) = Self::sub_handle_partial_def_of(
            instance, max, estimation, pred, to_merge, qvars, tterms,
        )? {
            Some(def)
        } else {
            None
        };

        Ok(res)
    }

    /// Handles a conjunction that's part of a definition for a predicate.
    fn sub_handle_partial_def_of(
        instance: &Instance,
        max: Option<usize>,
        estimation: &mut usize,
        pred: PrdIdx,
        to_merge: &mut Vec<(PrdIdx, VarTermsSet, &Dnf)>,
        qvars: Quantfed,
        tterms: TTermSet,
    ) -> Res<Option<Dnf>> {
        if_log! { @5
            log! { @5 |=> "qvars {{" }
            for (var, typ) in & qvars {
                log! { @5 |=> "  {}: {}", var.default_str(), typ }
            }
            log! { @5 |=> "}}" }
            log! { @5 |=> "conj {{" }
            for term in tterms.terms() {
                log! { @5 |=> "  {}", term }
            }
            for (pred, argss) in tterms.preds() {
                for args in argss {
                    log! { @5 |=> "  ({} {})", instance[* pred], args }
                }
            }
            log! { @5 |=> "}}" }
        }

        let mut curr = vec![(qvars, tterms)];

        for (_this_pred, argss, p_def) in to_merge.drain(0..) {
            conf.check_timeout()?;

            if_log! { @6
                Self::log_merge_defs(
                    _this_pred, instance, & argss, p_def, & curr
                )
            }

            if let Some(res) = Self::merge(
                instance,
                pred,
                &argss,
                p_def,
                &curr,
                max.map(|max: usize| {
                    if *estimation > max {
                        0
                    } else {
                        max - *estimation
                    }
                }),
            )? {
                curr = res.def;
                *estimation += res.estimation;
            } else {
                return Ok(None);
            }
        }

        Ok(Some(curr))
    }

    /// Prints definition before merging.
    #[cfg(not(feature = "bench"))]
    fn log_merge_defs(
        _this_pred: PrdIdx,
        _instance: &Instance,
        _argss: &VarTermsSet,
        _p_def: DnfRef,
        _curr: DnfRef,
    ) {
        log! { @6 |=> "curr {{" }
        let mut first = true;
        for &(ref qv, ref tterms) in _curr {
            if first {
                first = false
            } else {
                log! { @6 |=> " " }
            }
            for (var, typ) in qv {
                log! { @6 |=> "  {}: {}", var.default_str(), typ }
            }
            for term in tterms.terms() {
                log! { @6 |=> "  {}", term }
            }
            for (pred, _argss) in tterms.preds() {
                for args in _argss {
                    log! { @6 |=> "  ({} {})", _instance[* pred], args }
                }
            }
        }
        log! { @6 |=> "}}" }
        Self::log_merge_defs_sub(_this_pred, _instance, _argss, _p_def)
    }

    /// Prints definition before merging.
    #[cfg(not(feature = "bench"))]
    fn log_merge_defs_sub(
        _this_pred: PrdIdx,
        _instance: &Instance,
        _argss: &VarTermsSet,
        _p_def: DnfRef,
    ) {
        log! { @6 |=> "argss for {} {{", _instance[_this_pred] }
        for args in _argss {
            let mut pref = "  > ";
            for (var, arg) in args.index_iter() {
                log! { @6 |=> "{}{} -> {}", pref, var.default_str(), arg }
                pref = "    "
            }
        }
        log! { @6 |=> "}}" }
        log! { @6 |=> "defs {{" }
        let mut first = true;

        for &(ref qv, ref tterms) in _p_def {
            if first {
                first = false
            } else {
                log! { @6 |=> " " }
            }
            for (var, typ) in qv {
                log! { @6 |=> "  {}: {}", var.default_str(), typ }
            }
            for term in tterms.terms() {
                log! { @6 |=> "  {}", term }
            }
            for (pred, _argss) in tterms.preds() {
                for args in _argss {
                    log! { @6 |=> "  ({} {})", _instance[* pred], args }
                }
            }
        }
        log! { @6 |=> "}}" }
    }

    /// Constructs all the predicates not in `keep` by inlining the constraints.
    ///
    /// Returns a disjunction of conjunctions.
    pub fn inline(
        &mut self,
        instance: &mut PreInstance,
        keep: &mut PrdSet,
        mut upper_bound: usize,
    ) -> Res<Vec<(PrdIdx, Dnf)>> {
        let (extractor, instance) = instance.extraction();
        let mut res = Vec::with_capacity(instance.preds().len() - keep.len());
        macro_rules! res_contains {
            ($pred:expr) => {
                res.iter().any(|(pred, _)| pred == $pred)
            };
        }

        let forced_inlining = keep.len() == 0;

        conf.check_timeout()?;

        'construct: loop {
            // Find a predicate that's not in `keep` with all its antecedents in
            // `keep`.
            let mut pred = None;
            'find_pred: for (prd, srcs) in self.bakward.index_iter() {
                if keep.contains(&prd) || instance[prd].is_defined() || res_contains!(&prd) {
                    continue 'find_pred;
                }
                log! { @3 | "looking at {}", instance[prd] }
                'check_src: for (src, cnt) in srcs.index_iter() {
                    if *cnt == 0 {
                        continue 'check_src;
                    }
                    log! { @3 | "depends on {}", instance[src] }
                    if !keep.contains(&src) && !res_contains!(&src) {
                        continue 'find_pred;
                    }
                }
                pred = Some(prd);
                break 'find_pred;
            }

            let pred = if let Some(p) = pred {
                p
            } else {
                log! { @3 | "no predicate illeligible for inlining" }
                break 'construct;
            };

            log! { @3 | "investigating inlining {}", instance[pred] }

            macro_rules! keep_and_continue {
                ($pred:expr) => {
                    keep.insert($pred);
                    continue 'construct;
                };
                () => {{
                    keep.insert(pred);
                    continue 'construct;
                }};
            }

            let def = if let Some(res) = self.dnf_of(
                instance,
                extractor,
                pred,
                if !forced_inlining {
                    Some(upper_bound)
                } else {
                    None
                },
                &res,
            )? {
                upper_bound += res.estimation;
                log! { @4 |
                    "inlining {} (blow-up estimation: {})",
                    instance[pred], res.estimation
                }
                res.def
            } else {
                keep_and_continue!()
            };

            if_log! { @4
                log! { @4 |=> "definition:" }
                Self::log_definition(instance, & def)
            }

            conf.check_timeout()?;

            debug_assert! { ! res_contains!(& pred) }

            res.push((pred, def))
        }

        Ok(res)
    }

    /// Estimates clause creation blow-up.
    ///
    /// Estimates whether inlining `pred` with a DNF of length `len` will
    /// generate more than `max` clauses. If yes, returns `None`, and returns its
    /// prediction otherwise.
    fn estimate(instance: &Instance, pred: PrdIdx, len: usize, max: usize) -> Option<usize> {
        let max = max + instance.clauses_of(pred).1.len();
        let mut estimation: usize = 0;

        // println!("{}: {} / {}", instance[pred], len, max) ;

        for clause in instance.clauses_of(pred).0 {
            let argss_len = instance[*clause]
                .lhs_preds()
                .get(&pred)
                .map(|argss| argss.len())
                .expect("inconsistent instance state");
            // println!("  #{}: {}", clause, argss_len) ;

            let mut inc = len;
            for _ in 1..argss_len {
                if inc > max {
                    return None;
                } else if let Some(nu_inc) = inc.checked_mul(len) {
                    inc = nu_inc
                } else {
                    return None;
                }
            }

            if let Some(e) = estimation.checked_add(inc) {
                estimation = e;
                if estimation <= max {
                    // println!("  est: {}", estimation) ;
                    continue;
                }
            }
            // println!("blows up") ;
            log! { @6 |
                "inlining for {} blows up: {} > {} (len: {})",
                instance[pred], estimation, max, len
            }
            return None;
        }

        Some(estimation)
    }

    /// Finds a predicate to start breaking cycles from in the graph.
    fn find_starting_pred(
        &self,
        _instance: &Instance,
        pos: &PrdSet,
        forward: &PrdHMap<PrdSet>,
    ) -> Option<PrdIdx> {
        if_log! { @3
          log! { @3 |=> "  looking for a starting point with" }
          log! { @3 |=> "  - pos {{" }
          for prd in pos {
            log! { @3 |=> "    {}", _instance[* prd] }
          }
          log! { @3 |=> "  }}" }
          log! { @3 |=> "  - forward {{" }
          for (prd, set) in forward {
            let mut s = String::new() ;
            for prd in set {
              s = format!("{} {}", s, _instance[* prd])
            }
            log! { @3 |=> "    {} ->{}", _instance[* prd], s }
          }
          log! { @3 |=> " }}" }
        }

        // Find a starting point.
        if let Some(pred) = pos.iter().next() {
            log! { @3 | "  found one in `pos`" }
            // There was something in `pos`, remove it and move on.
            Some(*pred)
        } else {
            log! { @3 | "  no preds in `pos`, looking in `forward`" }
            // There was nothing in `pos`, select something from `forward`.
            forward.iter().next().map(|(pred, _)| *pred)
        }
    }

    /// Looks for a minimal set of predicates to infer by breaking cycles.
    ///
    /// Returns the set of predicates to keep, and the set of predicates to
    /// remove.
    pub fn break_cycles(&mut self, instance: &Instance) -> Res<PrdSet> {
        log_debug! { "breaking cycles in pred dep graph..." }

        let (mut set, mut pos, mut forward) = self.get_current_graph(instance)?;

        let mut cnt = 0;

        conf.check_timeout()?;
        'break_cycles: while !forward.is_empty() {
            cnt += 1;
            self.to_dot(instance, format!("pred_red_{}", cnt), &set)?;

            let start = self.find_starting_pred(instance, &pos, &forward);

            let start = if let Some(pred) = start {
                pred
            } else {
                log! { @3 | "  no starting point found, done" }
                break 'break_cycles;
            };

            log! { @3 | "  starting point is {}, following it", instance[start] }

            // Follow it.
            let weights = Self::follow(instance, start, &forward)?;
            if weights.is_empty() {
                bail!("`follow` failed to construct weights...")
            }

            if let Some(pred) = Self::find_heaviest(instance, &weights)? {
                log! { @3 |
                    "  removing it from everything" ;
                    "  remembering {}", instance[pred]
                }
                // Remove the representative from everything.
                Self::forget(pred, &mut pos, &mut forward);

                let is_new = set.insert(pred);
                debug_assert!(is_new);

                log! { @3 | "" }
            } else {
                // There's no cycle, forget everything in weight and keep going.
                for (pred, _weight) in weights {
                    log! { @3 | "  - forgetting {} ({})", instance[pred], _weight }
                    Self::forget(pred, &mut pos, &mut forward);
                    debug_assert!(_weight < 2)
                }
            }
        }

        set.shrink_to_fit();
        Ok(set)
    }

    /// Retrieves positive predicates and arrows in the current dependency graph.
    fn get_current_graph(&self, instance: &Instance) -> Res<(PrdSet, PrdSet, PrdHMap<PrdSet>)> {
        let mut set = PrdSet::with_capacity(instance.preds().len() / 3);

        conf.check_timeout()?;
        for (prd, prds) in self.forward.index_iter() {
            if prds[prd] > 0 {
                let is_new = set.insert(prd);
                debug_assert!(is_new)
            }
        }

        conf.check_timeout()?;
        let mut pos = PrdSet::new();
        for (prd, cnt) in self.pos.index_iter() {
            if set.contains(&prd) {
                continue;
            }
            if *cnt > 0 {
                pos.insert(prd);
            }
        }

        conf.check_timeout()?;
        let mut forward = PrdHMap::new();
        for (prd, prds) in self.forward.index_iter() {
            if set.contains(&prd) {
                continue;
            }
            for (tgt, cnt) in prds.index_iter() {
                if set.contains(&tgt) {
                    continue;
                }
                if *cnt > 0 {
                    let is_new = forward.entry(prd).or_insert_with(PrdSet::new).insert(tgt);
                    debug_assert!(is_new)
                }
            }
        }
        Ok((set, pos, forward))
    }

    /// Forgets a predicate from the positive and forward set.
    fn forget(pred: PrdIdx, pos: &mut PrdSet, forward: &mut PrdHMap<PrdSet>) {
        pos.remove(&pred);
        forward.remove(&pred);
        for (_, set) in forward.iter_mut() {
            set.remove(&pred);
        }
    }

    /// Looks for the heaviest predicate.
    ///
    /// Returns `None` if there are no cycles (max weight < 2).
    fn find_heaviest(_instance: &Instance, weights: &PrdHMap<usize>) -> Res<Option<PrdIdx>> {
        log! { @3 "  looking for the heaviest predicate" }

        // Representant.
        let mut rep = None;
        for (prd, weight) in weights {
            let (prd, weight) = (*prd, *weight);
            log! { @3 | "    {} -> {}", _instance[prd], weight }
            let curr_weight = if let Some(&(_, w)) = rep.as_ref() {
                w
            } else {
                0
            };
            if weight > curr_weight {
                rep = Some((prd, weight))
            }
        }

        if let Some((pred, weight)) = rep {
            log! { @3 | "  heaviest is {} ({})", _instance[pred], weight }
            if weight < 2 {
                log! { @3 | "no cycle, forgetting everything" }
                Ok(None)
            } else {
                Ok(Some(pred))
            }
        } else {
            bail!("try to find heaviest predicate in empty weight map")
        }
    }
}

/// Detects cycles and keeps a minimal set of predicates to infer.
///
/// Break the acyclic parts of the "control-flow graph" of the predicates. Writing `p_i, ..., p_k
/// -> p_n` when there's a clause with applications of `p_i, ..., p_k` in its LHS and `p_n` in its
/// RHS, say we have
///
/// - `true -> p_0`
/// - `p_0 -> p_1`
/// - `p_1, p_2 -> p_1`
/// - `p_3 -> p_2`
/// - `p_1 -> p_3`
/// - `p_1 -> false`
///
/// Graphically the dependencies between the predicates are
///
/// ```bash
///                       _
///                      | V
/// true ---> p_0 -----> p_1 ---> p_3
///                     / ^        |
///                    /  |        V
///           false <-|   |------ p_2
/// ```
///
/// The really `p_0` could be re-written in terms of `p_1`. Likewise for `p_3`. Then, since `p_2`
/// can be defined using `p_3`, `p_2` can be re-written in terms of `p_1` too.
///
/// This technique works by removing nodes in the CFG that break cycle. In particular,
/// self-referencing predicates like `p_1` above are removed right away. In the example above, this
/// breaks all the cycle, meaning the remaining predicates can be expressed in terms of the ones
/// removed.
///
/// # Examples
///
/// ```rust
/// // See this file for a non-trivial example.
/// ::std::fs::OpenOptions::new().read(true).open("rsc/sat/cfg_red.smt2").unwrap();
/// ```
pub struct CfgRed {
    /// Internal counter for log files.
    cnt: usize,
    /// Upper bound computed once at the beginning to avoid a progressive
    /// blow-up.
    upper_bound: usize,
    /// Graph, factored to avoid reallocation.
    graph: Graph,
}

impl CfgRed {
    /// Removes all clauses leading to some predicates and forces them in the
    /// instance.
    fn apply_pred_defs(
        &self,
        instance: &mut PreInstance,
        pred_defs: Vec<(PrdIdx, Dnf)>,
    ) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        for (pred, def) in pred_defs {
            if instance[pred].is_defined() {
                continue;
            }

            conf.check_timeout()?;
            info += instance.rm_rhs_clauses_of(pred)?;

            if_log! { @5
              let mut s = format!("{}(", instance[pred]) ;
              let mut is_first = true ;
              for (var, typ) in instance[pred].sig.index_iter() {
                if ! is_first {
                  s.push_str(", ")
                } else {
                  is_first = false
                }
                s.push_str( & var.default_str() ) ;
                s.push_str( & format!(": {}", typ) ) ;
              }
              s.push_str(") = (or\n") ;

              for & (ref qvars, ref conj) in & def {

                let (suff, pref) = if qvars.is_empty() {
                  (None, "  ")
                } else {
                  s.push_str("  (exists (") ;
                  for (var, typ) in qvars {
                    s.push_str(" (") ;
                    s.push_str( & var.default_str() ) ;
                    s.push_str( & format!(" {})", typ) )
                  }
                  s.push_str(" )\n") ;
                  (Some("  )"), "    ")
                } ;

                s.push_str(pref) ;
                s.push_str("(and\n") ;
                for term in conj.terms() {
                  s.push_str( & format!("{}  {}\n", pref, term) )
                }
                for (pred, argss) in conj.preds() {
                  for args in argss {
                    s.push_str(
                      & format!("{}  ({} {})\n", pref, instance[* pred], args)
                    )
                  }
                }
                s.push_str(pref) ;
                s.push_str(")\n") ;
                if let Some(suff) = suff {
                  s.push_str(suff) ;
                  s.push_str("\n")
                }
              }
              s.push_str(")\n") ;

              log! { @4 "{}", s }
            }

            log! { @4 "  unfolding {}", instance[pred] }

            info += instance.force_dnf_left(pred, def)?;

            preproc_dump!(
              instance =>
                format!("after_force_dnf_left_on_{}", pred),
                "Instance after reaching preproc fixed-point."
            )?;
        }

        Ok(info)
    }
}

impl RedStrat for CfgRed {
    fn name(&self) -> &'static str {
        "cfg_red"
    }

    fn new(instance: &Instance) -> Self {
        CfgRed {
            cnt: 0,
            upper_bound: {
                let clause_count = instance.clauses().len();
                let adjusted = 50. * (clause_count as f64).log(2.);
                ::std::cmp::min(clause_count, (adjusted).round() as usize)
            },
            graph: Graph::new(instance),
        }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        // use std::time::Instant ;
        // use common::profiling::DurationExt ;

        let mut total_info = RedInfo::new();

        loop {
            let mut info = RedInfo::new();

            // let start = Instant::now() ;
            self.graph.setup(instance);
            // let setup_duration = Instant::now() - start ;
            // println!("setup time: {}", setup_duration.to_str()) ;

            self.graph.check(&instance)?;

            // let start = Instant::now() ;
            let mut to_keep = self.graph.break_cycles(instance)?;
            // let breaking_duration = Instant::now() - start ;
            // println!("breaking time: {}", breaking_duration.to_str()) ;

            let no_inlining = instance.no_inlining();
            let no_inlining_preds = instance.no_inlining_preds();
            for p in instance.preds() {
                if no_inlining || no_inlining_preds.contains(&p.name) {
                    to_keep.insert(p.idx);
                }
            }

            self.graph
                .to_dot(&instance, format!("{}_pred_dep_b4", self.cnt), &to_keep)?;

            let pred_defs = self
                .graph
                .inline(instance, &mut to_keep, self.upper_bound)?;

            if pred_defs.is_empty() {
                break;
            }

            info.preds += pred_defs.len();

            self.graph.check(&instance)?;
            if_log! { @verb
                log! { @verb | "inlining {} predicate(s)", pred_defs.len() }
                for (pred, _) in & pred_defs {
                    log! { @verb | "  {}", instance[* pred] }
                }
            }

            if pred_defs.len() == instance.active_pred_count() {
                let (is_sat, this_info) = instance.force_all_preds(pred_defs, false)?;
                info += this_info;
                if !is_sat {
                    unsat!("by preprocessing (all predicates resolved but unsat)")
                } else {
                    total_info += info;
                    break;
                }
            }

            info += self.apply_pred_defs(instance, pred_defs)?;

            // if conf.preproc.log_pred_dep {
            //     self.graph.setup(instance);
            //     self.graph.check(&instance)?;
            //     self.graph.to_dot(
            //         &instance,
            //         format!("{}_pred_dep_reduced", self.cnt),
            //         &to_keep,
            //     )?;
            // }

            self.cnt += 1;

            if info.non_zero() {
                total_info += info
            } else {
                break;
            }
        }

        Ok(total_info)
    }
}

//! Entry point extraction data.
//!
//! Keeps track of the dependencies between positive samples.

use common::*;
use data::sample::Sample;

/// Set of samples.
pub type SampleSet = BTreeSet<Sample>;
/// Map of samples.
pub type SampleMap<T> = BTreeMap<Sample, T>;

/// Type of the solver used for reconstruction.
type Slvr = Solver<smt::FullParser>;

/// Entry point extraction type.
#[derive(Debug, Clone, Default)]
pub struct EntryPoints {
    /// Real positive samples.
    real_pos_samples: SampleSet,
    /// Maps RHS of implication constraints to the real positive samples they are known to depend
    /// on this far.
    pos_sample_map: SampleMap<SampleSet>,
}

impl EntryPoints {
    /// Constructor.
    pub fn new() -> Self {
        EntryPoints {
            real_pos_samples: SampleSet::new(),
            pos_sample_map: SampleMap::new(),
        }
    }

    /// Merges with another entry point tracker.
    pub fn merge(&mut self, other: Self) {
        for sample in other.real_pos_samples {
            self.real_pos_samples.insert(sample);
        }
        for (sample, set) in other.pos_sample_map {
            self.pos_sample_map.entry(sample).or_insert(set);
        }
    }

    /// String representation.
    pub fn to_string(&self, instance: &Instance) -> String {
        let mut s = "real_pos_samples:".to_string();
        for sample in &self.real_pos_samples {
            s += &format!("\n  ({} {})", instance[sample.pred], sample.args)
        }
        s += "\npos_sample_map:";
        for (sample, set) in &self.pos_sample_map {
            s += &format!("\n  ({} {})", instance[sample.pred], sample.args);
            for sample in set {
                s += &format!("\n  -> ({} {})", instance[sample.pred], sample.args)
            }
        }
        s
    }

    /// Registers a positive sample.
    pub fn register(&mut self, sample: Sample) {
        self.real_pos_samples.insert(sample);
    }

    /// Registers a dependency between the RHS of an implication constraint and a positive sample.
    pub fn register_dep(&mut self, sample: Sample, dep: &Sample) -> Res<()> {
        let mut set = self
            .pos_sample_map
            .remove(&sample)
            .unwrap_or_else(SampleSet::new);
        if self.real_pos_samples.contains(dep) {
            set.insert(dep.clone());
        } else if let Some(dep_set) = self.pos_sample_map.get(dep) {
            for sample in dep_set {
                set.insert(sample.clone());
            }
        } else {
            bail!(
                "trying to register dependency to unknown positive sample {}",
                dep
            )
        };
        let prev = self.pos_sample_map.insert(sample, set);
        debug_assert! { prev.is_none() }
        Ok(())
    }

    /// Retrieves the real positive samples corresponding to a sample.
    pub fn entry_points_of(&self, sample: &Sample) -> Res<Entry> {
        if self.real_pos_samples.contains(sample) {
            let samples: SampleSet = vec![sample.clone()].into_iter().collect();
            return Ok(samples.into());
        }
        self.pos_sample_map
            .get(sample)
            .map(|entry| entry.clone().into())
            .ok_or_else::<Error, _>(|| {
                format!(
                    "trying to recover entry points for unknown sample {}",
                    sample
                ).into()
            })
    }
}

/// Entry points leading to a contradiction.
#[derive(Debug, Clone)]
pub struct Entry {
    /// Positive samples leading to a contradiction.
    pub samples: SampleSet,
}

impl From<SampleSet> for Entry {
    fn from(samples: SampleSet) -> Self {
        Entry::new(samples)
    }
}

impl Entry {
    /// Constructor.
    pub fn new(samples: SampleSet) -> Self {
        Entry { samples }
    }

    /// Rewrites the entry points in terms of the original signatures.
    fn rewrite(&self, instance: &Instance) -> Vec<Sample> {
        let mut samples = vec![];

        for Sample { pred, args } in &self.samples {
            let pred = *pred;
            let original_sig = instance[pred].original_sig();
            let mut nu_args = VarMap::with_capacity(original_sig.len());
            for typ in original_sig {
                nu_args.push(val::none(typ.clone()))
            }
            for (var, val) in args.index_iter() {
                let old_var = instance[pred].original_sig_map()[var];
                nu_args[old_var] = val.clone()
            }
            let args = var_to::vals::new(nu_args);
            samples.push(Sample { pred, args })
        }

        samples
    }

    /// Reconstructs some entry points given the original instance.
    pub fn reconstruct(&self, instance: &Instance, original: &Instance) -> Res<Self> {
        let samples = self.rewrite(instance);
        log! { @2 | "reconstructing {} sample(s)", samples.len() }
        let mut solver = conf
            .solver
            .spawn("proof_reconstruction", smt::FullParser, original)?;
        let samples = Reconstr::new(original, instance, samples, &mut solver).work()?;
        Ok(Self::new(samples))
    }
}

// /// Result of looking for antecedents for a positive sample.
// enum AnteRes {
//     /// No antecedent, the sample can be derived from a positive clause.
//     Positive,
//     /// List of conjunction of antecedents leading to this sample.
//     Ante(Vec<SampleSet>),
//     /// Positive sample cannot be derived.
//     Dead,
// }

/// Entry point reconstructor.
struct Reconstr<'a> {
    /// Predicates that are safe to inline: they are defined in the instance mention only other
    /// defined predicates.
    safe_preds: PrdSet,
    /// Predicates that are defined and can be used in positive samples.
    pos_preds: PrdSet,
    /// Original instance.
    original: &'a Instance,
    /// Instance.
    instance: &'a Instance,
    /// Samples to reconstruct.
    to_do: Vec<Sample>,
    /// Positive samples for the original instance.
    samples: SampleSet,
    // /// Stack of things, used when reconstructing a sample.
    // stack: Vec<()>,
    /// Solver.
    solver: &'a mut Slvr,
}

impl<'a> Reconstr<'a> {
    /// Constructor.
    pub fn new(
        original: &'a Instance,
        instance: &'a Instance,
        to_do: Vec<Sample>,
        solver: &'a mut Slvr,
    ) -> Self {
        let pos_preds: PrdSet = original
            .pos_clauses()
            .iter()
            .map(|idx| {
                original[*idx]
                    .rhs()
                    .expect("positive clauses necessarily have a RHS")
                    .0
            }).collect();
        let mut safe_preds = PrdSet::new();
        let mut fp = false;
        while !fp {
            fp = true;
            for pred in instance.preds() {
                if safe_preds.contains(&pred.idx) {
                    continue;
                } else if let Some(def) = pred.def() {
                    if def.preds().is_subset(&safe_preds) {
                        fp = false;
                        safe_preds.insert(pred.idx);
                    }
                }
            }
        }

        if_log! { @3
            if safe_preds.is_empty() {
                log! { @3 |=> "no safe predicates" }
            } else {
                log! { @3 |=> "safe predicates:" }
                for pred in &safe_preds {
                    log! { @3 |=> "  {}", instance[*pred] }
                }
            }
        }

        Reconstr {
            safe_preds,
            pos_preds,
            original,
            instance,
            to_do,
            solver,
            samples: SampleSet::new(),
        }
    }

    /// Finds clauses of the original instance elligible for reconstruction for a predicate.
    ///
    /// Returns
    ///
    /// - the positive clauses in which `pred` appears,
    /// - the clauses in which `pred` is the rhs and *all* predicates in the LHS are defined in the
    ///   instance.
    fn clauses_for(&self, pred: PrdIdx) -> (Vec<ClsIdx>, Vec<ClsIdx>) {
        let mut pos = vec![];
        let mut others = vec![];
        for clause_idx in self.original.rhs_clauses_of(pred) {
            let clause_preds = self.original[*clause_idx].lhs_preds();
            if clause_preds.is_empty() {
                pos.push(*clause_idx)
            } else if clause_preds
                .keys()
                .all(|pred| self.safe_preds.contains(pred))
            {
                others.push(*clause_idx)
            }
        }
        (pos, others)
    }

    /// Tries to reconstruct a positive sample from a clause.
    ///
    /// Returns `true` if the reconstruction was positive. If it was, (potentially) new positive
    /// samples have been added to `self.samples`.
    fn work_on_clause(&mut self, pred: PrdIdx, sample: &VarVals, clause: ClsIdx) -> Res<bool> {
        debug_assert! { self.original[clause].rhs().map(|(p, _)| p == pred).unwrap_or(false) }
        self.solver.push(1)?;
        // Declare clause variables.
        self.original[clause].declare(self.solver)?;
        // Assert lhs terms.
        for term in self.original[clause].lhs_terms() {
            self.solver.assert(&smt::SmtTerm::new(term))?;
        }
        // Assert lhs preds.
        for (pred, argss) in self.original[clause].lhs_preds() {
            for args in argss {
                self.solver.assert_with(
                    &smt::SmtPredApp::new(*pred, args),
                    (self.instance.preds(), true),
                )?
            }
        }

        if let Some((p, args)) = self.original[clause].rhs() {
            debug_assert_eq! { pred, p }
            self.solver.assert(&smt::EqConj::new(args, &sample))?
        } else {
            bail!("proof reconstruction, illegal clause-level call (no rhs)")
        }

        let sat = self.solver.check_sat()?;

        let model = if sat {
            let model = self.solver.get_model()?;
            Some(smt::FullParser.fix_model(model)?)
        } else {
            None
        };

        self.solver.pop(1)?;

        if let Some(model) = model {
            let model = Cex::of_model(self.original[clause].vars(), model, true)?;
            // Reconstruct all LHS applications.
            for (pred, argss) in self.original[clause].lhs_preds() {
                let mut samples = vec![];
                for args in argss {
                    let mut sample = VarMap::with_capacity(args.len());
                    for arg in args.iter() {
                        let val = arg.eval(&model)?;
                        sample.push(val)
                    }
                    samples.push(Sample::new(*pred, var_to::vals::new(sample)))
                }
                if self.pos_preds.contains(pred) {
                    if_log! { @5
                        log! { @5 |=> "generated positive samples:" }
                        for sample in &samples {
                            log! { @5 |=> "  ({} {})", self.original[sample.pred], sample.args }
                        }
                    }
                    self.samples.extend(samples.into_iter())
                } else {
                    if_log! { @5
                        log! { @5 |=> "generated new samples:" }
                        for sample in &samples {
                            log! { @5 |=> "  ({} {})", self.original[sample.pred], sample.args }
                        }
                    }
                    self.to_do.extend(samples.into_iter())
                }
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Reconstructs a sample using the definitions of the positive predicates.
    fn work_on_defs(&mut self, pred: PrdIdx, vals: &VarVals) -> Res<bool> {
        let mut current_pred = PrdSet::with_capacity(1);
        current_pred.insert(pred);

        log! { @4 "trying to reconstruct from {} definition(s)", self.pos_preds.len() }

        'find_pos_pred: for pos_pred in &self.pos_preds {
            let pos_pred = *pos_pred;
            if let Some(def) = self.instance[pos_pred].def() {
                let mut pred_args = None;
                for pred_apps in def.pred_apps() {
                    'current_apps: for (p, argss) in pred_apps {
                        if self.safe_preds.contains(p) {
                            continue 'current_apps;
                        } else if *p == pred {
                            for args in argss {
                                let prev = ::std::mem::replace(&mut pred_args, Some(args));
                                if prev.is_some() {
                                    continue 'find_pos_pred;
                                }
                            }
                        } else {
                            continue 'find_pos_pred;
                        }
                    }
                }

                let pred_args = if let Some(args) = pred_args {
                    args
                } else {
                    continue 'find_pos_pred;
                };

                log! { @5
                    "positive predicate {} mentions {}: ({} {})",
                    self.instance[pos_pred], self.instance[pred], self.instance[pred], pred_args
                }

                self.solver.push(1)?;

                for (var, typ) in self.original[pos_pred].sig.index_iter() {
                    self.solver.declare_const(&var, typ.get())?;
                }

                self.solver
                    .assert_with(def, &(&current_pred, &PrdSet::new(), self.instance.preds()))?;

                self.solver.assert(&smt::EqConj::new(pred_args, vals))?;

                let sat = self.solver.check_sat()?;

                let model = if sat {
                    let model = self.solver.get_model()?;
                    Some(smt::FullParser.fix_model(model)?)
                } else {
                    None
                };

                self.solver.pop(1)?;

                if let Some(model) = model {
                    log! { @5 "sat, getting sample" }
                    let vals = Cex::of_pred_model(&self.original[pos_pred].sig, model, true)?;
                    let vals = var_to::vals::new(vals);
                    self.samples.insert(Sample::new(pos_pred, vals));
                    return Ok(true);
                } else {
                    log! { @5 "unsat" }
                }
            }
        }
        Ok(false)
    }

    /// Reconstructs a single positive sample.
    fn work_on_sample(&mut self, Sample { pred, args }: Sample) -> Res<()> {
        log! { @3 | "working on ({} {})", self.instance[pred], args }

        // Already an entry point for the original instance?
        if self.pos_preds.contains(&pred) {
            log! { @4 | "already a legal entry point" }
            self.samples.insert(Sample::new(pred, args));
            return Ok(());
        }

        // Try reconstructing by using predicate definitions directly.
        let done = self.work_on_defs(pred, &args)?;
        if done {
            return Ok(());
        }

        let (pos, others) = self.clauses_for(pred);
        log! { @4 | "{} positive clause(s), {} usable clause(s)", pos.len(), others.len() }
        if_log! { @5
            if ! pos.is_empty() {
                log! { @4 |=> "positive clause(s)" }
                for idx in &pos {
                    log! { @5 => "{}", self.original[*idx].to_string_info(self.original.preds())? }
                }
            }
            if ! others.is_empty() {
                log! { @4 |=> "usable clause(s)" }
                for idx in &others {
                    log! { @5 => "{}", self.original[*idx].to_string_info(self.original.preds())? }
                }
            }
        }

        for clause in pos {
            let okay = self.work_on_clause(pred, &args, clause)?;
            if okay {
                log! { @3 | "  reconstructed using positive clause #{}", clause }
                return Ok(());
            }
        }
        for clause in others {
            let okay = self.work_on_clause(pred, &args, clause)?;
            if okay {
                log! { @3 | "  reconstructed using non-positive clause #{}", clause }
                return Ok(());
            }
        }

        bail!(
            "could not reconstruct sample ({} {})",
            self.instance[pred],
            args
        )
    }

    /// Reconstructs the positive samples.
    pub fn work(mut self) -> Res<SampleSet> {
        if !self.safe_preds.is_empty() {
            let model = self.instance.extend_model(PrdHMap::new())?;
            self.instance.write_definitions(self.solver, "", &model)?
        }

        if_log! { @4
            log! { @4 |=> "{} safe preds", self.safe_preds.len() }
            for pred in &self.safe_preds {
                log! { @4 |=> "  {}", self.instance[*pred] }
            }
            log! { @4 |=> "{} pos preds", self.pos_preds.len() }
            for pred in &self.pos_preds {
                log! { @4 |=> "  {}", self.instance[*pred] }
            }
        }

        while let Some(sample) = self.to_do.pop() {
            if let Err(e) = self.work_on_sample(sample.clone()) {
                print_err(&e);
                self.samples.insert(sample);
            }
        }

        self.solver.reset()?;
        Ok(self.samples)
    }
}

//! Entry point extraction.
//!
//! Keeps track of the dependencies between positive samples. When unsat proof production is
//! active, the [learning data] will maintain an [`EntryPoints` tracker]. From this tracker, if a
//! conflict is discovered, one can extract the actual unsat proof in the form of entry points.
//!
//! *Entry points* are samples for (some of) the positive clauses of the instance that lead to the
//! conflict. This only makes sense if the instance corresponds to a (deterministic) program. That
//! is, it is possible to execute the program from the entry points to find the conflict again. To
//! put differently, there is no non-deterministic choices to make: *e.g.* there never is two
//! clauses that can be activated at the same time using the same samples (arguments for a
//! predicate application).
//!
//! [learning data]: ../../data/index.html (learning data module)
//! [`EntryPoints` tracker]: struct.EntryPoints.html (EntryPoints struct)

use crate::{common::*, data::sample::Sample};

/// Set of samples.
pub type SampleSet = BTreeSet<Sample>;
/// Map of samples.
pub type SampleMap<T> = BTreeMap<Sample, T>;

/// Type of the solver used for reconstruction.
type Slvr = Solver<smt::FullParser>;

/// Entry point extraction structure.
///
/// This type distinguishes two kinds of positive samples: *real* ones and the rest. A *real*
/// positive sample is a sample obtained directly from a positive clause.
///
/// For instance, say that we have positive Horn clause `n = 2 => P(n)` (1) and `n >= 0 /\ P(n) =>
/// P(n+1)` (2). Then `P(2)` is a real positive sample by (1). Say at some point we get the
/// implication constraint `P(2) => P(3)`: we know right away that `P(3)` has to be positive since
/// `P(2)` is. But `P(3)` is not a *real* positive sample: it does not come directly from a
/// positive clause.
///
/// This structures remembers the real positive samples, and has a map associating a non-real
/// positive sample `P(s)` to the real positive samples that led to classifying `P(s)` as positive.
#[derive(Debug, Clone, Default)]
pub struct EntryPoints {
    /// Real positive samples.
    real_pos_samples: SampleSet,
    /// Maps positive samples that are not real to the real positive samples to infer them.
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

    /// Accessor for real positive samples.
    pub fn real_pos_set(&self) -> &SampleSet {
        &self.real_pos_samples
    }
    /// Accessor for the map from samples to real positive samples.
    pub fn map(&self) -> &SampleMap<SampleSet> {
        &self.pos_sample_map
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[macro_use]
    /// extern crate hoice;
    /// use hoice::{
    ///     common::*, unsat_core::entry_points::EntryPoints, data::sample::Sample,
    ///     var_vals
    /// } ;
    ///
    /// # fn main() {
    /// let mut entry = EntryPoints::new();
    /// let pred: PrdIdx = 0.into();
    /// let s_1 = &Sample::new(pred, var_vals!( (int 1) (bool true) ));
    /// entry.register(s_1.clone());
    /// let s_2 = &Sample::new(pred, var_vals!( (int 7) (bool true) ));
    /// entry.register(s_2.clone());
    /// assert_eq! { entry.real_pos_set().len(), 2 }
    /// assert! { entry.real_pos_set().contains(s_1) }
    /// assert! { entry.real_pos_set().contains(s_2) }
    /// # }
    /// ```
    pub fn register(&mut self, sample: Sample) {
        self.real_pos_samples.insert(sample);
    }

    /// Registers a dependency between the RHS of an implication constraint and a positive sample.
    ///
    /// Fails if the dependency sample (second argument) is unknown (see below).
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[macro_use]
    /// extern crate hoice;
    /// use hoice::{
    ///     common::*, unsat_core::entry_points::EntryPoints, data::sample::Sample,
    ///     var_vals
    /// } ;
    ///
    /// # fn main() {
    /// let mut entry = EntryPoints::new();
    /// let pred: PrdIdx = 0.into();
    /// let s_1 = &Sample::new(pred, var_vals!( (int 1) (bool true) ));
    /// entry.register(s_1.clone());
    ///
    /// let s_2 = &Sample::new(pred, var_vals!( (int 7) (bool true) ));
    /// entry.register_dep(s_2.clone(), s_1).unwrap();
    /// assert_eq! { entry.real_pos_set().len(), 1 }
    /// assert! { entry.real_pos_set().contains(s_1) }
    /// {
    ///     let s_2_dep = entry.map().get(s_2).unwrap();
    ///     assert_eq! { s_2_dep.len(), 1 }
    ///     assert! { s_2_dep.contains(s_1) }
    /// }
    ///
    /// let s_3 = &Sample::new(pred, var_vals!( (int 42) (bool false) ));
    /// entry.register_dep(s_3.clone(), s_2).unwrap();
    /// assert_eq! { entry.real_pos_set().len(), 1 }
    /// assert! { entry.real_pos_set().contains(s_1) }
    /// {
    ///     let s_3_dep = entry.map().get(s_3).unwrap();
    ///     assert_eq! { s_3_dep.len(), 1 }
    ///     assert! { s_3_dep.contains(s_1) }
    /// }
    /// # }
    /// ```
    ///
    /// Failure on inexistent real positive sample.
    ///
    /// ```rust
    /// #[macro_use]
    /// extern crate hoice;
    /// use hoice::{
    ///     common::*, unsat_core::entry_points::EntryPoints, data::sample::Sample,
    ///     var_vals
    /// } ;
    ///
    /// # fn main() {
    /// let mut entry = EntryPoints::new();
    /// let pred: PrdIdx = 0.into();
    /// let s_1 = &Sample::new(pred, var_vals!( (int 1) (bool true) ));
    ///
    /// let s_2 = &Sample::new(pred, var_vals!( (int 7) (bool true) ));
    /// if let Err(e) = entry.register_dep(s_2.clone(), s_1) {
    ///     assert_eq! {
    ///         format!("{}", e),
    ///         "trying to register dependency to unknown positive sample (p_0 1 true)"
    ///     }
    /// } else { panic!("should have failed") }
    /// # }
    /// ```
    pub fn register_dep(&mut self, sample: Sample, dep: &Sample) -> Res<()> {
        let mut set = self
            .pos_sample_map
            .remove(&sample)
            .unwrap_or_else(SampleSet::new);

        let mut real_dep = None;
        for s in &self.real_pos_samples {
            if s.pred == dep.pred && s.args.subsumes(&dep.args) {
                real_dep = Some(s.clone());
                break;
            }
        }

        if let Some(res) = real_dep {
            set.insert(res);
        } else {
            set.extend(
                self.pos_sample_map
                    .get(dep)
                    .ok_or_else::<Error, _>(|| {
                        format!(
                            "trying to register dependency to unknown positive sample ({})",
                            dep
                        )
                        .into()
                    })?
                    .iter()
                    .cloned(),
            )
        }

        let prev = self.pos_sample_map.insert(sample, set);
        debug_assert! { prev.is_none() }
        Ok(())
    }

    /// Merges with another entry point tracker.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[macro_use]
    /// extern crate hoice;
    /// use hoice::{
    ///     common::*, unsat_core::entry_points::EntryPoints, data::sample::Sample,
    ///     var_vals
    /// } ;
    ///
    /// # fn main() {
    /// let mut entry = EntryPoints::new();
    /// let pred: PrdIdx = 0.into();
    /// let s_1 = &Sample::new(pred, var_vals!( (int 1) (bool true) ));
    /// entry.register(s_1.clone());
    /// let s_1_1 = &Sample::new(pred, var_vals!( (int 11) (bool true) ));
    /// entry.register(s_1_1.clone());
    ///
    /// let s_2 = &Sample::new(pred, var_vals!( (int 7) (bool true) ));
    /// entry.register_dep(s_2.clone(), s_1).unwrap();
    ///
    /// let s_3 = &Sample::new(pred, var_vals!( (int 42) (bool false) ));
    /// entry.register_dep(s_3.clone(), s_2).unwrap();
    /// entry.register_dep(s_3.clone(), s_1_1).unwrap();
    ///
    /// let mut entry_2 = EntryPoints::new();
    /// entry_2.register(s_1.clone());
    /// let s_4 = &Sample::new(pred, var_vals!( (int 0) (bool false) ));
    /// entry_2.register(s_4.clone());
    /// let s_5 = &Sample::new(pred, var_vals!( (int 0) (bool false) ));
    /// entry_2.register_dep(s_5.clone(), s_4).unwrap();
    /// entry_2.register_dep(s_5.clone(), s_1).unwrap();
    ///
    /// entry.merge(entry_2);
    /// let mut instance = Instance::new();
    /// instance.push_pred("p_0", vec![typ::int(), typ::bool()].into());
    ///
    /// assert_eq! {
    ///     format!("{}", entry.to_string(&instance)), "\
    /// real_pos_samples:
    ///   (p_0 1 true)
    ///   (p_0 11 true)
    ///   (p_0 0 false)
    /// pos_sample_map:
    ///   (p_0 7 true)
    ///   -> (p_0 1 true)
    ///   (p_0 42 false)
    ///   -> (p_0 1 true)
    ///   -> (p_0 11 true)
    ///   (p_0 0 false)
    ///   -> (p_0 1 true)
    ///   -> (p_0 0 false)\
    ///     "
    /// }
    /// # }
    /// ```
    pub fn merge(&mut self, other: Self) {
        for sample in other.real_pos_samples {
            self.real_pos_samples.insert(sample);
        }
        for (sample, set) in other.pos_sample_map {
            self.pos_sample_map.entry(sample).or_insert(set);
        }
    }

    /// Retrieves the real positive samples corresponding to a sample.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[macro_use]
    /// extern crate hoice;
    /// use hoice::{
    ///     common::*, unsat_core::entry_points::EntryPoints, data::sample::Sample,
    ///     var_vals
    /// } ;
    ///
    /// # fn main() {
    /// let mut entry = EntryPoints::new();
    /// let pred: PrdIdx = 0.into();
    /// let s_1 = &Sample::new(pred, var_vals!( (int 1) (bool true) ));
    /// entry.register(s_1.clone());
    /// // s_1 is positive
    /// let s_1_1 = &Sample::new(pred, var_vals!( (int 11) (bool true) ));
    /// entry.register(s_1_1.clone());
    /// // s_1_1 is positive
    ///
    /// let s_2 = &Sample::new(pred, var_vals!( (int 7) (bool true) ));
    /// entry.register_dep(s_2.clone(), s_1).unwrap();
    /// // s_1 => s_2, hence the "positiveness" of s_2 depends on s_1
    ///
    /// let s_3 = &Sample::new(pred, var_vals!( (int 42) (bool false) ));
    /// entry.register_dep(s_3.clone(), s_2).unwrap();
    /// // s_2 => s_3, hence the "positiveness" of s_3 depends on s_2 which depends on s_1
    /// entry.register_dep(s_3.clone(), s_1_1).unwrap();
    /// // s_1_1 => s_3, hence the "positiveness" of s_3 depends on s_1_1
    /// let s_3_dep = entry.entry_points_of(s_3).expect("while retrieving s_3's entry points");
    /// assert_eq! { s_3_dep.samples.len(), 2 }
    /// assert! { s_3_dep.samples.contains(s_1) }
    /// assert! { s_3_dep.samples.contains(s_1_1) }
    /// # }
    /// ```
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
                    "trying to recover entry points for unknown sample ({})",
                    sample
                )
                .into()
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

/// Entry point reconstructor.
///
/// Handles the difference between the instance hoice worked on and found a conflict for, and the
/// original ones so that the entry points are in terms of the user's instance.
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
    ///
    /// Each element of the vector is a path toward what we're reconstructing. If we're trying to
    /// reconstruct `(p vals)`, then several path are created for this sample if there are more
    /// than one clauses that lead to this sample.
    to_do: Vec<Vec<Sample>>,
    /// Positive samples for the original instance.
    samples: SampleSet,
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
        let to_do = vec![to_do];
        let pos_preds: PrdSet = original
            .pos_clauses()
            .iter()
            .map(|idx| {
                original[*idx]
                    .rhs()
                    .expect("positive clauses necessarily have a RHS")
                    .0
            })
            .collect();
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
    ///   instance or appear in a positive clause.
    fn clauses_for(&self, pred: PrdIdx) -> (Vec<ClsIdx>, Vec<ClsIdx>) {
        let mut pos = vec![];
        let mut others = vec![];
        log! {
            @4 | "retrieving {} clause(s) for {}",
            self.original.rhs_clauses_of(pred).len(), self.original[pred]
        }
        for clause_idx in self.original.rhs_clauses_of(pred) {
            log! {
                @5 "{}", self.original[*clause_idx].to_string_info(&self.original.preds()).unwrap()
            }
            let clause_preds = self.original[*clause_idx].lhs_preds();
            if clause_preds.is_empty() {
                pos.push(*clause_idx)
            } else if clause_preds.keys().all(|pred| {
                self.instance[*pred].is_defined()
                    || self.safe_preds.contains(pred)
                    || self.pos_preds.contains(pred)
            }) {
                others.push(*clause_idx)
            }
        }
        (pos, others)
    }

    /// Tries to reconstruct a positive sample from a clause.
    ///
    /// Returns `true` if the reconstruction was positive. If it was, (potentially) new positive
    /// samples have been added to `self.samples`.
    fn work_on_clause(
        &mut self,
        pred: PrdIdx,
        sample: &VarVals,
        clause: ClsIdx,
    ) -> Res<Option<Vec<Vec<Sample>>>> {
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
            bail!("proof reconstruction: illegal clause-level call (no rhs)")
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
            let mut res = vec![];
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
                    res.push(samples)
                } else {
                    if_log! { @5
                        log! { @5 |=> "generated new samples:" }
                        for sample in &samples {
                            log! { @5 |=> "  ({} {})", self.original[sample.pred], sample.args }
                        }
                    }
                    res.push(samples)
                }
            }
            Ok(Some(res))
        } else {
            Ok(None)
        }
    }

    /// Reconstructs a sample using the definitions of the positive predicates.
    ///
    /// Returns `true` if the sample was discovered to be positive.
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
    ///
    /// Returns `true` if the sample was found to be a legal positive sample for the original
    /// instance.
    fn work_on_sample(&mut self, Sample { pred, args }: Sample, path: &Vec<Sample>) -> Res<bool> {
        log! { @3 | "working on ({} {})", self.instance[pred], args }

        // Already an entry point for the original instance?
        if self.pos_preds.contains(&pred) {
            log! { @4 | "already a legal entry point" }
            self.samples.insert(Sample::new(pred, args));
            return Ok(true);
        }

        // Try reconstructing by using predicate definitions directly.
        let done = self.work_on_defs(pred, &args)?;
        if done {
            return Ok(true);
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
            if let Some(steps) = self.work_on_clause(pred, &args, clause)? {
                if !steps.is_empty() {
                    debug_assert! { steps.iter().all(|step| step.is_empty()) }
                    log! { @3 | "  reconstructed using positive clause #{}", clause }
                    return Ok(true);
                }
            }
        }
        let mut clause_count = 0;
        for clause in others {
            if let Some(steps) = self.work_on_clause(pred, &args, clause)? {
                log! {
                    @3 | "  reconstructed using non-positive clause #{}, {} step(s)",
                    clause, steps.len()
                }
                clause_count += 1;
                for step in steps {
                    let mut path = path.clone();
                    path.extend(step.into_iter());
                    self.to_do.push(path)
                }
            }
        }

        if clause_count == 0 {
            // Reconstruction failed. This can be okay, when there are more than one path and the
            // current one has no solution.
            log! { @3
                "could not reconstruct sample ({} {})",
                self.instance[pred],
                args
            }
        }
        Ok(false)
    }

    /// Generates a sample for each positive clause.
    pub fn samples_of_pos_clauses(&mut self) -> Res<()> {
        for clause in self.original.pos_clauses() {
            let clause = *clause;
            let (pred, args) = self.original[clause].rhs().ok_or_else::<Error, _>(|| {
                "illegal (original) instance state, positive clause has no RHS".into()
            })?;

            debug_assert! { self.original[clause].lhs_preds().is_empty() }

            self.solver.push(1)?;
            // Declare clause variables.
            self.original[clause].declare(self.solver)?;
            // Assert lhs terms.
            for term in self.original[clause].lhs_terms() {
                self.solver.assert(&smt::SmtTerm::new(term))?;
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
                let mut sample = VarMap::with_capacity(args.len());
                for arg in args.iter() {
                    let val = arg.eval(&model)?;
                    sample.push(val)
                }
                self.samples
                    .insert(Sample::new(pred, var_to::vals::new(sample)));
            }
        }

        Ok(())
    }

    /// Reconstructs the positive samples.
    pub fn work(mut self) -> Res<SampleSet> {
        if self.to_do.iter().all(|to_do| to_do.is_empty()) {
            log! { @4 | "no samples to reconstruct, generating samples from positive clauses" }
            self.samples_of_pos_clauses()?;
            log! { @4 | "done, generated {} sample(s)", self.samples.len() }
            return Ok(self.samples);
        }

        if !self.safe_preds.is_empty() {
            for pred in self.instance.preds() {
                if !pred.is_defined() {
                    let sig: Vec<_> = pred.original_sig().iter().map(|typ| typ.get()).collect();
                    self.solver.declare_fun(&pred.name, &sig, "Bool")?
                }
            }
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

        'all_branches: while let Some(mut to_do) = self.to_do.pop() {
            if_log! { @3
                log! { @3 |=> "to_do {} other branch(es):", self.to_do.len() }
                for sample in &to_do {
                    log! { @3 |=> "  ({} {})", self.instance[sample.pred], sample.args }
                }
            }
            while let Some(sample) = to_do.pop() {
                match self.work_on_sample(sample.clone(), &to_do) {
                    Err(e) => {
                        print_err(&e);
                        self.samples.insert(sample);
                    }
                    Ok(true) => {
                        log! { @4 | "positive" }
                        // This sample was positive, keep going in the current branch.
                        ()
                    }
                    Ok(false) => {
                        log! { @4 | "new branches" }
                        // New branches to explore, keep going.
                        continue 'all_branches;
                    }
                }
            }

            // Reachable if all samples in `to_do` have been explained positively.
            log! { @3 |
                "solution found, discarding {} remaining path(s)", self.to_do.len()
            }
            self.to_do.clear();
            break 'all_branches;
        }

        self.solver.reset()?;

        if self.samples.is_empty() {
            bail!("could not reconstruct entry points")
        }

        Ok(self.samples)
    }
}

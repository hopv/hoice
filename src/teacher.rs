//! Checks candidates and sends data to learner(s).
//!
//! [teach]: fn.teach.html
//! (Teacher's teach function)

use std::time::Duration;

use crate::{
    common::{
        msg::*,
        smt::{FullParser as Parser, SmtTerm},
        *,
    },
    data::Data,
    unsat_core::UnsatRes,
};

pub mod assistant;
mod cex_bias;
use self::assistant::Assistant;

pub use self::cex_bias::CexBias;

/// Starts the teaching process.
///
/// The partial model stores conjunction of top terms for some of the top
/// terms, and is expressed in terms of the predicates' original signatures.
pub fn start_class(
    instance: Arc<Instance>,
    partial_model: &ConjCandidates,
    profiler: &Profiler,
) -> Res<TeachRes> {
    log! { @debug
        "starting the learning process" ;
        "  launching solver kid..."
    }
    let mut teacher = Teacher::new(instance, profiler, partial_model)?;

    let res = match teach(&mut teacher) {
        Ok(res) => Ok(res),

        Err(e) => match e.kind() {
            ErrorKind::Unsat => {
                warn! {
                "legacy unsat (by error) result triggered\n\
                unsat core will not be available\n\
                please consider contacting the developer"
                }
                let core = teacher.unsat_core()?;
                Ok(TeachRes::Unsat(core))
            }

            _ => {
                if let Err(tmo) = conf.check_timeout() {
                    Err(tmo)
                } else {
                    Err(e)
                }
            }
        },
    };

    teacher.finalize()?;
    res
}

/// Teaching to the learners.
pub fn teach(teacher: &mut Teacher) -> Res<TeachRes> {
    log_debug! { "spawning ice learner(s)..." }
    if conf.ice.pure_synth {
        teacher.add_learner(crate::learning::ice::Launcher, false)?;
    }
    teacher.add_learner(crate::learning::ice::Launcher, true)?;

    if let Some(res) = teacher.init()? {
        return Ok(res);
    }

    // Index of the learner the teacher is currently working for.
    //
    // None at the beginning (broadcast).
    let mut learner: Option<LrnIdx> = None;

    loop {
        log_verb! {
          "all learning data:\n{}", teacher.data.string_do(
            & (), |s| s.to_string()
          ) ?
        }

        if let Some(idx) = learner {
            if conf.teacher.step {
                pause(
                    &format!(
                        "to send data to {}... (--step on)",
                        &conf.emph(&teacher.learners[idx].1)
                    ),
                    &teacher._profiler,
                );
            }
            let _ = teacher.send(idx)?;
            ()
        } else {
            if conf.teacher.step {
                pause("to broadcast data... (--step on)", &teacher._profiler);
            }
            let one_alive = teacher.broadcast();
            if !one_alive {
                unknown!("all learners are dead")
            }
        }

        // if teacher.data.is_unsat().is_some() {
        //   return Ok(Either::Right(teacher.unsat_core()))
        // }

        match teacher.get_candidates(false)? {
            // Unsat result, done.
            Either::Right(unsat) => return Ok(TeachRes::Unsat(unsat)),

            // Got a candidate.
            Either::Left((idx, candidates)) => {
                learner = Some(idx);
                if let Some(res) = teacher.handle_candidates(candidates, idx)? {
                    return Ok(res);
                }
            }
        }
    }
}

/// The teacher, stores a solver.
pub struct Teacher<'a> {
    /// The solver.
    pub solver: Solver<Parser>,

    /// The (shared) instance.
    pub instance: Arc<Instance>,
    /// Learning data.
    pub data: Data,

    /// Receiver.
    pub from_learners: Receiver<Msg>,
    /// Sender used by learners. Becomes `None` when the learning process starts.
    pub to_teacher: Option<Sender<Msg>>,

    /// Learners sender and description.
    ///
    /// Stores the channel to the learner, its name (for log), and a flag
    /// indicating whether the data has changed since this learner's last
    /// candidates.
    pub learners: LrnMap<(Option<Sender<FromTeacher>>, String, bool)>,
    /// Assistant for implication constraint breaking.
    ///
    /// The boolean flag indicates whether the assistant was sent some stuff.
    // pub assistant: Option< (Sender<FromTeacher>, bool) >,
    pub assistant: Option<Assistant>,
    /// Profiler.
    pub _profiler: &'a Profiler,

    /// Predicates that are true in the current candidate.
    tru_preds: PrdSet,
    /// Predicates that are true in the current candidate.
    fls_preds: PrdSet,
    /// Clauses that are trivially verified in the current candidate.
    clauses_to_ignore: ClsSet,

    /// Helper for cex bias.
    bias: CexBias,

    /// Partial candidate, only really contains stuff when in split mode.
    ///
    /// Used to further constrain the learner's candidates using previous
    /// results, when in split mode.
    partial_model: PrdHMap<Term>,
    /// Map from
    /// Number of guesses.
    count: usize,

    /// True if some recursive functions are defined.
    using_rec_funs: bool,
    /// Forces to restart the solver after each check.
    restart_on_cex: bool,
}

impl<'a> Teacher<'a> {
    /// Constructor.
    pub fn new(
        instance: Arc<Instance>,
        profiler: &'a Profiler,
        partial_model: &'a ConjCandidates,
    ) -> Res<Self> {
        let solver = conf.solver.spawn("teacher", Parser, &instance)?;

        // let partial_model = PrdHMap::new() ;
        let partial_model = partial_model
            .iter()
            .filter_map(|(pred, tterms_vec)| {
                let subst = instance.map_from_original_sig_of(*pred);
                let conj: Vec<_> = tterms_vec
                    .iter()
                    .filter_map(|tterms| {
                        if let Some(term) = tterms.to_term() {
                            term.subst_total(&subst).map(|(term, _)| term)
                        } else {
                            None
                        }
                    })
                    .collect();

                if conj.is_empty() {
                    None
                } else {
                    profile! {
                      |profiler| "partial model reuse" => add 1
                    }
                    Some((*pred, term::and(conj)))
                }
            })
            .collect();

        let learners = LrnMap::with_capacity(2);
        let (to_teacher, from_learners) = Msg::channel();
        let data = Data::new(instance.clone());

        let assistant = if conf.teacher.assistant {
            Some(
                Assistant::new(instance.clone())
                    .chain_err(|| "while spawning assistant".to_string())?,
            )
        } else {
            None
        };

        let mut using_rec_funs = false;

        fun::iter(|_| {
            using_rec_funs = true;
            Ok(())
        })?;

        let restart_on_cex =
            conf.teacher.restart_on_cex || !dtyp::get_all().is_empty() || using_rec_funs;

        Ok(Teacher {
            solver,
            instance,
            data,
            from_learners,
            to_teacher: Some(to_teacher),
            learners,
            assistant,
            _profiler: profiler,
            partial_model,
            count: 0,
            tru_preds: PrdSet::new(),
            fls_preds: PrdSet::new(),
            clauses_to_ignore: ClsSet::new(),
            bias: CexBias::new(),
            using_rec_funs,
            restart_on_cex,
        })
    }

    /// Model from some candidates.
    fn model_of_candidates(&self, mut cands: Candidates) -> Candidates {
        for (pred, cand) in cands.index_iter_mut() {
            if let Some(cand) = cand.as_mut() {
                if let Some(other) = self.instance[pred].strength() {
                    *cand = term::and(vec![cand.clone(), other.clone()])
                }
            }
        }
        cands
    }

    /// Completes some candidates with partial-model and partial-defs.
    fn complete_candidates(&self, mut cands: Candidates) -> Candidates {
        for (pred, cand) in cands.index_iter_mut() {
            if let Some(cand) = cand.as_mut() {
                let mut others = None;
                if let Some(other) = self.instance[pred].strength() {
                    others.get_or_insert_with(Vec::new).push(other.clone())
                }
                if let Some(other) = self.partial_model.get(&pred) {
                    others.get_or_insert_with(Vec::new).push(other.clone())
                }
                if let Some(mut others) = others {
                    others.push(cand.clone());
                    *cand = term::and(others)
                }
            }
        }
        cands
    }

    /// Runs the initial check and registers the data.
    pub fn init(&mut self) -> Res<Option<TeachRes>> {
        log_debug! { "performing initial check..." }
        let (cexs, cands) = self.initial_check()?;
        if cexs.is_empty() {
            log_debug! { "solved by initial candidate..." }
            return Ok(Some(TeachRes::Model(self.model_of_candidates(cands))));
        }

        log_debug! { "generating data from initial cex..." }
        let nu_stuff = self.instance.cexs_to_data(&mut self.data, cexs)?;
        if !nu_stuff {
            bail! { "translation of initial cexs to data generated no new data" }
        }
        self.run_assistant()?;

        Ok(None)
    }

    /// Runs the assistant (if any) on the current data.
    pub fn run_assistant(&mut self) -> Res<()> {
        if let Some(assistant) = self.assistant.as_mut() {
            if let Some(mut data) = self.data.to_ass_data()? {
                profile! { self tick "assistant" }
                assistant.break_implications(&mut data)?;
                let (_nu_pos, _nu_neg) = self.data.merge_samples(data)?;
                profile! { self mark "assistant" }
                profile! { self "assistant pos useful" => add _nu_pos }
                profile! { self "assistant neg useful" => add _nu_neg }
            }
        }
        Ok(())
    }

    /// Finalizes the run.
    pub fn finalize(mut self) -> Res<()> {
        for set in self.data.pos.iter() {
            for sample in set {
                if sample.is_partial() {
                    profile! { self "partial pos samples" => add 1 }
                }
            }
        }
        for set in self.data.neg.iter() {
            for sample in set {
                if sample.is_partial() {
                    profile! { self "partial neg samples" => add 1 }
                }
            }
        }
        self.solver.kill().chain_err(|| "While killing solver")?;
        for &mut (ref mut sender, _, _) in self.learners.iter_mut() {
            if let Some(sender) = sender.as_ref() {
                let _ = sender.send(FromTeacher::Exit);
                ()
            }
            *sender = None
        }

        if let Some(assistant) = self.assistant {
            let profiler = assistant.finalize()?;
            self._profiler.add_sub("assistant", profiler)
        }
        self.assistant = None;
        log_debug! { "draining messages" }
        while let Ok(_) = self.get_candidates(true) {}

        if conf.stats {
            self._profiler.add_sub("data", self.data.destroy())
        }
        Ok(())
    }

    /// Adds a new learner.
    pub fn add_learner<L>(&mut self, learner: L, mine: bool) -> Res<()>
    where
        L: Learner + 'static,
    {
        if let Some(to_teacher) = self.to_teacher.clone() {
            let index = self.learners.next_index();
            let name = learner.description(mine);
            let instance = self.instance.clone();
            let data = self.data.to_lrn_data();
            let (to_learner, learner_recv) = FromTeacher::channel();
            ::std::thread::Builder::new()
                .name(name.clone())
                .spawn(move || {
                    learner.run(
                        MsgCore::new_learner(index, to_teacher.clone(), learner_recv),
                        instance,
                        data,
                        mine,
                    )
                })
                .chain_err(|| format!("while spawning learner `{}`", conf.emph(&name)))?;
            self.learners.push((Some(to_learner), name, false));
            Ok(())
        } else {
            bail!("trying to add learner after teacher's finalization")
        }
    }

    /// Broadcasts data to the learners. Returns `true` if there's no more
    /// learner left.
    ///
    /// Only used for the data from the first check.
    pub fn broadcast(&self) -> bool {
        profile! { self tick "sending" }
        let mut one_alive = false;
        log_verb! { "broadcasting..." }
        for &(ref sender, ref name, _) in self.learners.iter() {
            if let Some(sender) = sender.as_ref() {
                if sender
                    .send(FromTeacher::Data(Box::new(self.data.to_lrn_data())))
                    .is_err()
                {
                    warn!("learner `{}` is dead...", name)
                } else {
                    one_alive = true
                }
            }
        }
        log_verb! { "done broadcasting..." }
        profile! { self mark "sending" }
        one_alive
    }

    /// Sends data to a specific learner.
    pub fn send(&self, learner: LrnIdx) -> Res<bool> {
        profile! { self tick "sending" }
        let (ref sender, ref name, _) = self.learners[learner];
        let alive = if let Some(sender) = sender.as_ref() {
            sender
                .send(FromTeacher::Data(Box::new(self.data.to_lrn_data())))
                .is_ok()
        } else {
            false
        };
        if !alive {
            warn!("learner `{}` is dead...", name);
        }
        profile! { self mark "sending" }

        Ok(alive)
    }

    /// Receives a message with a timeout.
    fn receive_msg_tmo(&mut self, drain: bool, timeout: Duration) -> Res<Msg> {
        macro_rules! all_dead {
            () => {
                unknown!("all learners are dead")
            };
        }
        let msg = if !drain {
            match profile! {
              self wrap {
                self.from_learners.recv_timeout(timeout)
              } "waiting"
            } {
                Ok(msg) => msg,
                Err(_) => {
                    profile! { self mark "waiting" }
                    conf.check_timeout()?;
                    all_dead!()
                }
            }
        } else {
            match profile! {
              self wrap {
                self.from_learners.recv()
              } "waiting"
            } {
                Ok(msg) => msg,
                Err(_) => {
                    profile! { self mark "waiting" }
                    all_dead!()
                }
            }
        };
        Ok(msg)
    }

    /// Receive a message.
    fn receive_msg(&mut self, drain: bool) -> Res<(Id, MsgKind)> {
        macro_rules! all_dead {
            () => {
                unknown!("all learners are dead")
            };
        }

        if !drain
            && self
                .learners
                .iter()
                .all(|&(ref channel, _, _)| channel.is_none())
        {
            all_dead!()
        }

        profile! { self tick "waiting" }
        let Msg { id, msg } = if let Some(timeout) = conf.until_timeout() {
            self.receive_msg_tmo(drain, timeout)?
        } else {
            match profile! {
              self wrap {
                self.from_learners.recv()
              } "waiting"
            } {
                Ok(msg) => msg,
                Err(_) => {
                    profile! { self mark "waiting" }
                    all_dead!()
                }
            }
        };

        Ok((id, msg))
    }

    /// Handles some candidates.
    ///
    /// - checks for counterexamples
    /// - turns the cexs into learning data
    /// - runs the assistant
    /// - propagates the learning data
    pub fn handle_candidates(
        &mut self,
        candidates: Candidates,
        idx: LrnIdx,
    ) -> Res<Option<TeachRes>> {
        if_log! { @1
          log! { conf.teacher.step, || @1
            "\nCurrent candidate(s) from {} learner:",
            conf.emph( & self.learners[idx].1 )
          }
          for _pred in self.instance.preds() {
            if let Some(term) = candidates[_pred.idx].as_ref() {
              log!( @1
                "{}:", conf.emph(& _pred.name) ;
                "  {}", term
              )
            }
          }
          log! { @1 "" }
        }

        if conf.teacher.step {
            pause(
                "to look for counterexamples... (--step on)",
                &self._profiler,
            );
        }

        let cexs = profile! {
          self wrap { self.get_cexs(& candidates) } "cexs"
        }?;

        if cexs.is_empty() {
            return Ok(Some(TeachRes::Model(self.model_of_candidates(candidates))));
        }

        profile! { self tick "data" }
        profile! { self tick "data", "registration" }
        let res = self.instance.cexs_to_data(&mut self.data, cexs);
        profile! { self mark "data", "registration" }
        profile! { self mark "data" }

        self.run_assistant()?;

        match res {
            Ok(true) => {
                // New data.
                for (index, &mut (_, _, ref mut changed)) in self.learners.index_iter_mut() {
                    *changed = *changed || index != idx
                }
            }
            Ok(false) => {
                if self.learners.len() == 1 {
                    bail! {
                      "translation of cexs to data for {} generated no new data",
                      conf.emph( & self.learners[idx].1 )
                    }
                }
            }
            Err(e) => {
                if e.is_unsat() {
                    return Ok(Some(TeachRes::Unsat(self.unsat_core()?)));
                } else {
                    bail!(e)
                }
            }
        }

        profile! { self tick "data" }
        profile! { self tick "data", "propagation" }
        self.data.propagate()?;
        profile! { self mark "data", "propagation" }
        profile! { self mark "data" }

        Ok(None)
    }

    /// Waits for some candidates.
    ///
    /// Returns `None` when there are no more kids. Otherwise, the second
    /// element of the pair is `None` if a learner concluded `unsat`, and
    /// `Some` of the candidates otherwise.
    ///
    /// If true, `drain` forces to ignore timeouts. Useful when finalizing.
    pub fn get_candidates(&mut self, drain: bool) -> Res<Either<(LrnIdx, Candidates), UnsatRes>> {
        loop {
            let (id, msg) = self.receive_msg(drain)?;

            match msg {
                MsgKind::Cands(cands) => {
                    profile! { self "candidates" => add 1 }
                    if let Id::Learner(idx) = id {
                        return Ok(Either::Left((idx, self.complete_candidates(cands))));
                    } else {
                        bail!("received candidates from {}", id)
                    }
                }

                MsgKind::Samples(samples) => {
                    let (_pos, _neg) = samples.pos_neg_count();
                    profile! { self "assistant pos       " => add _pos }
                    profile! { self "assistant neg       " => add _neg }
                    let (pos, neg) = self.data.merge_samples(*samples)?;
                    profile! { self "assistant pos useful" => add pos }
                    profile! { self "assistant neg useful" => add neg }

                    if pos + neg != 0 {
                        for &mut (_, _, ref mut changed) in &mut self.learners {
                            *changed = true
                        }
                    }
                }

                MsgKind::Msg(_s) => {
                    let id = match id {
                        Id::Learner(idx) => conf.emph(&self.learners[idx].1),
                        Id::Assistant => conf.emph("assistant"),
                    };
                    println!(";");
                    for _line in _s.lines() {
                        println!("; {} | {}", id, _line)
                    }
                }

                MsgKind::Err(ref e) if e.is_unknown() => {
                    if_not_bench! {
                      let id = match id {
                        Id::Learner(idx) => conf.emph( & self.learners[idx].1 ),
                        Id::Assistant => conf.emph( "assistant" ),
                      } ;
                      log! { @verb "received `{}` from {}", conf.bad("unknown"), id }
                    }

                    // Are we unsat?
                    if self
                        .data
                        .check_unsat()
                        .chain_err(|| "while checking unsat result in teacher")?
                    {
                        return Ok(Either::Right(self.unsat_core()?));
                    }
                }

                MsgKind::Err(e) => {
                    conf.check_timeout()?;
                    let id = match id {
                        Id::Learner(idx) => conf.emph(&self.learners[idx].1),
                        Id::Assistant => conf.emph("assistant"),
                    };
                    let err: Res<()> = Err(e);
                    let err: Res<()> = err.chain_err(|| format!("from {} learner", id));
                    print_err(&err.unwrap_err())
                }

                MsgKind::Stats(profiler) => {
                    let id = match id {
                        Id::Learner(idx) => {
                            self.learners[idx].0 = None;
                            self.learners[idx].1.clone()
                        }
                        Id::Assistant => "assistant".into(),
                    };
                    if conf.stats {
                        self._profiler.add_other(id, profiler)
                    }
                }

                MsgKind::Unsat => return Ok(Either::Right(self.unsat_core()?)),
            }
        }
    }

    /// Retrieves the unsat core, if any.
    pub fn unsat_core(&mut self) -> Res<UnsatRes> {
        self.data
            .get_unsat_proof()
            .chain_err(|| "while getting unsat proof in teacher")
    }

    /// Initial check, where all candidates are `true`.
    ///
    /// Drops the copy of the `Sender` end of the channel used to communicate
    /// with the teacher (`self.to_teacher`). This entails that attempting to
    /// receive messages will automatically fail if all learners are dead.
    pub fn initial_check(&mut self) -> Res<(Cexs, Candidates)> {
        // Drop `to_teacher` sender so that we know when all kids are dead.
        self.to_teacher = None;

        let mut cands = PrdMap::with_capacity(self.instance.preds().len());
        for pred in self.instance.pred_indices() {
            if self.instance[pred].is_defined() {
                cands.push(None)

            // } else if let Some(dnf) = partial_candidate.get(& pred) {
            //   let mut cand_dnf = vec![] ;
            //   for conj in dnf {
            //     let mut cand_conj = vec![] ;
            //     for tterms in conj {
            //       if let Some(term) = tterms.to_term() {
            //         term.subst()
            //         cand_conj.push(term)
            //       } else {
            //         cand_conj.clear() ;
            //         cand_dnf.clear() ;
            //         cands.push( Some(term::tru()) ) ;
            //         continue 'all_preds
            //       }
            //     }
            //     cand_dnf.push( term::and(cand_conj) )
            //   }
            //   cands.push( Some( term::or(cand_dnf) ) )
            } else {
                cands.push(Some(term::tru()))
            }
        }

        let cands = self.complete_candidates(cands);

        if_verb! {
          log_verb! { "  initial candidates:" }
          for (pred, cand) in cands.index_iter() {
            if let Some(cand) = cand.as_ref() {
              log_verb! {
                "    {}: {}", self.instance[pred], cand
              }
            }
          }
        }

        self.get_cexs(&cands).map(|res| (res, cands))
    }

    /// Defines the predicates given some candidates.
    ///
    /// Only defines predicates that are neither trivially true or false.
    pub fn define_preds(&mut self, cands: &Candidates) -> Res<()> {
        for (pred, cand) in cands.index_iter() {
            if let Some(ref term) = *cand {
                match term.bool() {
                    None => {
                        let pred = &self.instance[pred];
                        let sig: Vec<_> = pred
                            .sig
                            .index_iter()
                            .map(|(var, typ)| (var, typ.get()))
                            .collect();
                        self.solver.define_fun(
                            &pred.name,
                            &sig,
                            typ::bool().get(),
                            &SmtTerm::new(&term),
                        )?
                    }
                    Some(_) => (),
                }
            }
        }
        Ok(())
    }

    /// Registers predicates that are trivially true/false in a candidate.
    ///
    /// Returns the clauses that are trivially true given the candidate.
    ///
    /// Clears and then populates `self.clauses_to_ignore`, `self.tru_preds` and
    /// `self.fls_preds`.
    pub fn register_trivial(&mut self, cands: &Candidates) {
        self.tru_preds.clear();
        self.fls_preds.clear();
        self.clauses_to_ignore.clear();

        for (pred, cand) in cands.index_iter() {
            if let Some(ref term) = *cand {
                match term.bool() {
                    Some(true) => {
                        let _ = self.tru_preds.insert(pred);
                        self.clauses_to_ignore
                            .extend(self.instance.clauses_of(pred).1)
                    }
                    Some(false) => {
                        let _ = self.fls_preds.insert(pred);
                        self.clauses_to_ignore
                            .extend(self.instance.clauses_of(pred).0)
                    }
                    None => (),
                }
            }
        }
    }

    /// Looks for falsifiable clauses given some candidates.
    pub fn get_cexs(&mut self, cands: &Candidates) -> Res<Cexs> {
        self.count += 1;

        self.register_trivial(cands);

        let mut map = ClsHMap::with_capacity(self.instance.clauses().len());

        if !self.restart_on_cex {
            self.solver.push(1)?;
            self.define_preds(cands)?
        }

        let instance = self.instance.clone();

        let mut got_unknown = false;

        macro_rules! handle_clause_res {
            ($e:expr) => {
                match $e {
                    Ok(()) => Ok(()),
                    Err(e) => {
                        if e.is_unknown() {
                            smt::reset(&mut self.solver, &self.instance)?;
                            self.solver.push(1)?;
                            self.define_preds(cands)?;
                            got_unknown = true;
                            Ok(())
                        } else {
                            Err(e)
                        }
                    }
                }
            };
        }

        // True if we got some positive or negative samples.
        // let mut got_pos_neg_samples = false ;

        log! { @verb |
            "looking for counterexamples in positive clauses ({})...",
            instance.pos_clauses().len()
        }
        for clause in instance.pos_clauses() {
            handle_clause_res!(self.get_cexs_of_clause(cands, *clause, &mut map, false))?
        }

        log! { @verb |
            "looking for counterexamples in strict negative clauses ({})...",
            instance.strict_neg_clauses().len()
        }
        for clause in instance.strict_neg_clauses() {
            handle_clause_res!(self.get_cexs_of_clause(cands, *clause, &mut map, false))?
        }

        // got_pos_neg_samples = ! map.is_empty() ;

        if map.is_empty() || !conf.teacher.max_bias {
            log! { @verb |
                "looking for counterexamples in non-strict negative clauses ({})...",
                instance.non_strict_neg_clauses().len()
            }
            for clause in instance.non_strict_neg_clauses() {
                handle_clause_res!(self.get_cexs_of_clause(
                    cands,
                    *clause,
                    &mut map,
                    conf.teacher.bias_cexs
                ))?
            }
        }

        if map.is_empty() || !conf.teacher.max_bias {
            log! { @verb |
                "looking for counterexamples in implication clauses ({})...",
                instance.imp_clauses().len()
            }

            for clause in instance.imp_clauses() {
                handle_clause_res!(self.get_cexs_of_clause(
                    cands,
                    *clause,
                    &mut map,
                    conf.teacher.bias_cexs
                ))?
            }
        }

        if map.is_empty() && got_unknown {
            bail!(ErrorKind::SmtError(::rsmt2::errors::ErrorKind::Unknown))
        }

        for (_, cexs) in map.iter_mut() {
            cexs.dedup()
        }

        log! { @debug
            "extracted {} cexs", map.iter().fold(0, |acc, (_, cexs)| acc + cexs.len())
        }

        // if got_pos_neg_samples && conf.teacher.max_bias {
        //   map.retain(
        //     |_, cexs| {
        //       cexs.retain( |(_, bias)| ! bias.is_none() ) ;
        //       ! cexs.is_empty()
        //     }
        //   )
        // }

        if self.count % 100 == 0 || self.restart_on_cex {
            smt::reset(&mut self.solver, &self.instance)?;
        } else {
            self.solver.pop(1)?
        }

        Ok(map)
    }

    /// Retrieves counterexamples for a clause.
    pub fn get_cexs_of_clause(
        &mut self,
        cands: &Candidates,
        clause: ClsIdx,
        map: &mut ClsHMap<Vec<BCex>>,
        bias: bool,
    ) -> Res<()> {
        if !self.clauses_to_ignore.contains(&clause) {
            if self.restart_on_cex {
                self.define_preds(cands)?
            } else {
                self.solver.push(1)?
            }

            let cexs = self.get_cex(clause, bias, conf.teacher.max_bias, !map.is_empty())?;

            if self.restart_on_cex {
                smt::reset(&mut self.solver, &self.instance)?
            } else {
                self.solver.pop(1)?
            }

            if !cexs.is_empty() {
                let prev = map.insert(clause, cexs);
                debug_assert_eq!(prev, None)
            }
        }

        Ok(())
    }

    /// Retrieves a counterexample given some bias.
    fn get_bias_cex(&mut self, clause: ClsIdx, bias: &Bias) -> Res<Cex> {
        profile! {
          self wrap { self.get_bias_cex_inner(clause, bias) } "cexs", "model"
        }
    }
    fn get_bias_cex_inner(&mut self, clause: ClsIdx, bias: &Bias) -> Res<Cex> {
        let model = self.solver.get_model()?;
        let model = Parser.fix_model(model)?;
        Cex::of_model(
            self.instance[clause].vars(),
            model,
            !bias.is_none() && conf.teacher.partial,
        )
    }

    /// Check-sats given an optional bias.
    fn check_sat_cex(
        &mut self,
        clause: ClsIdx,
        bias: Option<(Actlit, Bias)>,
        just_try: bool,
    ) -> Res<Option<(Cex, Bias)>> {
        if let Some((actlit, bias)) = bias {
            log! { @debug |
                "  checksat with bias {}", bias.to_string(& self.instance)
            }
            self.solver.comment(&format!(
                "checksat with bias {}",
                bias.to_string(&self.instance)
            ))?;
            profile! { self tick "cexs", "biased check-sat" }
            let sat = { self.solver.check_sat_act(Some(&actlit))? };

            if sat {
                log! { @debug | "  sat, getting cex" }
                profile! { self mark "cexs", "biased check-sat" }
                let cex = self.get_bias_cex(clause, &bias)?;
                log! { @debug | "  {}", cex }
                self.solver.de_actlit(actlit)?;
                Ok(Some((cex, bias)))
            } else {
                Ok(None)
            }
        } else {
            log! { @debug | "  checksat" }
            let sat = profile! {
                self wrap {

                    if self.using_rec_funs {
                        let solver = & mut self.solver;
                        let tru_preds = & self.tru_preds;
                        let fls_preds = & self.fls_preds;
                        let instance = & self.instance;
                        smt::tmo_multi_try_check_sat_legacy(
                            solver,
                            conf.until_timeout().map(
                                |time| time / 20
                            ).unwrap_or_else( || Duration::new(5,0) ),
                            |solver| {
                                let clause = smt::NegQClause::new(& instance[clause]);
                                solver.assert_with(
                                    & clause,
                                    (
                                        tru_preds,
                                        fls_preds,
                                        instance.preds(),
                                    )
                                )?;
                                Ok(())
                            },
                            ! just_try
                        )
                        // if res.as_ref().err().map(
                        //     |e| e.is_unknown()
                        // ).unwrap_or(false) {
                        //     smt::multi_try_check_sat(solver)
                        // } else {
                        //     res
                        // }
                    } else {
                        self.solver.check_sat().map_err(
                            |e| e.into()
                        )
                    }

                } "cexs", "check-sat"
            }?;

            if sat {
                log! { @debug | "  sat, getting cex" }
                let bias = if self.instance[clause].is_positive() {
                    Bias::Lft
                } else if self.instance[clause].is_strict_neg() {
                    let (pred, args) = self.instance[clause]
                        .lhs_preds()
                        .iter()
                        .next()
                        .map(|(pred, argss)| (*pred, argss.iter().next().unwrap().clone()))
                        .unwrap();
                    Bias::NuRgt(pred, args)
                } else {
                    Bias::Non
                };
                let cex = self.get_bias_cex(clause, &bias)?;
                log! { @debug "  {}", cex }
                Ok(Some((cex, bias)))
            } else {
                log! { @debug | "  unsat" }
                Ok(None)
            }
        }
    }

    /// Checks if a clause is falsifiable and returns a model if it is.
    pub fn get_cex(
        &mut self,
        clause_idx: ClsIdx,
        bias: bool,
        bias_only: bool,
        just_try: bool,
    ) -> Res<Vec<BCex>> {
        let mut cexs = vec![];

        log! { @debug | "working on clause #{}", clause_idx }

        // Macro to avoid borrowing `self.instance`.
        macro_rules! clause {
            () => {
                &self.instance[clause_idx]
            };
        }

        if conf.solver.log {
            self.solver.comment_args(format_args!(
                "\n\nClause # {}: {}",
                clause_idx,
                clause!().to_string_info(self.instance.preds()).unwrap()
            ))?
        }

        profile! { self tick "cexs", "prep" }
        clause!().declare(&mut self.solver)?;

        if self.using_rec_funs {
            log! { @4 | "assert/check-sat lhs terms" }
            for term in clause!().lhs_terms() {
                log! { @5 | "{}", term }
                self.solver.assert(&smt::SmtTerm::new(term))?;
            }
            let res = smt::multi_try_check_sat(&mut self.solver);
            if let Ok(false) = res {
                return Ok(vec![]);
            }

            log! { @4 | "assert/check-sat lhs preds" }
            for (pred, argss) in clause!().lhs_preds() {
                if self.tru_preds.contains(pred) {
                    continue;
                }

                for args in argss {
                    log! { @5 | "({} {})", self.instance[*pred], args }
                    self.solver.assert_with(
                        &smt::SmtPredApp::new(*pred, args),
                        (self.instance.preds(), true),
                    )?;

                    let res = smt::multi_try_check_sat(&mut self.solver);
                    if let Ok(false) = res {
                        return Ok(vec![]);
                    }
                }
            }

            if let Some((pred, args)) = clause!().rhs() {
                if !self.fls_preds.contains(&pred) {
                    log! { @4 | "assert/check-sat rhs pred" }
                    log! { @5 | "(not ({} {}))", self.instance[pred], args }
                    self.solver.assert_with(
                        &smt::SmtPredApp::new(pred, args),
                        (self.instance.preds(), false),
                    )?
                }
            }
        } else {
            self.solver.assert_with(
                clause!(),
                &(
                    false,
                    &self.tru_preds,
                    &self.fls_preds,
                    self.instance.preds(),
                ),
            )?
        }

        profile! { self mark "cexs", "prep" }

        macro_rules! get_cex {
            () => {
                // Normal check, no actlit.
                if let Some(cex) = self.check_sat_cex(clause_idx, None, just_try)? {
                    cexs.push(cex)
                }
            };

            ($actlit:expr ; $bias:expr) => {
                if let Some(cex) =
                    self.check_sat_cex(clause_idx, Some(($actlit, $bias)), just_try)?
                {
                    cexs.push(cex)
                }
            };
        }

        get_cex!();

        if bias {
            let unbiased_cex = cexs.pop();

            // Don't try bias examples if instance is unsat.
            if unbiased_cex.is_some() && !self.using_rec_funs {
                log! { @3 | "generating bias actlits" }
                let biased = profile! {
                  self wrap {
                    self.bias.apply(
                      & self._profiler, & mut self.solver,
                      clause_idx, & self.instance, & self.data,
                      bias_only
                    )
                  } "cexs", "bias generation"
                }?;
                log! { @3 | "working on {} biased checks", biased.len() }
                for (actlit, bias) in biased {
                    get_cex! { actlit ; bias }
                }
            }

            // Add the unbiased cex back if bias checks yielded nothing.
            if !conf.teacher.max_bias || cexs.is_empty() {
                if let Some(unbiased_cex) = unbiased_cex {
                    cexs.push(unbiased_cex)
                }
            }
        }

        Ok(cexs)
    }
}

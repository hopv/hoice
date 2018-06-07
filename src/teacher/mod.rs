//! Checks candidates and sends data to learner(s).
//! 
//! # TODO
//!
//! - clean [`teach`][teach] function, it's a mess and the way it's currently
//!   written doesn't make sense
//!
//! [teach]: fn.teach.html
//! (Teacher's teach function)

use common::{
  *,
  msg::*,
  smt::{ SmtTerm, FullParser as Parser },
} ;
use unsat_core::UnsatRes ;
use data::Data ;

pub mod assistant ;
use self::assistant::Assistant ;

/// Starts the teaching process.
///
/// The partial model stores conjunction of top terms for some of the top
/// terms, and is expressed in terms of the predicates' original signatures.
pub fn start_class(
  instance: & Arc<Instance>,
  partial_model: & ConjCandidates,
  profiler: & Profiler
) -> Res< Either<Candidates, UnsatRes> > {
  let instance = instance.clone() ;
  log! { @debug
    "starting the learning process" ;
    "  launching solver kid..."
  }
  let mut teacher = Teacher::new(instance.clone(), profiler, partial_model) ? ;

  let res = match teach(& mut teacher) {
    Ok(res) => Ok(res),
    Err(e) => {
      match e.kind() {
        & ErrorKind::Unsat => {
          warn! {
            "legacy unsat (by error) result triggered\n\
            unsat core will not be available\n\
            please consider contacting the developer"
          }
          let core = teacher.unsat_core() ;
          Ok( Either::Right(core) )
        },
        _ => Err(e)
      }
    },
  } ;

  teacher.finalize() ? ;
  res
}


/// Teaching to the learners.
pub fn teach(teacher: & mut Teacher) -> Res<
  Either<Candidates, UnsatRes>
> {

  log_debug!{ "spawning ice learner..." }
  if conf.ice.pure_synth {
    teacher.add_learner( ::learning::ice::Launcher, false ) ? ;
  }
  teacher.add_learner( ::learning::ice::Launcher, true ) ? ;

  log_debug!{ "performing initial check..." }
  let (cexs, cands) = teacher.initial_check() ? ;
  if cexs.is_empty() {
    log_debug!{ "solved by initial candidate..." }
    return Ok( Either::Left(cands) )
  }
  log_debug!{ "generating data from initial cex..." }
  let nu_stuff = teacher.instance.cexs_to_data(& mut teacher.data, cexs ) ? ;
  if ! nu_stuff {
    bail! { "translation of initial cexs to data generated no new data" }
  }
  teacher.run_assistant() ? ;

  // Index of the learner the teacher is currently working for.
  //
  // None at the beginning (broadcast).
  let mut learner: Option<LrnIdx> = None ;

  'teach: loop {

    log_verb! {
      "all learning data:\n{}", teacher.data.string_do(
        & (), |s| s.to_string()
      ) ?
    }

    if let Some(idx) = learner {
      if conf.teacher.step {
        pause(
          & format!(
            "to send data to {}... (--step on)",
            & conf.emph(& teacher.learners[idx].1)
          ), & teacher._profiler
        ) ;
      }
      let _ = teacher.send(idx) ? ;
      ()
    } else {
      if conf.teacher.step {
        pause(
          "to broadcast data... (--step on)",
          & teacher._profiler
        ) ;
      }
      let one_alive = teacher.broadcast() ;
      if ! one_alive {
        unknown!("all learners are dead")
      }
    }

    match teacher.get_candidates(false) ? {

      // Unsat result, done.
      Either::Right(unsat) => {
        return Ok(Either::Right(unsat))
      },

      // Got a candidate.
      Either::Left( ( idx, candidates) ) => {
        learner = Some(idx) ;
        if_verb!{
          log! { conf.teacher.step, || @info
            "\nCurrent candidates from {} learner:",
            conf.emph( & teacher.learners[idx].1 )
          }
          for _pred in teacher.instance.preds() {
            if let Some(term) = candidates[_pred.idx].as_ref() {
              log!( @info
                "{}:", conf.emph(& _pred.name) ;
                "  {}", term
              )
            }
          }
          log_verb! { "" }
        }

        if conf.teacher.step {
          pause(
            & format!(
              "to look for counterexamples... (--step on)",
            ), & teacher._profiler
          ) ;
        }

        profile!{ teacher tick "cexs" }
        let cexs = teacher.get_cexs(& candidates) ? ;
        profile!{ teacher mark "cexs" }

        if cexs.is_empty() {
          return Ok( Either::Left(candidates) )
        }

        profile!{ teacher tick "data" }
        profile!{ teacher tick "data", "registration" }
        let res = teacher.instance.cexs_to_data(
          & mut teacher.data, cexs
        ) ;
        profile!{ teacher mark "data", "registration" }
        profile!{ teacher mark "data" }

        teacher.run_assistant() ? ;
        match res {
          Ok(true) => {
            // New data.
            for (
              index, & mut (_, _, ref mut changed)
            ) in teacher.learners.index_iter_mut() {
              * changed = index != idx
            }
          },
          Ok(false) => if teacher.learners[idx].2 {
            // Something has changed since the last candidate of this learner.
            // The fact that the current candidate generated no new data is not
            // a problem.
            ()
          } else {
            bail! {
              "translation of cexs to data for {} generated no new data",
              conf.emph( & teacher.learners[idx].1 )
            }
          },
          Err(e) => {
            if e.is_unsat() {
              return Ok( Either::Right(teacher.unsat_core()) )
            } else {
              bail!(e)
            }
          },
        }

        profile!{ teacher tick "data" }
        profile!{ teacher tick "data", "propagation" }
        teacher.data.propagate() ? ;
        profile!{ teacher mark "data", "propagation" }
        profile!{ teacher mark "data" }
      },
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
  pub to_teacher: Option< Sender<Msg> >,

  /// Learners sender and description.
  ///
  /// Stores the channel to the learner, its name (for log), and a flag
  /// indicating whether the data has changed since this learner's last
  /// candidates.
  pub learners: LrnMap<( Option< Sender<FromTeacher> >, String, bool )>,
  /// Assistant for implication constraint breaking.
  ///
  /// The boolean flag indicates whether the assistant was sent some stuff.
  // pub assistant: Option< (Sender<FromTeacher>, bool) >,
  pub assistant: Option<Assistant>,
  /// Profiler.
  pub _profiler: & 'a Profiler,
  /// Partial candidate, only really contains stuff when in split mode.
  ///
  /// Used to further constrain the learner's candidates using previous
  /// results, when in split mode.
  partial_model: PrdHMap<Term>,
  /// Map from 
  /// Number of guesses.
  count: usize,
}

impl<'a> Teacher<'a> {
  /// Constructor.
  pub fn new(
    instance: Arc<Instance>, profiler: & 'a Profiler,
    partial_model: & 'a ConjCandidates
  ) -> Res<Self> {
    let solver = conf.solver.spawn(
      "teacher", Parser, & instance
    ) ? ;

    // let partial_model = PrdHMap::new() ;
    let partial_model = partial_model.iter().filter_map(
      |(pred, tterms_vec)| {
        let subst = instance.map_from_original_sig_of(* pred) ;
        let conj: Vec<_> = tterms_vec.iter().filter_map(
          |tterms| if let Some(term) = tterms.to_term() {
            term.subst_total(& subst).map(
              |(term, _)| term
            )
          } else {
            None
          }
        ).collect() ;

        if conj.is_empty() {
          None
        } else {
          profile! {
            |profiler| "partial model reuse" => add 1
          }
          Some( (* pred, term::and(conj)) )
        }
      }
    ).collect() ;

    let learners = LrnMap::with_capacity( 2 ) ;
    let (to_teacher, from_learners) = Msg::channel() ;
    let data = Data::new( instance.clone() ) ;

    let assistant = if conf.teacher.assistant {
      Some(
        Assistant::new(instance.clone()).chain_err(
          || format!("while spawning assistant")
        ) ?
      )
    } else {
      None
    } ;

    Ok(
      Teacher {
        solver, instance, data, from_learners,
        to_teacher: Some(to_teacher), learners, assistant,
        _profiler: profiler, partial_model, count: 0,
      }
    )
  }

  /// Runs the assistant (if any) on the current data.
  pub fn run_assistant(& mut self) -> Res<()> {
    if let Some(assistant) = self.assistant.as_mut() {
      profile! { self tick "assistant" }
      if let Some(mut data) = self.data.clone_new_constraints() ? {
        assistant.break_implications(& mut data) ? ;
        let (_nu_pos, _nu_neg) = self.data.merge_samples(data) ? ;
        profile! { self "assistant pos useful" => add _nu_pos }
        profile! { self "assistant neg useful" => add _nu_neg }
      }
      profile! { self mark "assistant" }
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
    self.solver.kill().chain_err(
      || "While killing solver"
    ) ? ;
    for & mut (ref mut sender, _, _) in self.learners.iter_mut() {
      if let Some(sender) = sender.as_ref() {
        let _ = sender.send( FromTeacher::Exit ) ;
        ()
      }
      * sender = None
    }

    if let Some(assistant) = self.assistant {
      let profiler = assistant.finalize() ? ;
      self._profiler.add_sub("assistant", profiler)
    }
    self.assistant = None ;
    log_debug! { "draining messages" }
    while let Ok(_) = self.get_candidates(true) {}

    if conf.stats {
      self._profiler.add_sub(
        "data", self.data.destroy()
      )
    }
    Ok(())
  }

  /// Adds a new learner.
  pub fn add_learner<L>(& mut self, learner: L, mine: bool) -> Res<()>
  where L: Learner + 'static {
    if let Some(to_teacher) = self.to_teacher.clone() {
      let index = self.learners.next_index() ;
      let name = learner.description(mine) ;
      let instance = self.instance.clone() ;
      let data = self.data.clone() ;
      let (to_learner, learner_recv) = FromTeacher::channel() ;
      ::std::thread::Builder::new().name( name.clone() ).spawn(
        move || learner.run(
          MsgCore::new_learner(
            index, to_teacher.clone(), learner_recv
          ),
          instance, data, mine
        )
      ).chain_err(
        || format!("while spawning learner `{}`", conf.emph(& name))
      ) ? ;
      self.learners.push( ( Some(to_learner), name, false ) ) ;
      Ok(())
    } else {
      bail!("trying to add learner after teacher's finalization")
    }
  }

  /// Broadcasts data to the learners. Returns `true` if there's no more
  /// learner left.
  ///
  /// Only used for the data from the first check.
  pub fn broadcast(& self) -> bool {
    profile!{ self tick "sending" }
    let mut one_alive = false ;
    log_verb! { "broadcasting..." }
    for & (ref sender, ref name, _) in self.learners.iter() {
      if let Some(sender) = sender.as_ref() {
        if let Err(_) = sender.send(
          FromTeacher::Data( self.data.clone() )
        ) {
          warn!( "learner `{}` is dead...", name )
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
  pub fn send(& self, learner: LrnIdx) -> Res<bool> {
    profile! { self tick "sending" }
    let (ref sender, ref name, _) = self.learners[learner] ;
    let alive = if let Some(sender) = sender.as_ref() {
      if let Err(_) = sender.send(
        FromTeacher::Data( self.data.clone() )
      ) {
        false
      } else {
        true
      }
    } else {
      false
    } ;
    if ! alive {
      warn!( "learner `{}` is dead...", name ) ;
    }
    profile! { self mark "sending" }
    Ok(alive)
  }

  /// Waits for some candidates.
  ///
  /// Returns `None` when there are no more kids. Otherwise, the second
  /// element of the pair is `None` if a learner concluded `unsat`, and
  /// `Some` of the candidates otherwise.
  ///
  /// If true, `drain` forces to ignore timeouts. Useful when finalizing.
  pub fn get_candidates(
    & mut self, drain: bool
  ) -> Res< Either<(LrnIdx, Candidates), UnsatRes> > {
    macro_rules! all_dead {
      () => ( unknown!("all learners are dead") ) ;
    }

    'recv: loop {

      if ! drain {
        if self.learners.iter().all(
          |& (ref channel, _, _)| {
            channel.is_none()
          }
        ) {
          all_dead!()
        }
      }

      profile!{ self tick "waiting" }
      let Msg { id, msg } = if let Some(timeout) = conf.until_timeout() {
        if ! drain {
          match profile! {
            self wrap {
              self.from_learners.recv_timeout(timeout)
            } "waiting"
          } {
            Ok(msg) => msg,
            Err(_) => {
              profile!{ self mark "waiting" }
              conf.check_timeout() ? ;
              all_dead!()
            },
          }
        } else {
          match profile! {
            self wrap {
              self.from_learners.recv()
            } "waiting"
          } {
            Ok(msg) => msg,
            Err(_) => {
              profile!{ self mark "waiting" }
              all_dead!()
            },
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
            profile!{ self mark "waiting" }
            all_dead!()
          },
        }
      } ;

      match msg {

        MsgKind::Cands(cands) => {
          profile!{ self "candidates" => add 1 }
          if let Id::Learner(idx) = id {
            return Ok( Either::Left( (idx, cands) ) )
          } else {
            bail!("received candidates from {}", id)
          }
        },

        MsgKind::Samples(samples) => {
          let (_pos, _neg) = samples.pos_neg_count() ;
          profile! { self "assistant pos       " => add _pos }
          profile! { self "assistant neg       " => add _neg }
          let (pos, neg) = self.data.merge_samples(samples) ? ;
          profile! { self "assistant pos useful" => add pos }
          profile! { self "assistant neg useful" => add neg }

          if pos + neg != 0 {
            for & mut (_, _, ref mut changed) in & mut self.learners {
              * changed = true
            }
          }
        },

        MsgKind::Msg(_s) => {
          let id = match id {
            Id::Learner(idx) => conf.emph( & self.learners[idx].1 ),
            Id::Assistant => conf.emph( "assistant" ),
          } ;
          println!(";") ;
          for _line in _s.lines() {
            println!("; {} | {}", id, _line)
          }
        },

        MsgKind::Err(ref e) if e.is_unknown() => {
          if_not_bench! {
            let id = match id {
              Id::Learner(idx) => conf.emph( & self.learners[idx].1 ),
              Id::Assistant => conf.emph( "assistant" ),
            } ;
            log! { @verb "received `{}` from {}", conf.bad("unknown"), id }
          }

          // Are we unsat?
          if self.data.is_unsat().is_some() {
            return Ok(Either::Right(self.unsat_core()))
          }
        },

        MsgKind::Err(e) => {
          let id = match id {
            Id::Learner(idx) => conf.emph( & self.learners[idx].1 ),
            Id::Assistant => conf.emph( "assistant" ),
          } ;
          let err: Res<()> = Err(e) ;
          let err: Res<()> = err.chain_err(
            || format!(
              "from {} learner", id
            )
          ) ;
          print_err( err.unwrap_err() )
        },

        MsgKind::Stats(profiler) => {
          let id = match id {
            Id::Learner(idx) => {
              self.learners[idx].0 = None ;
              self.learners[idx].1.clone()
            },
            Id::Assistant => "assistant".into(),
          } ;
          if conf.stats {
            self._profiler.add_other(id, profiler)
          }
        },

        MsgKind::Unsat => if self.data.is_unsat().is_some() {
          return Ok(Either::Right(self.unsat_core()))
        },

      }

    }
  }

  /// Retrieves the unsat core, if any.
  pub fn unsat_core(& mut self) -> UnsatRes {
    // UnsatRes::new( self.data.sample_graph() )
    UnsatRes::new( None )
  }

  /// Initial check, where all candidates are `true`.
  ///
  /// Drops the copy of the `Sender` end of the channel used to communicate
  /// with the teacher (`self.to_teacher`). This entails that attempting to
  /// receive messages will automatically fail if all learners are dead.
  pub fn initial_check(
    & mut self
  ) -> Res< (Cexs, Candidates) > {
    // Drop `to_teacher` sender so that we know when all kids are dead.
    self.to_teacher = None ;

    let mut cands = PrdMap::with_capacity( self.instance.preds().len() ) ;
    'all_preds: for pred in self.instance.pred_indices() {
      if self.instance.forced_terms_of(pred).is_some() {
        cands.push( None )

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
        cands.push( Some(term::tru()) )
      }
    }

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

    self.get_cexs(& cands).map(|res| (res, cands))
  }


  /// Looks for falsifiable clauses given some candidates.
  pub fn get_cexs(& mut self, cands: & Candidates) -> Res< Cexs > {
    use std::iter::Extend ;
    self.count += 1 ;

    // These will be passed to clause printing to inline trivial predicates.
    let (mut true_preds, mut false_preds) = ( PrdSet::new(), PrdSet::new() ) ;
    // Clauses to ignore, because they are trivially true. (lhs is false or
    // rhs is true).
    let mut clauses_to_ignore = ClsSet::new() ;

    let mut map = ClsHMap::with_capacity( self.instance.clauses().len() ) ;

    self.solver.push(1) ? ;

    // Retrieve true/false predicates and clauses to ignore. Define predicates.
    for (pred, cand) in cands.index_iter() {
      if let Some(ref term) = * cand {
        let term = if let Some(other) = self.partial_model.get(& pred) {
          term::and( vec![term.clone(), other.clone()] )
        } else {
          term.clone()
        } ;
        match term.bool() {
          Some(true) => {
            let _ = true_preds.insert(pred) ;
            clauses_to_ignore.extend(
              self.instance.clauses_of(pred).1
            )
          },
          Some(false) => {
            let _ = false_preds.insert(pred) ;
            clauses_to_ignore.extend(
              self.instance.clauses_of(pred).0
            )
          },
          None => {
            let term = if let Some(other) = self.partial_model.get(& pred) {
              term::and( vec![term.clone(), other.clone()] )
            } else {
              term.clone()
            } ;
            let pred = & self.instance[pred] ;
            let sig: Vec<_> = pred.sig.index_iter().map(
              |(var, typ)| (var, typ.get())
            ).collect() ;
            self.solver.define_fun(
              & pred.name, & sig, typ::bool().get(), & SmtTerm::new(& term)
            ) ?
          },
        }
      }
    }

    let instance = self.instance.clone() ;

    // True if we got some positive or negative samples.
    // let mut got_pos_neg_samples = false ;

    macro_rules! run {
      ($clause:expr, $bias:expr) => (
        if ! clauses_to_ignore.contains($clause) {
          self.solver.push(1) ? ;

          let cexs = self.get_cex(
            * $clause, & true_preds, & false_preds, $bias,
            // got_pos_neg_samples &&
            conf.teacher.max_bias
          ).chain_err(
            || format!("while getting counterexample for clause {}", $clause)
          ) ? ;

          self.solver.pop(1) ? ;

          if ! cexs.is_empty() {
            // got_pos_neg_samples = got_pos_neg_samples || (
            //   cexs.iter().any(
            //     |(_, bias)| ! bias.is_none()
            //   )
            // ) ;
            let prev = map.insert(* $clause, cexs) ;
            debug_assert_eq!(prev, None)
          }
        }
      ) ;
    }

    log! { @verb
      "looking for counterexamples in positive clauses ({})...",
      instance.pos_clauses().len()
    }
    for clause in instance.pos_clauses() {
      run!(clause, false)
    }

    log! { @verb
      "looking for counterexamples in strict negative clauses ({})...",
      instance.strict_neg_clauses().len()
    }
    for clause in instance.strict_neg_clauses() {
      run!(clause, false)
    }

    // got_pos_neg_samples = ! map.is_empty() ;

    if map.is_empty() || ! conf.teacher.max_bias {
      log! { @verb
        "looking for counterexamples in non-strict negative clauses ({})...",
        instance.non_strict_neg_clauses().len()
      }
      for clause in instance.non_strict_neg_clauses() {
        run!(clause, true)
      }
    }

    if map.is_empty() || ! conf.teacher.max_bias {
      log_verb! { "looking for counterexamples in implication clauses..." }

      for clause in instance.imp_clauses() {
        run!(clause, true)
      }
    }

    log! { @debug
      "extracted {} cexs", map.iter().fold(
        0, |acc, (_, cexs)| acc + cexs.len()
      )
    }

    // if got_pos_neg_samples && conf.teacher.max_bias {
    //   map.retain(
    //     |_, cexs| {
    //       cexs.retain( |(_, bias)| ! bias.is_none() ) ;
    //       ! cexs.is_empty()
    //     }
    //   )
    // }

    if self.count % 100 == 0 {
      self.solver.reset() ?
    } else {
      self.solver.pop(1) ?
    }

    Ok(map)
  }

  /// Checks if a clause is falsifiable and returns a model if it is.
  pub fn get_cex(
    & mut self,
    clause_idx: ClsIdx, true_preds: & PrdSet, false_preds: & PrdSet,
    bias: bool, bias_only: bool
  ) -> Res< Vec<BCex> > {
    log! { @debug "working on clause #{}", clause_idx }

    // Macro to avoid borrowing `self.instance`.
    macro_rules! clause {
      () => (& self.instance[clause_idx])
    }

    if conf.solver.log {
      self.solver.comment_args(
        format_args!(
          "\n\nClause # {}: {}",
          clause_idx,
          clause!().to_string_info(& self.instance.preds()).unwrap()
        )
      ) ?
    }

    profile!{ self tick "cexs", "prep" }
    clause!().declare(& mut self.solver) ? ;
    self.solver.assert_with(
      clause!(), & (false, true_preds, false_preds, self.instance.preds())
    ) ? ;
    profile!{ self mark "cexs", "prep" }

    let mut cexs = vec![] ;

    macro_rules! get_cex {

      (@$sat:ident $bias:expr) => ({ // Works on the check-sat result.
        conf.check_timeout() ? ;
        if $sat {
          log! { @3 "sat, getting cex" }
          profile!{ self tick "cexs", "model" }
          let model = self.solver.get_model() ? ;
          let model = Parser.fix_model(model) ? ;
          // for (var, _, val) in & model {
          //   println!("v_{} -> {}", var,)
          // }
          let cex = Cex::of_model(
            clause!().vars(), model, ! $bias.is_none() && conf.teacher.partial
          ) ? ;
          profile!{ self mark "cexs", "model" }

          if ! $bias.is_none() {
            profile! { self "  biased checksat" => add 1 }
          } else {
            profile! { self "unbiased checksat" => add 1 }
          }

          cexs.push((cex, $bias))
        }
      }) ;

      () => ({ // Normal check, no actlit.
        log! { @debug "  checksat" }
        profile!{ self tick "cexs", "check-sat" }
        let sat = self.solver.check_sat() ? ;
        profile!{ self mark "cexs", "check-sat" }
        get_cex!(
          @sat if clause!().is_positive() {
            Bias::Lft
          } else if clause!().is_strict_neg() {
            let (pred, args) = clause!().lhs_preds().iter().next().map(
              |(pred, argss)| (
                * pred, argss.iter().next().unwrap().clone()
              )
            ).unwrap() ;
            Bias::NuRgt(pred, args)
          } else {
            Bias::Non
          }
        ) ;
      }) ;

      ($actlit:expr ; $bias:expr) => ({
        log! { @debug
          "  checksat with bias {}", $bias.to_string(& self.instance)
        }
        self.solver.comment(
          & format!("checksat with bias {}", $bias.to_string(& self.instance))
        ) ? ;
        profile!{ self tick "cexs", "biased check-sat" }
        let sat = self.solver.check_sat_act(
          Some(& $actlit)
        ) ? ;
        profile!{ self mark "cexs", "biased check-sat" }
        get_cex!(@sat $bias) ;
        self.solver.de_actlit($actlit) ?
      }) ;
    }

    get_cex!() ;

    if bias {
      let unbiased_cex = cexs.pop() ;

      // Don't try bias examples if instance is unsat.
      if unbiased_cex.is_some() {
        log! { @3 "generating bias actlits" }
        let biased = profile! { 
          self wrap {
            self.nu_bias_applications(clause_idx, bias_only)
            // self.bias_applications(clause_idx)
          } "cexs", "bias generation"
        } ? ;
        log! { @3 "working on {} biased checks", biased.len() }
        for (actlit, bias) in biased {
          get_cex! { actlit ; bias }
        }
      }

      // Add the unbiased cex back if bias checks yielded nothing.
      if ! conf.teacher.max_bias || cexs.is_empty() {
        if let Some(unbiased_cex) = unbiased_cex {
          cexs.push(unbiased_cex)
        }
      }
    }

    Ok(cexs)
  }



  pub fn nu_bias_applications(
    & mut self, clause_idx: ClsIdx, bias_only: bool,
  ) -> Res<Vec<(Actlit, Bias)>> {
    use common::smt::DisjArgs ;
    use var_to::terms::{ VarTermsMap, VarTermsSet } ;

    let clause = & self.instance[clause_idx] ;

    // Maps lhs applications to activation literals for positive samples.
    let mut lhs_actlits_of = PrdHMap::with_capacity(
      clause.lhs_preds().len()
    ) ;
    // Predicates in lhs applications that don't have positive samples, or for
    // which positive samples cannot be activated.
    let mut lhs_preds_with_no_pos = PrdHMap::<VarTermsSet>::new() ;

    log! { @4 "creating lhs actlits" }

    let mut cant_pos_argss = VarTermsSet::new() ;

    // Create actlits for lhs applications when possible.
    for (pred, argss) in clause.lhs_preds() {
      let pred = * pred ;
      log! { @5 "for {} ({})", self.instance[pred], argss.len() }

      if self.data.pos[pred].is_empty() {
        log! { @5 "  no positive data" }
        lhs_preds_with_no_pos.insert(pred, argss.clone()) ;
        continue
      }

      self.solver.comment(
        & format!(
          "activating positive samples for {} ({} applications)",
          self.instance[pred], argss.len()
        )
      ) ? ;

      let mut argss_map = VarTermsMap::with_capacity( argss.len() ) ;

      debug_assert! { cant_pos_argss.is_empty() }

      for args in argss {
        log! { @6 "generating actlit for {}", args }
        let actlit = self.solver.get_actlit() ? ;
        let disjunction = DisjArgs::new(
          args, & self.data.pos[pred]
        ) ? ;
        self.solver.assert_act(& actlit, & disjunction) ? ;

        if self.solver.check_sat_act( Some(& actlit) ) ? {
          log! { @6 "  sat, keeping" }
          let prev = argss_map.insert(args.clone(), actlit) ;
          debug_assert! { prev.is_none() }
        } else {
          log! { @6 "  unsat, discarding" }
          self.solver.de_actlit(actlit) ? ;
          let is_new = cant_pos_argss.insert( args.clone() ) ;
          debug_assert! { is_new }
        }
      }

      if ! cant_pos_argss.is_empty() {
        let prev = lhs_preds_with_no_pos.insert(
          pred, cant_pos_argss.drain().into()
        ) ;
        debug_assert! { prev.is_none() }
      }

      if ! argss_map.is_empty() {
        let prev = lhs_actlits_of.insert(pred, argss_map) ;
        debug_assert! { prev.is_none() }
      }
    }

    log! { @4 "working on rhs" }

    // Create actlit for rhs application if any.
    //
    // - `Some(None)` if there's not rhs
    // - `None` if there's one but it has no negative data
    // - `Some(actlit)` otherwise.
    //
    // So `rhs_actlit.is_none()` => we can't force the rhs to be false.
    let rhs_actlit = if let Some((pred, args)) = clause.rhs() {
      log! { @5 "-> {}", self.instance[pred] }
      if self.data.neg[pred].is_empty() {
        // No negative data...
        log! { @5 "   no negative data" }
        None
      } else {
        log! { @5 "   has negative data" }
        // Negative data, generate an actlit for that.
        self.solver.comment(
          & format!(
            "activating negative samples for {}", self.instance[pred]
          )
        ) ? ;
        let actlit = self.solver.get_actlit() ? ;
        let disjunction = DisjArgs::new(
          args, & self.data.neg[pred]
        ) ? ;
        self.solver.assert_act(& actlit, & disjunction) ? ;

        if self.solver.check_sat_act( Some(& actlit) ) ? {
          log! { @6 "sat, keeping" }
          Some( Some(actlit) )
        } else {
          log! { @6 "unsat, discarding" }
          self.solver.de_actlit(actlit) ? ;
          None
        }
      }
    } else {
      log! { @5 "-> None" }
      Some(None)
    } ;


    // Let's do this.
    let mut actlits = vec![] ;


    // If there's any positive samples at all, we can do something for the rhs
    // (if any).
    if ! lhs_actlits_of.is_empty() && clause.rhs().is_some() && (
      // Skip if we're only generating biased check-sat and there are
      // applications without any positive data.
      ! bias_only || lhs_preds_with_no_pos.is_empty()
    ) {
      self.solver.comment("activating all lhs positive samples") ? ;
      let actlit = self.solver.get_actlit() ? ;
      for (_, map) in & lhs_actlits_of {
        for (_, pos_actlit) in map {
          self.solver.assert_act(& actlit, pos_actlit) ?
        }
      }

      let bias = if lhs_preds_with_no_pos.is_empty() {
        log! { @4 "total bias left" }
        profile! { self "bias: total left" => add 1 }
        // If all lhs predicates have positive sample then this actlit yields a
        // positive example for the rhs.
        Bias::Lft
      } else {
        log! { @4 "partial bias left" }
        profile! { self "bias: partial left" => add 1 }
        // Otherwise this will generate a constraint.
        Bias::Non
      } ;

      if ! bias.is_none() || ! bias_only {
        actlits.push( (actlit, bias) )
      }
    }


    // If there's no rhs or it has negative samples we can do something for the
    // lhs.
    if let Some(maybe_actlit) = rhs_actlit {

      if lhs_preds_with_no_pos.is_empty() {
        log! { @4 "exhaustive bias right" }
        // We can force all positive examples for all lhs applications but
        // one in turn to try to generate negative examples.
        for (this_pred, map) in & lhs_actlits_of {
          for (this_args, _) in map {

            self.solver.comment(
              & format!(
                "actlit forcing application ({} {}) to be false",
                self.instance[* this_pred], this_args
              )
            ) ? ;
            let this_actlit = self.solver.get_actlit() ? ;

            // Force rhs false if any.
            if let Some(rhs_actlit) = maybe_actlit.as_ref() {
              self.solver.assert_act(& this_actlit, rhs_actlit) ?
            }

            // Activate everything else than this particular application
            for (pred, map) in & lhs_actlits_of {
              for (args, actlit) in map {
                if pred == this_pred && args == this_args {
                  continue
                }
                self.solver.assert_act(& this_actlit, actlit) ?
              }
            }

            profile! { self "bias: exhaustive right" => add 1 }

            actlits.push(
              (this_actlit, Bias::NuRgt(* this_pred, this_args.clone()))
            )
          }
        }

      } else if ! bias_only || lhs_preds_with_no_pos.iter().fold(
        // Skip if only generating biased checksat and there's more than one
        // application without positive data.
        0, |acc, (_, argss)| acc + argss.len()
      ) == 1 {

        // There's some lhs applications with no negative data. Activate
        // everything we can.

        let this_actlit = self.solver.get_actlit() ? ;

        // Force rhs false if any.
        if let Some(rhs_actlit) = maybe_actlit.as_ref() {
          self.solver.assert_act(& this_actlit, rhs_actlit) ?
        }

        // Activate everything we can.
        for (_, map) in & lhs_actlits_of {
          for (_, actlit) in map {
            self.solver.assert_act(& this_actlit, actlit) ?
          }
        }

        // Now the question is what kind of bias this corresponds to.

        let mut iter = lhs_preds_with_no_pos.into_iter() ;
        let (this_pred, argss) = iter.next().expect(
          "next on non-empty iterator cannot yield none"
        ) ;

        let mut argss_iter = argss.into_iter() ;
        let this_args = argss_iter.next().expect(
          "empty arguments for predicate are illegal in clauses"
        ) ;

        // If we have a single predicate application with no negative samples
        // we can generate an actlit for this one.
        let bias = if iter.next().is_none() && argss_iter.next().is_none() {
          log! { @4 "singular bias right" }
          profile! { self "bias: singular right" => add 1 }
          Bias::NuRgt(this_pred, this_args.clone())
        } else {
          // Otherwise we can just generate a negative constraint that's more
          // constrained.
          log! { @4 "partial bias right" }
          profile! { self "bias: partial right " => add 1 }
          Bias::Non
        } ;

        actlits.push( (this_actlit, bias) )

      }

    }


    Ok(actlits)
  }



  /// Biases the arguments of the predicates of a clause.
  ///
  /// **Assumes all active variables are already defined.**
  ///
  /// Guaranteed to return `(None, None)` if this feature is deactivated by
  /// [`bias_cexs`][conf], or if the clause is positive / negative (either LHS
  /// or RHS have no predicate applications).
  ///
  /// The first element of the pair it returns is an activation literal that
  /// forces predicate applications in the LHS to be positive. That is, it
  /// forces their arguments to correspond to one of the known positive
  /// examples.
  ///
  /// - When no predicate appearing in the LHS have positive examples, returns
  ///   no actlit.
  /// - When only some of them do, returns an actlit: some LHS applications
  ///   will not be constrained.
  ///
  /// The second element of the pair it returns is an activation literal that
  /// forces the predicate application in the RHS to be negative. That is, it
  /// forces its arguments to correspond to one of the known negative examples.
  ///
  /// - When the predicate appearing in the RHS has no negative examples,
  ///   returns no actlit.
  ///
  /// [conf]: ../common/config/struct.TeacherConf.html#structfield.bias_cexs
  /// (bias_cexs configuration)
  pub fn bias_applications(
    & mut self, clause_idx: ClsIdx
  ) -> Res<Vec<(Actlit, Bias)>> {
    use common::smt::DisjArgs ;

    let clause = & self.instance[clause_idx] ;

    // Active and not a positive constraint?
    if ! conf.teacher.bias_cexs
    || clause.lhs_preds().is_empty() {
      return Ok( vec![] )
    }

    let rhs_actlit = if let Some((rhs_pred, rhs_args)) = clause.rhs() {
      if ! self.data.neg[rhs_pred].is_empty() {
        self.solver.comment(
          & format!("actlit for rhs bias ({})", self.instance[rhs_pred])
        ) ? ;
        let actlit = self.solver.get_actlit() ? ;

        let disjunction = DisjArgs::new(
          rhs_args, & self.data.neg[rhs_pred]
        ) ? ;
        self.solver.assert_act(& actlit, & disjunction) ? ;

        Some(actlit)
      } else {
        None
      }
    } else if clause.lhs_pred_apps_len() == 1 {
      // Negative constraint, skipping.
      return Ok( vec![] )
    } else {
      None
    } ;

    // Work on lhs pred apps that have some positive data.
    let mut lhs_actlit = None ;
    for (pred, argss) in clause.lhs_preds() {
      let pred = * pred ;
      if self.data.pos[pred].is_empty() { continue }
      let actlit = if let Some(actlit) = lhs_actlit {
        actlit
      } else {
        self.solver.comment(
          & format!("\nactlit for lhs bias")
        ) ? ;
        self.solver.get_actlit() ?
      } ;

      self.solver.comment(
        & format!("\nbias for {}", self.instance[pred])
      ) ? ;

      for args in argss {
        let disjunction = DisjArgs::new(args, & self.data.pos[pred]) ? ;
        self.solver.assert_act(& actlit, & disjunction) ?
      }

      lhs_actlit = Some(actlit)
    }

    let mut res = vec![] ;

    if let Some(actlit) = rhs_actlit {
      res.push((actlit, Bias::Non))
    }

    if let Some(actlit) = lhs_actlit {
      res.push((actlit, Bias::Non))
    }

    Ok(res)
  }
}
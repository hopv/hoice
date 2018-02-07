//! The teacher. Queries an SMT-solver to check candidates.
//! 
//! # TODO
//!
//! - clean [`teach`][teach] function, it's a mess and the way it's currently
//!   written doesn't make sense
//!
//! [teach]: fn.teach.html
//! (Teacher's teach function)

use common::* ;
use common::data::* ;
use common::msg::* ;

use self::smt::Parser ;

pub mod assistant ;


/// Starts the teaching process.
pub fn start_class(
  instance: & Arc<Instance>, profiler: & Profiler
) -> Res< Option<Candidates> > {
  use rsmt2::{ solver, Kid } ;
  let instance = instance.clone() ;
  log_debug!{ "starting the learning process\n  launching solver kid..." }
  let mut kid = Kid::new( conf.solver.conf() ).chain_err(
    || ErrorKind::Z3SpawnError
  ) ? ;
  let res = {
    let solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("teacher") ? {
      let mut teacher = Teacher::new(
        solver.tee(log), instance, profiler
      ) ? ;
      let res = teach( & mut teacher ) ;
      teacher.finalize() ? ;
      res
    } else {
      let mut teacher = Teacher::new(
        solver, instance, profiler
      ) ? ;
      let res = teach( & mut teacher ) ;
      teacher.finalize() ? ;
      res
    }
  } ;

  kid.kill().chain_err(
    || "while killing solver kid"
  ) ? ;
  res
}


/// Teaching to the learners.
pub fn teach< 'kid, S: Solver<'kid, Parser> >(
  teacher: & mut Teacher<'kid, S>
) -> Res< Option<Candidates> > {
  log_debug!{ "  creating teacher" }

  // if conf.smt_learn {
  //   log_debug!{ "  spawning smt learner..." }
  //   teacher.add_learner( ::learning::smt::Launcher ) ?
  // }
  log_debug!{ "  spawning ice learner..." }
  if conf.ice.pure_synth {
    teacher.add_learner( ::learning::ice::Launcher, false ) ? ;
  }
  teacher.add_learner( ::learning::ice::Launcher, true ) ? ;

  log_debug!{ "  performing initial check..." }
  let (cexs, cands) = teacher.initial_check() ? ;
  if cexs.is_empty() {
    return Ok( Some(cands) )
  }
  log_debug!{ "  generating data from initial cex..." }
  let nu_stuff = teacher.instance.cexs_to_data(& mut teacher.data, cexs ) ? ;
  if ! nu_stuff {
    bail! { "translation of initial cexs to data generated no new data" }
  }

  // Index of the learner the teacher is currently working for.
  //
  // None at the beginning (broadcast).
  let mut learner: Option<LrnIdx> = None ;

  log_debug!{ "  starting teaching loop" }
  'teach: loop {

    log_debug!{
      "all learning data:\n{}", teacher.data.string_do(
        & (), |s| s.to_string()
      ) ?
    }

    if let Some(idx) = learner {
      if conf.teacher.step {
        read_line(
          & format!(
            "to send data to {} (--step on)...",
            & conf.emph(& teacher.learners[idx].1)
          )
        ) ;
      }
      let _ = teacher.send(idx) ? ;
      ()
    } else {
      if conf.teacher.step {
        read_line("to broadcast data (--step on)...") ;
      }
      let one_alive = teacher.broadcast() ;
      if ! one_alive {
        bail!("all learners are dead")
      }
    }

    match teacher.get_candidates(false) ? {

      // Unsat result, done.
      None => return Ok(None),

      // Got a candidate.
      Some( ( idx, candidates) ) => {
        learner = Some(idx) ;
        if_verb!{
          log_info!(
            "\nCurrent candidates from {} learner:",
            conf.emph( & teacher.learners[idx].1 )
          ) ;
          for _pred in teacher.instance.preds() {
            if let Some(term) = candidates[_pred.idx].as_ref() {
              log_info!("{}:", conf.emph(& _pred.name)) ;
              log_info!("  {}", term)
            }
          }
          log_info!( "" )
        }
        profile!{ teacher tick "cexs" }
        let cexs = teacher.get_cexs(& candidates) ? ;
        profile!{ teacher mark "cexs" }

        if cexs.is_empty() {
          return Ok( Some(candidates) )
        }

        profile!{ teacher tick "data" }
        profile!{ teacher tick "data", "registration" }
        let res = teacher.instance.cexs_to_data(
          & mut teacher.data, cexs
        ) ;
        profile!{ teacher mark "data", "registration" }
        profile!{ teacher mark "data" }
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
              "translation of cexs for {} to data generated no new data",
              conf.emph( & teacher.learners[idx].1 )
            }
          },
          Err(e) => {
            if e.is_unsat() {
              return Ok(None)
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
pub struct Teacher<'a, S> {
  /// The solver.
  pub solver: S,

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
  pub assistant: Option< ( Sender<FromTeacher>, Data ) >,

  /// Profiler.
  pub _profiler: & 'a Profiler,
  /// Number of guesses.
  count: usize,
}

impl<'a, 'kid, S: Solver<'kid, Parser>> Teacher<'a, S> {
  /// Constructor.
  pub fn new(
    solver: S, instance: Arc<Instance>, profiler: & 'a Profiler
  ) -> Res<Self> {
    let learners = LrnMap::with_capacity( 2 ) ;
    let (to_teacher, from_learners) = Msg::channel() ;
    let data = Data::new( instance.clone() ) ;

    let assistant = if conf.teacher.assistant {
      let (to_assistant_send, to_assistant_recv) = FromTeacher::channel() ;
      let instance = instance.clone() ;
      let to_teacher = to_teacher.clone() ;

      ::std::thread::Builder::new().name( "assistant".into() ).spawn(
        move || assistant::launch(
          instance, MsgCore::new_assistant(
            to_teacher, to_assistant_recv
          )
        )
      ).chain_err(
        || format!("while spawning assistant")
      ) ? ;

      Some(( to_assistant_send, data.clone() ))
    } else {
      None
    } ;

    Ok(
      Teacher {
        solver, instance, data, from_learners,
        to_teacher: Some(to_teacher), learners, assistant,
        _profiler: profiler, count: 0,
      }
    )
  }

  /// Finalizes the run.
  #[cfg( not(feature = "bench") )]
  pub fn finalize(mut self) -> Res<()> {
    for & mut (ref mut sender, _, _) in self.learners.iter_mut() {
      if let Some(sender) = sender.as_ref() {
        let _ = sender.send( FromTeacher::Exit ) ;
        ()
      }
      * sender = None
    }
    if let Some(& (ref sender, _)) = self.assistant.as_ref() {
      let _ = sender.send( FromTeacher::Exit ) ;
      ()
    }
    self.assistant = None ;
    log_debug! { "draining messages" }
    while let Ok(_) = self.get_candidates(true) {}
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
    log_info!{ "broadcasting..." }
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
    log_info!{ "done broadcasting..." }
    profile!{ self mark "sending" }
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
    & self, drain: bool
  ) -> Res< Option<(LrnIdx, Candidates)> > {
    macro_rules! all_dead {
      () => ( bail!("all learners are dead") ) ;
    }

    profile!{ self tick "waiting" }

    'recv: loop {

      let Msg { id, msg } = if let Some(timeout) = conf.until_timeout() {
        if ! drain {
          match self.from_learners.recv_timeout(timeout) {
            Ok(msg) => msg,
            Err(_) => {
              profile!{ self mark "waiting" }
              conf.check_timeout() ? ;
              all_dead!()
            },
          }
        } else {
          match self.from_learners.recv() {
            Ok(msg) => msg,
            Err(_) => {
              profile!{ self mark "waiting" }
              all_dead!()
            },
          }
        }
      } else {
        match self.from_learners.recv() {
          Ok(msg) => msg,
          Err(_) => {
            profile!{ self mark "waiting" }
            all_dead!()
          },
        }
      } ;

      match msg {

        MsgKind::Cands(cands) => {
          profile!{ self mark "waiting" }
          profile!{ self "candidates" => add 1 }
          if let Id::Learner(idx) = id {
            return Ok( Some( (idx, cands) ) )
          } else {
            bail!("received candidates from {}", id)
          }
        },

        MsgKind::Samples(_samples) => unimplemented!(),

        MsgKind::Msg(_s) => if_verb!{
          let id = match id {
            Id::Learner(idx) => conf.emph( & self.learners[idx].1 ),
            Id::Assistant => conf.emph( "assistant" ),
          } ;
          println!(";") ;
          for _line in _s.lines() {
            println!("; {} | {}", id, _line)
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

        MsgKind::Stats(tree, stats) => if conf.stats {
          let id = match id {
            Id::Learner(idx) => self.learners[idx].1.clone(),
            Id::Assistant => "assistant".into(),
          } ;
          log_debug! { "received stats from {}", conf.emph(& id) }
          self._profiler.add_sub(
            id, tree, stats
          )
        },

        MsgKind::Unsat => return Ok(None),

      }

    }
  }

  /// Initial check, where all candidates are `true`.
  ///
  /// Drops the copy of the `Sender` end of the channel used to communicate
  /// with the teacher (`self.to_teacher`). This entails that attempting to
  /// receive messages will automatically fail if all learners are dead.
  pub fn initial_check(& mut self) -> Res< (Cexs, Candidates) > {
    // Drop `to_teacher` sender so that we know when all kids are dead.
    self.to_teacher = None ;

    let mut cands = PrdMap::with_capacity( self.instance.preds().len() ) ;
    for pred in self.instance.pred_indices() {
      if self.instance.forced_terms_of(pred).is_some() {
        cands.push( None )
      } else {
        cands.push( Some(term::tru()) )
      }
    }
    self.get_cexs(& cands).map(|res| (res, cands))
  }

  /// Looks for falsifiable clauses given some candidates.
  pub fn get_cexs(& mut self, cands: & Candidates) -> Res< Cexs > {
    use std::iter::Extend ;
    self.count += 1 ;
    self.solver.reset() ? ;

    // These will be passed to clause printing to inline trivial predicates.
    let (mut true_preds, mut false_preds) = ( PrdSet::new(), PrdSet::new() ) ;
    // Clauses to ignore, because they are trivially true. (lhs is false or
    // rhs is true).
    let mut clauses_to_ignore = ClsSet::new() ;

    // Define non-forced predicates that are not trivially true or false.
    'define_non_forced: for (pred, cand) in cands.index_iter() {
      if let Some(ref term) = * cand {
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
            let pred = & self.instance[pred] ;
            let sig: Vec<_> = pred.sig.index_iter().map(
              |(var, typ)| (var, * typ)
            ).collect() ;
            self.solver.define_fun(
              & pred.name, & sig, & Typ::Bool, & TermWrap(term)
            ) ?
          },
        }
      }
    }

    let mut map = ClsHMap::with_capacity( self.instance.clauses().len() ) ;
    let clauses = ClsRange::zero_to( self.instance.clauses().len() ) ;
    self.solver.comment("looking for counterexamples...") ? ;
    for clause in clauses {
      if ! clauses_to_ignore.contains(& clause) {
        // log_debug!{ "  looking for a cex for clause {}", clause }
        if let Some(cex) = self.get_cex(
          clause, & true_preds, & false_preds
        ).chain_err(
          || format!("while getting counterexample for clause {}", clause)
        ) ? {
          let prev = map.insert(clause, cex) ;
          debug_assert_eq!(prev, None)
        }
      }
    }
    Ok(map)
  }

  /// Checks if a clause is falsifiable and returns a model if it is.
  pub fn get_cex(
    & mut self, clause_idx: ClsIdx, true_preds: & PrdSet, false_preds: & PrdSet
  ) -> SmtRes< Option<Cex> > {
    // log_debug!{
    //   "getting cex for {}",
    //   self.instance[clause_idx].to_string_info(
    //     self.instance.preds()
    //   ).unwrap()
    // }
    self.solver.push(1) ? ;
    let clause = & self.instance[clause_idx] ;
    if_not_bench!{
      if conf.solver.log {
        self.solver.comment(& format!("clause variables:\n")) ? ;
        for info in clause.vars() {
          self.solver.comment(
            & format!("  v_{} ({})\n", info.idx, info.active)
          ) ?
        }
        self.solver.comment(& format!("lhs terms:\n")) ? ;
        for lhs in clause.lhs_terms() {
          self.solver.comment(
            & format!("  {}\n", lhs)
          ) ?
        }
        self.solver.comment(& format!("lhs pred applications:\n")) ? ;
        for (pred, argss) in clause.lhs_preds() {
          for args in argss {
            let mut s = format!("  ({}", & self.instance[* pred]) ;
            for arg in args.iter() {
              s = format!("{} {}", s, arg)
            }
            s.push(')') ;
            self.solver.comment(& s) ?
          }
        }
        self.solver.comment(& format!("rhs:\n")) ? ;
        if let Some((pred, args)) = clause.rhs() {
          self.solver.comment(
            & format!("  {}", TTerm::P { pred, args: args.clone() })
          ) ?
        } else {
          self.solver.comment("  false") ?
        }
      }
    }

    profile!{ self tick "cexs", "prep" }
    clause.declare(& mut self.solver) ? ;
    self.solver.assert_with(
      clause, & (false, true_preds, false_preds, self.instance.preds())
    ) ? ;
    profile!{ self mark "cexs", "prep" }

    profile!{ self tick "cexs", "check-sat" }
    let sat = self.solver.check_sat() ? ;
    profile!{ self mark "cexs", "check-sat" }

    let res = if sat {
      profile!{ self tick "cexs", "model" }
      log_debug!{ "    sat, getting model..." }
      let model = self.solver.get_model_const() ? ;
      let mut map: VarMap<_> = clause.vars().iter().map(
        |info| info.typ.default_val() // Val::N
      ).collect() ;
      for (var, _, val) in model {
        log_debug!{ "    - {} = {}", var.default_str(), val }
        map[var] = val
      }
      log_debug!{ "    done constructing model" }
      profile!{ self mark "cexs", "model" }
      Ok( Some( map ) )
    } else {
      Ok(None)
    } ;
    self.solver.pop(1) ? ;
    res
  }
}



/// Wraps a term to write as the body of a `define-fun`.
pub struct TermWrap<'a>( & 'a Term ) ;
impl<'a> ::rsmt2::to_smt::Expr2Smt<()> for TermWrap<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.0.write( w, |w, var| var.default_write(w) ) ? ;
    Ok(())
  }
}



/// Teacher's smt stuff.
mod smt {
  use std::str::FromStr ;
  use std::io::BufRead ;

  use rsmt2::parse::{ IdentParser, ValueParser, SmtParser } ;

  use common::* ;

  /// Unit type parsing the output of the SMT solver.
  ///
  /// Parses variables of the form `v<int>` and constants. It is designed to
  /// parse models of the falsification of a single clause, where the
  /// variables of the clause are written as `v<index>` in smt2.
  #[derive(Clone, Copy)]
  pub struct Parser ;

  impl<'a> IdentParser<VarIdx, (), & 'a str> for Parser {
    fn parse_ident(self, input: & 'a str) -> SmtRes<VarIdx> {
      debug_assert_eq!( & input[0..2], "v_" ) ;
      match usize::from_str(& input[2..]) {
        Ok(idx) => Ok( idx.into() ),
        Err(e) => bail!(
          "could not retrieve var index from `{}`: {}", input, e
        ),
      }
    }
    fn parse_type(self, _: & 'a str) -> SmtRes<()> {
      Ok(())
    }
  }

  impl<'a, Br> ValueParser<Val, & 'a mut SmtParser<Br>> for Parser
  where Br: BufRead {
    fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Val> {
      if let Some(val) = input.try_int::<
        _, _, ::num::bigint::ParseBigIntError
      >(
        |int, pos| {
          let int = Int::from_str(int) ? ;
          Ok( if ! pos { - int } else { int } )
        }
      ) ? {
        Ok( Val::I(val) )
      } else if let Some(val) = input.try_bool() ? {
        Ok( Val::B(val) )
      } else if let Some(val) = input.try_rat::<
        _, _, ::num::bigint::ParseBigIntError
      >(
        |num, den, pos| {
          let (num, den) = (
            Int::from_str(num) ?, Int::from_str(den) ?
          ) ;
          let rat = Rat::new(num, den) ;
          Ok( if ! pos { - rat } else { rat } )
        }
      ) ? {
        Ok( Val::R(val) )
      } else {
        input.fail_with("unexpected value")
      }
    }
  }
}
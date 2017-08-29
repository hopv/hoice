#![doc = r#"The teacher. Queries an SMT-solver to check candidates.

# TO DO

- clean `teach` function, it's a mess and the way it's currently written
  doesn't make sense

"#]

use rsmt2::{ ParseSmt2, Kid } ;

use nom::IResult ;

use common::* ;
use common::data::* ;
use common::msg::* ;
use instance::{ Instance, Val } ;




/// Starts the teaching process.
pub fn start_class(instance: Instance, profiler: Profile) -> Res<()> {
  use rsmt2::solver ;
  log_debug!{ "starting the learning process\n  launching solver kid..." }
  let mut kid = Kid::mk( conf.solver_conf() ).chain_err(
    || ErrorKind::Z3SpawnError
  ) ? ;
  let res = {
    let solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.smt_log_file("teacher") ? {
      teach( instance, solver.tee(log), profiler )
    } else {
      teach( instance, solver, profiler )
    }
  } ;

  let res_2 = kid.kill().chain_err(
    || "while killing solver kid"
  ) ;
  res.and_then(
    |()| res_2
  )
}


/// Teaching to the learners.
fn teach<
  'kid, S: Solver<'kid, Parser>
>(instance: Instance, solver: S, profiler: Profile) -> Res<()> {
  log_debug!{ "  creating teacher" }
  let mut teacher = Teacher::mk(solver, instance, profiler) ;

  // if conf.smt_learn {
  //   log_debug!{ "  spawning smt learner..." }
  //   teacher.add_learner( ::learning::smt::Launcher ) ?
  // }
  log_debug!{ "  spawning ice learner..." }
  teacher.add_learner( ::learning::ice::Launcher ) ? ;

  log_debug!{ "  performing initial check..." }
  let cexs = teacher.initial_check() ? ;
  log_debug!{ "  generating data from initial cex..." }
  teacher.instance.cexs_to_data(& mut teacher.data, cexs ) ? ;

  log_debug!{ "  starting teaching loop" }
  'teach: loop {
    log_info!{
      "all learning data:\n{}", teacher.data.string_do(
        & (), |s| s.to_string()
      ) ?
    }

    if conf.step {
      let mut dummy = String::new() ;
      println!("") ;
      println!( "; {} to broadcast data...", conf.emph("press return") ) ;
      let _ = ::std::io::stdin().read_line(& mut dummy) ;
    }

    let one_alive = teacher.broadcast() ;
    if ! one_alive {
      bail!("all learners are dead")
    }

    if let Some( (_idx, candidates) ) = teacher.get_candidates() ? {
      if_verb!{
        log_info!(
          "\nCurrent candidates from {} learner:",
          conf.emph( & teacher.learners[_idx].1 )
        ) ;
        for _pred in teacher.instance.preds() {
          log_info!("{}:", _pred.name) ;
          log_info!("  {}", candidates[_pred.idx])
        }
      }
      profile!{ teacher tick "cexs" }
      let cexs = teacher.get_cexs(& candidates) ? ;
      profile!{ teacher mark "cexs" }

      if cexs.is_empty() {
        println!("sat") ;
        println!("(model") ;
        for pred in teacher.instance.preds() {
          println!("  (define-fun {}", pred.name) ;
          print!(  "    (") ;
          for (var, typ) in pred.sig.index_iter() {
            print!(" ({} {})", teacher.instance.var(var), typ)
          }
          println!(" ) Bool") ;
          println!("    {}", candidates[pred.idx]) ;
          println!("  )")
        }
        println!(")") ;
        teacher.finalize()? ;
        return Ok(())
      }

      log_info!{
        "\nlearning data before adding cex:\n{}",
        teacher.data.string_do(
          & (), |s| s.to_string()
        ) ?
      }
      profile!{ teacher tick "data", "registration" }
      teacher.instance.cexs_to_data(& mut teacher.data, cexs) ? ;
      profile!{ teacher mark "data", "registration" }
      log_info!{
        "\nlearning data before propagation:\n{}",
        teacher.data.string_do(
          & (), |s| s.to_string()
        ) ?
      }
      profile!{ teacher tick "data", "propagation" }
      teacher.data.propagate() ? ;
      profile!{ teacher mark "data", "propagation" }
    } else {
      bail!("all learners are dead")
    }
  }
}




/// Alias type for a counterexample for a clause.
pub type Cex = VarMap<Val> ;
/// Alias type for a counterexample for a sequence of clauses.
pub type Cexs = ClsHMap<Cex> ;




/// The teacher, stores a solver.
pub struct Teacher<S> {
  /// The solver.
  pub solver: S,
  /// The (shared) instance.
  pub instance: Arc<Instance>,
  /// Learning data.
  pub data: Data,
  /// Receiver.
  pub from_learners: Receiver<(LrnIdx, FromLearners)>,
  /// Sender used by learners. Becomes `None` when the learning process starts.
  pub to_teacher: Option< Sender<(LrnIdx, FromLearners)> >,
  /// Learners sender and description.
  pub learners: LrnMap<( Option< Sender<Data> >, String )>,
  /// Profiler.
  pub _profiler: Profile,
  /// Number of guesses.
  count: usize,
}
impl<'kid, S: Solver<'kid, Parser>> Teacher<S> {
  /// Constructor.
  pub fn mk(solver: S, instance: Instance, profiler: Profile) -> Self {
    let learners = LrnMap::with_capacity( 2 ) ;
    let (to_teacher, from_learners) = from_learners() ;
    let instance = Arc::new(instance) ;
    let data = Data::mk( instance.clone() ) ;
    Teacher {
      solver, instance, data, from_learners,
      to_teacher: Some(to_teacher), learners,
      _profiler: profiler, count: 0,
    }
  }

  /// Finalizes the run.
  #[cfg( not(feature = "bench") )]
  pub fn finalize(mut self) -> Res<()> {
    if conf.stats {
      println!("; Done in {} guesses", self.count) ;
      println!("") ;
    }

    for & mut (ref mut sender, _) in self.learners.iter_mut() {
      * sender = None
    }
    while self.get_candidates()?.is_some() {}

    if conf.stats {
      let (tree, stats) = self._profiler.extract_tree() ;
      tree.print() ;
      if ! stats.is_empty() {
        println!("; stats:") ;
        stats.print()
      }
      println!("") ;
    }

    Ok(())
  }
  #[cfg(feature = "bench")]
  pub fn finalize(self) -> Res<()> {
    Ok(())
  }

  /// Adds a new learner.
  pub fn add_learner<L: Learner + 'static>(& mut self, learner: L) -> Res<()> {
    if let Some(to_teacher) = self.to_teacher.clone() {
      let index = self.learners.next_index() ;
      let name = learner.description() ;
      let instance = self.instance.clone() ;
      let data = self.data.clone() ;
      let (to_learner, learner_recv) = new_to_learner() ;
      ::std::thread::Builder::new().name( name.clone() ).spawn(
        move || learner.run(
          LearnerCore::mk(index, to_teacher.clone(), learner_recv),
          instance, data
        )
      ).chain_err(
        || format!("while spawning learner `{}`", conf.emph(& name))
      ) ? ;
      self.learners.push( ( Some(to_learner), name ) ) ;
      Ok(())
    } else {
      bail!("trying to add learner after teacher's finalization")
    }
  }

  /// Broadcasts data to the learners. Returns `true` if there's no more
  /// learner left.
  pub fn broadcast(& self) -> bool {
    profile!{ self tick "broadcast" }
    let mut one_alive = false ;
    for & (ref sender, ref name) in self.learners.iter() {
      if let Some(sender) = sender.as_ref() {
        if let Err(_) = sender.send( self.data.clone() ) {
          warn!(
            "learner `{}` is dead...", name
          )
        } else {
          one_alive = true
        }
      }
    }
    profile!{ self mark "broadcast" }
    one_alive
  }

  /// Waits for some candidates.
  pub fn get_candidates(& self) -> Res< Option<(LrnIdx, Candidates)> > {
    profile!{ self tick "waiting" }
    'recv: loop {
      match self.from_learners.recv() {
        Ok( (_idx, FromLearners::Msg(_s)) ) => if_verb!{
          for _line in _s.lines() {
            log_info!("{} > {}", conf.emph( & self.learners[_idx].1 ), _line)
          }
        },
        Ok( (idx, FromLearners::Err(e)) ) => {
          let err: Res<()> = Err(e) ;
          let err: Res<()> = err.chain_err(
            || format!(
              "from {} learner", conf.emph( & self.learners[idx].1 )
            )
          ) ;
          // println!("receiving:") ;
          // for err in e.iter() {
          //   println!("{}", err)
          // }
          print_err( err.unwrap_err() )
        },
        Ok( (idx, FromLearners::Stats(tree, stats)) ) => if conf.stats {
          println!(
            "; received stats from {}", conf.emph( & self.learners[idx].1 )
          ) ;
          tree.print() ;
          if ! stats.is_empty() {
            println!("; stats:") ;
            stats.print()
          }
          println!("")
        },
        Ok( (idx, FromLearners::Cands(cands)) ) => {
          profile!{ self mark "waiting" }
          profile!{ self "candidates" => add 1 }
          return Ok( Some( (idx, cands) ) )
        },
        Ok( (_, FromLearners::Unsat) ) => {
          bail!( ErrorKind::Unsat )
        },
        Err(_) => {
          profile!{ self mark "waiting" }
          return Ok( None )
        },
      }
    }
  }

  /// Initial check, where all candidates are `true`.
  ///
  /// Drops the copy of the `Sender` end of the channel used to communicate
  /// with the teacher (`self.to_teacher`). This entails that attempting to
  /// receive messages will automatically fail if all learners are dead.
  pub fn initial_check(& mut self) -> Res< Cexs > {
    // Drop `to_teacher` sender so that we know when all kids are dead.
    self.to_teacher = None ;

    let mut cands = PrdMap::with_capacity( self.instance.preds().len() ) ;
    for _ in 0..self.instance.preds().len() {
      cands.push( self.instance.bool(true) )
    }
    self.get_cexs(& cands)
  }

  /// Looks for falsifiable clauses given some candidates.
  pub fn get_cexs(& mut self, cands: & Candidates) -> Res< Cexs > {
    self.count += 1 ;
    let mut map = ClsHMap::with_capacity( self.instance.clauses().len() ) ;
    let clauses = ClsRange::zero_to( self.instance.clauses().len() ) ;
    self.solver.comment("looking for counterexamples...") ? ;
    for clause in clauses {
      log_debug!{ "  looking for a cex for clause {}", clause }
      if let Some(cex) = self.get_cex(cands, clause).chain_err(
        || format!("while getting counterexample for clause {}", clause)
      ) ? {
        let prev = map.insert(clause, cex) ;
        debug_assert_eq!(prev, None)
      }
    }
    Ok(map)
  }

  /// Checks if a clause is falsifiable and returns a model if it is.
  pub fn get_cex(
    & mut self, cands: & Candidates, clause_idx: ClsIdx
  ) -> SmtRes< Option<Cex> > {
    self.solver.push(1) ? ;
    let clause = & self.instance[clause_idx] ;
    if_not_bench!{
      if conf.smt_log {
        for lhs in clause.lhs() {
          self.solver.comment(
            & format!("{}\n", lhs)
          ) ?
        }
        self.solver.comment(
          & format!("=> {}", clause.rhs())
        ) ?
      }
    }
    profile!{ self tick "cexs", "prep" }
    for var in clause.vars() {
      self.solver.declare_const(var, & var.typ, & ()) ?
    }
    self.solver.assert( clause, cands ) ? ;
    profile!{ self mark "cexs", "prep" }
    profile!{ self tick "cexs", "check-sat" }
    let sat = self.solver.check_sat() ? ;
    profile!{ self mark "cexs", "check-sat" }
    let res = if sat {
      profile!{ self tick "cexs", "model" }
      log_debug!{ "    sat, getting model..." }
      let model = self.solver.get_model() ? ;
      let mut map: VarMap<_> = clause.vars().iter().map(
        |info| info.typ.default_val()
      ).collect() ;
      for (var,val) in model {
        log_debug!{ "    - v_{} = {}", var, val }
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





#[doc = r#"Unit type parsing the output of the SMT solver.

Parses variables of the form `v<int>` and constants. It is designed to parse
models of the falsification of a single clause, where the variables of the
clause are written as `v<index>` in smt2.
"#]
pub struct Parser ;
impl ParseSmt2 for Parser {
  type Ident = VarIdx ;
  type Value = Val ;
  type Expr = () ;
  type Proof = () ;
  type I = () ;

  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], VarIdx> {
    use std::str::FromStr ;
    preceded!(
      bytes,
      char!('v'),
      map!(
        map_res!(
          map_res!(
            re_bytes_find!("^[0-9][0-9]*"),
            ::std::str::from_utf8
          ),
          usize::from_str
        ),
        |i| i.into()
      )
    )
  }

  fn parse_value<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], Val> {
    fix_error!( bytes, u32, call!(Val::parse) )
  }

  fn parse_expr<'a>(
    & self, _: & 'a [u8], _: & ()
  ) -> IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_expr` of the teacher parser should never be called")
  }

  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_proof` of the teacher parser should never be called")
  }
}



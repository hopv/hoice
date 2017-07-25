#![doc = r#"The teacher. Queries an SMT-solver to check candidates.

# TO DO

- clean `teach` function, it's a mess and the way it's currently written
  doesn't make sense

"#]

use rsmt2::{ ParseSmt2, SolverConf, Kid } ;

use nom::IResult ;

use common::* ;
use common::data::* ;
use common::msg::* ;
use instance::{ Instance, Val } ;



/// Logs at info level. Deactivated in release.
#[cfg( feature = "bench" )]
macro_rules! log_info {
  ($($tt:tt)*) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! log_info {
  ($($tt:tt)*) => ( info!{$($tt)*} ) ;
}


/// Logs at debug level. Deactivated in release.
#[cfg( feature = "bench" )]
macro_rules! log_debug {
  ($($tt:tt)*) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! log_debug {
  ($($tt:tt)*) => ( debug!{$($tt)*} ) ;
}



/// Starts the teaching process.
pub fn start_class(instance: Instance) -> Res<()> {
  use rsmt2::solver ;
  log_debug!{ "starting the learning process\n  launching solver kid..." }
  let mut kid = Kid::mk( SolverConf::z3() ).chain_err(
    || "while spawning the teacher's solver"
  ) ? ;
  let res = {
    let solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.smt_log_file("teacher") ? {
      teach( instance, solver.tee(log) )
    } else {
      teach( instance, solver )
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
>(instance: Instance, solver: S) -> Res<()> {
  let mut teacher = Teacher::mk(solver, instance) ;

  if conf.smt_learn {
    teacher.add_learner( ::learning::smt::Launcher ) ?
  }
  teacher.add_learner( ::learning::ice::Launcher ) ? ;

  let cexs = teacher.initial_check() ? ;
  let mut data = teacher.instance.cexs_to_data(& teacher.data, cexs) ? ;

  'teach: loop {
    log_info!{
      "\nnew learning data:\n{}", data.string_do(
        teacher.instance.preds(), |s| s.to_string()
      ) ?
    }
    log_info!{
      "all learning data:\n{}", teacher.data.string_do(
        teacher.instance.preds(), |s| s.to_string()
      ) ?
    }

    if conf.step {
      let mut dummy = String::new() ;
      println!("") ;
      println!( "; {} to broadcast data...", conf.emph("press return") ) ;
      let _ = ::std::io::stdin().read_line(& mut dummy) ;
    }

    let one_alive = teacher.broadcast(data) ;
    if ! one_alive {
      bail!("all learners are dead")
    }

    if let Some( (_idx, candidates) ) = teacher.get_candidates() {
      log_info!(
        "\nCurrent candidates from {} learner:",
        conf.emph( & teacher.learners[_idx].1 )
      ) ;
      for _pred in teacher.instance.preds() {
        log_info!("{}:", _pred.name) ;
        log_info!("  {}", candidates[_pred.idx])
      }
      let cexs = teacher.get_cexs(& candidates) ? ;
      data = teacher.instance.cexs_to_data(& teacher.data, cexs) ? ;
      // teacher.data.add_learning_data(& data) ? ;
      // info!{ "data:" }
      // teacher.data.string_do(
      //   teacher.instance.preds(), |s| info!{ "{}", s }
      // ) ?
      if data.is_empty() {
        println!("(safe") ;
        for pred in teacher.instance.preds() {
          println!("  (define-pred {}", pred.name) ;
          print!(  "    (") ;
          for (var, typ) in pred.sig.index_iter() {
            print!(" ({} {})", teacher.instance.var(var), typ)
          }
          println!(" )") ;
          println!("    {}", candidates[pred.idx]) ;
          println!("  )")
        }
        println!(")") ;
        return Ok(())
      }
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
  pub data: Arc<Data>,
  /// Receiver.
  pub from_learners: Receiver<(LrnIdx, FromLearners)>,
  /// Sender used by learners. Becomes `None` when the learning process starts.
  pub to_teacher: Option< Sender<(LrnIdx, FromLearners)> >,
  /// Learners sender and description.
  pub learners: LrnMap<(Sender<LearningData>, String)>,
}
impl<'kid, S: Solver<'kid, Parser>> Teacher<S> {
  /// Constructor.
  pub fn mk(solver: S, instance: Instance) -> Self {
    let learners = LrnMap::with_capacity( 2 ) ;
    let (to_teacher, from_learners) = from_learners() ;
    let data = Arc::new( Data::mk(& instance) ) ;
    Teacher {
      solver, instance: Arc::new(instance), data,
      from_learners, to_teacher: Some(to_teacher), learners
    }
  }

  /// Adds a new learner.
  pub fn add_learner<L: Learner + 'static>(& mut self, learner: L) -> Res<()> {
    if let Some(to_teacher) = self.to_teacher.clone() {
      let index = self.learners.next_index() ;
      let name = learner.description() ;
      let instance = self.instance.clone() ;
      let data = self.data.clone() ;
      let (to_learner, learner_recv) = to_learner() ;
      ::std::thread::Builder::new().name( name.clone() ).spawn(
        move || learner.run(
          LearnerCore::mk(index, to_teacher.clone(), learner_recv),
          instance, data
        )
      ).chain_err(
        || format!("while spawning learner `{}`", conf.emph(& name))
      ) ? ;
      self.learners.push( (to_learner, name) ) ;
      Ok(())
    } else {
      bail!("trying to add learner after teacher's finalization")
    }
  }

  /// Broadcasts data to the learners. Returns `true` if there's no more
  /// learner left.
  pub fn broadcast(& self, data: LearningData) -> bool {
    let mut one_alive = false ;
    for & (ref sender, ref name) in self.learners.iter() {
      if let Err(_) = sender.send( data.clone() ) {
        warn!(
          "learner `{}` is dead...", name
        )
      } else {
        one_alive = true
      }
    }
    one_alive
  }

  /// Waits for some candidates.
  pub fn get_candidates(& self) -> Option<(LrnIdx, Candidates)> {
    'recv: loop {
      match self.from_learners.recv() {
        Ok( (_idx, FromLearners::Msg(s)) ) => for _line in s.lines() {
          log_info!("{} > {}", conf.emph( & self.learners[_idx].1 ), _line)
        },
        Ok( (idx, FromLearners::Err(e)) ) => print_err(
          Error::with_chain::<Error, ErrorKind>(
            format!(
              "from {} learner", conf.emph( & self.learners[idx].1 )
            ).into(), e.into()
          )
        ),
        Ok( (idx, FromLearners::Cands(cands)) ) => return Some( (idx, cands) ),
        Err(_) => return None
      }
    }
  }

  /// Initial check, where all candidates are `true`.
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
    let mut map = ClsHMap::with_capacity( self.instance.clauses().len() ) ;
    let clauses = ClsRange::zero_to( self.instance.clauses().len() ) ;
    for clause in clauses {
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
      {
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
    for var in clause.vars() {
      self.solver.declare_const(var, & var.typ, & ()) ?
    }
    self.solver.assert( clause, cands ) ? ;
    let sat = self.solver.check_sat() ? ;
    let res = if sat {
      let model = self.solver.get_model() ? ;
      let mut map: VarMap<_> = clause.vars().iter().map(
        |info| info.typ.default_val()
      ).collect() ;
      for (var,val) in model {
        map[var] = val
      }
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



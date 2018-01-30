//! ICE learner.

use common::* ;
use common::data::* ;
use common::msg::* ;

use self::smt::* ;

pub mod quals ;
pub mod synth ;
pub mod data ;

use self::quals::Qualifiers ;
use self::data::CData ;


/// Launcher.
pub struct Launcher ;
unsafe impl Sync for Launcher {}
unsafe impl Send for Launcher {}

impl Launcher {
  /// Launches an smt learner.
  pub fn launch(
    core: & LearnerCore, instance: Arc<Instance>, data: DataCore,
    mine: bool
  ) -> Res<()> {
    use rsmt2::{ solver, Kid } ;
    let mut kid = Kid::new( conf.solver.conf() ).chain_err(
      || "while spawning the teacher's solver"
    ) ? ;
    let conflict_solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    // let mut synth_kid = Kid::new( conf.solver.conf() ).chain_err(
    //   || "while spawning the teacher's synthesis solver"
    // ) ? ;
    // let synth_solver = solver(& mut synth_kid, Parser).chain_err(
    //   || "while constructing the teacher's synthesis solver"
    // ) ? ;
    if let Some(log) = conf.solver.log_file("ice_learner") ? {
      // let synth_log = conf.solver.log_file("ice_learner_synth")?.expect(
      //   "[unreachable] log mod is active"
      // ) ;
      IceLearner::new(
        & core, instance, data,
        conflict_solver.tee(log), // synth_solver.tee(synth_log)
        mine
      ).chain_err(
        || "while creating ice learner"
      )?.run()
    } else {
      IceLearner::new(
        & core, instance, data, conflict_solver, // synth_solver
        mine
      ).chain_err(
        || "while creating ice learner"
      )?.run()
    }
  }
}
impl Learner for Launcher {
  fn run(
    & self, core: LearnerCore,
    instance: Arc<Instance>, data: DataCore,
    mine: bool
  ) {
    if let Err(e) = Self::launch(& core, instance, data, mine) {
      let _ = core.err(e) ;
    }
  }
  fn description(& self, mine: bool) -> String {
    format!("ice{}", if mine { "" } else { " pure synth" })
  }
}


/// A branch of a decision tree.
///
/// Boolean is `false` if the term should be negated.
pub type Branch = Vec<(Term, bool)> ;



/// Ice learner.
pub struct IceLearner<'core, Slver> {
  /// Arc to the instance.
  pub instance: Arc<Instance>,
  /// Qualifiers for the predicates.
  pub qualifiers: Qualifiers,
  /// Current data.
  data: DataCore,
  /// Solver used to check if the constraints are respected.
  solver: Slver,
  /// Learner core.
  core: & 'core LearnerCore,
  /// Branches of the tree, used when constructing a decision tree.
  finished: Vec<Branch>,
  /// Branches to construct later, used when constructing a decision tree.
  unfinished: Vec< (Branch, CData) >,
  /// Classifier for constraint data.
  classifier: HashMap<HSample, bool>,
  /// Declaration memory: used when declaring samples in the solver to
  /// remember what's already declared. The `u64` is the sample's uid.
  dec_mem: PrdMap< HashSet<u64> >,
  /// Current candidate, cleared at the beginning of each learning phase.
  candidate: PrdMap< Option<Term> >,
  /// Profiler.
  _profiler: Profiler,
  /// Vector used during learning, avoids re-allocation.
  predicates: Vec<(usize, usize, PrdIdx)>,
  /// Rng to decide when to sort predicates.
  rng: ::rand::StdRng,
  /// Luby counter for restarts.
  luby: Option<LubyCount>,
}
impl<'core, 'kid, Slver> IceLearner<'core, Slver>
where Slver: Solver<'kid, Parser> {
  /// Ice learner constructor.
  pub fn new(
    core: & 'core LearnerCore, instance: Arc<Instance>, data: DataCore,
    solver: Slver, mine: bool// synth_solver: Slver
  ) -> Res<Self> {
    let _profiler = Profiler::new() ;
    profile!{ |_profiler| tick "mining" }
    let qualifiers = Qualifiers::new( instance.clone(), mine ).chain_err(
      || "while creating qualifier structure"
    ) ? ;

    profile!{ |_profiler| mark "mining" }
    // if_verb!{
    //   log_info!{ "qualifiers:" } ;
    //   for quals in qualifiers.qualifiers() {
    //     for (qual, _) in quals {
    //       log_info!("- {}", qual)
    //     }
    //   }
    // }
    let dec_mem = vec![
      HashSet::with_capacity(103) ; instance.preds().len()
    ].into() ;
    let candidate = vec![ None ; instance.preds().len() ].into() ;
    let predicates = Vec::with_capacity( instance.preds().len() ) ;

    Ok(
      IceLearner {
        instance, qualifiers, data, solver, // synth_solver,
        core,
        finished: Vec::with_capacity(103),
        unfinished: Vec::with_capacity(103),
        classifier: HashMap::with_capacity(1003),
        dec_mem, candidate,
        _profiler,
        predicates,
        rng: {
          use rand::SeedableRng ;
          ::rand::StdRng::from_seed(& [ 42 ])
        },
        luby: if mine { None } else {
          Some( LubyCount::new() )
        }
      }
    )
  }

  /// Returns true if all qualifiers should be wiped out.
  pub fn restart(& mut self) -> bool {
    self.luby.as_mut().map( |l| l.inc() ).unwrap_or(false)
  }

  /// Runs the learner.
  pub fn run(mut self) -> Res<()> {
    let mut teacher_alive = true ;
    profile!{ self "quals synthesized" => add 0 }
    profile!{ self "quals initially" => add self.qualifiers.qual_count() }
    profile!{
      self "qual count initially" =>
        add self.qualifiers.real_qual_count()
    }
    // if_verb!{
    //   teacher_alive = msg!{ & self => "Qualifiers:" } ;
    //   for quals in self.qualifiers.qualifiers() {
    //     for & (ref qual, _) in quals {
    //       teacher_alive = msg!{ & self => "  {}", qual }
    //     }
    //   }
    // }
    'learn: loop {
      if ! teacher_alive {
        bail!("teacher is dead T__T")
      }
      profile!{ self tick "waiting" }
      match self.recv() {
        Some(data) => {
          profile!{ self mark "waiting" }
          if let Some(candidates) = self.learn(data) ? {
            teacher_alive = self.send_cands(candidates) ? ;
            // if self.restart() {
            //   self.qualifiers.wipe()
            // }
          } else {
            bail!("can't synthesize candidates for this, sorry")
          }
        },
        None => {
          profile!{ self mark "waiting" }
          return self.finalize()
        },
      }
    }
  }

  /// Finalizes the learning process.
  #[cfg( not(feature = "bench") )]
  pub fn finalize(self) -> Res<()> {
    profile!{ self "quals once done" => add self.qualifiers.qual_count() }
    profile!{
      self "qual count once done" => add self.qualifiers.real_qual_count()
    }

    let success = self.core.stats(
      self._profiler, vec![ vec!["learning", "smt", "data"] ]
    ) ;
    if success {
      Ok(())
    } else {
      bail!("could not send statistics to teacher")
    }
  }
  #[cfg(feature = "bench")]
  pub fn finalize(self) -> Res<()> {
    Ok(())
  }

  /// Sends some candidates.
  ///
  /// Also resets the solver and clears declaration memory.
  pub fn send_cands(& mut self, candidates: Candidates) -> Res<bool> {
    profile!{ self tick "sending" }
    let res = self.send_candidates(
      candidates
    ) ;
    // Reset and clear declaration memory.
    self.solver.reset() ? ;
    for set in self.dec_mem.iter_mut() {
      set.clear()
    } ;
    profile!{ self mark "sending" }
    Ok(res)
  }

  /// Looks for a classifier.
  pub fn learn(
    & mut self, data: DataCore
  ) -> Res< Option<Candidates> > {
    profile! { self tick "learning" }
    profile! { self tick "learning", "setup" }
    self.data = data ;

    profile!{ self mark "learning", "setup" }

    let contradiction = self.setup_solver().chain_err(
      || "while initializing the solver"
    ) ? ;

    if contradiction {
      bail!( ErrorKind::Unsat )
    }

    let prd_count = self.instance.preds().len() ;
    debug_assert!{{
      let mut okay = true ;
      for term_opt in & self.candidate {
        okay = okay && term_opt.is_none() ;
      }
      okay
    }}
    // Stores `(<unclassified_count>, <classified_count>, <prd_index>)`
    debug_assert! { self.predicates.is_empty() }

    for pred in PrdRange::zero_to(prd_count) {
      // msg!{
      //   self => "current data:\n{}", self.data.to_string_info(& ()) ?
      // } ;
      if self.instance.is_known(pred) {
        continue
      }
      let pos_len = self.data.pos[pred].len() ;
      let neg_len = self.data.neg[pred].len() ;
      let unc_len = self.data.map[pred].len() ;
      if pos_len == 0 && neg_len > 0 {
        msg!( self => "legal_pred (1)" ) ;
        // Maybe we can assert everything as negative right away?
        if self.is_legal_pred(pred, false) ? {
          msg!(
            self =>
            "{} only has negative ({}) and unclassified ({}) data\n\
            legal check ok, assuming everything negative",
            self.instance[pred], neg_len, unc_len
          ) ;
          self.candidate[pred] = Some( term::fls() ) ;
          profile!{ self tick "learning", "data" }
          self.data.pred_all_false(pred) ? ;
          profile!{ self mark "learning", "data" }
          continue
        }
      }
      if neg_len == 0 && pos_len > 0 {
        msg!( self => "legal_pred (2)" ) ;
        // Maybe we can assert everything as positive right away?
        if self.is_legal_pred(pred, true) ? {
          msg!(
            self =>
            "{} only has positive ({}) and unclassified ({}) data\n\
            legal check ok, assuming everything positive",
            self.instance[pred], pos_len, unc_len
          ) ;
          self.candidate[pred] = Some( term::tru() ) ;
          self.data.pred_all_true(pred) ? ;
          continue
        }
      }
      self.predicates.push((
        unc_len, pos_len + neg_len, pred
      ))
    }

    use rand::Rng ;
    // Use simple entropy 30% of the time.
    let simple = conf.ice.simple_gain || self.rng.next_f64() <= 0.30 ;
    msg!{ self => "looking for qualifier (simple: {})...", simple } ;

    // Sort the predicates 70% of the time.
    if conf.ice.sort_preds && self.rng.next_f64() <= 0.70 {

      profile!{ self tick "learning", "predicate sorting" }
      self.predicates.sort_unstable_by(
        |
          & (
            unclassed_1, classed_1, _
          ), & (
            unclassed_2, classed_2, _
          )
        | {
          use std::cmp::Ordering::* ;
          match (unclassed_1, unclassed_2) {
            (0, 0) => classed_1.cmp(& classed_2).reverse(),
            (0, _) => Less,
            (_, 0) => Greater,
            (_, _) => match classed_1.cmp(& classed_2).reverse() {
              Equal => unclassed_1.cmp(& unclassed_2),
              res => res,
            },
          }
        }
      ) ;
      profile!{ self mark "learning", "predicate sorting" }

    } else {

      // Not sorting, forcing random order.
      profile!{ self tick "learning", "predicate sorting" }
      let mut rng = self.rng.clone() ;
      self.predicates.sort_unstable_by(
        |_, _| {
          use std::cmp::Ordering::* ;
          let rand = rng.next_f64() ;
          if rand <= 0.33 {
            Less
          } else if rand <= 0.66 {
            Equal
          } else {
            Greater
          }
        }
      ) ;
      profile!{ self mark "learning", "predicate sorting" }

    }

    'pred_iter: while let Some(
      (_unc, _cla, pred)
    ) = self.predicates.pop() {
      msg!(
        self => "{}: {} unclassified, {} classified",
                self.instance[pred], _unc, _cla
      ) ;
      let data = self.data.data_of(pred) ;
      if let Some(term) = self.pred_learn(
        pred, data, simple
      ) ? {
        self.candidate[pred] = Some(term)
      } else {
        return Ok(None)
      }
    }
    let mut candidates: PrdMap<_> = vec![
      None ; self.instance.preds().len()
    ].into() ;
    ::std::mem::swap(& mut candidates, & mut self.candidate) ;
    profile!{ self mark "learning" }

    // if conf.ice.decay {
    //   profile!{ self tick "decay" }
    //   let _brushed = self.qualifiers.brush_quals(
    //     used_quals, conf.ice.max_decay
    //   ) ;
    //   profile!{ self "brushed qualifiers" => add _brushed }
    //   profile!{ self mark "decay" }
    // }

    Ok( Some(candidates) )
  }


  /// Backtracks to the last element of `unfinished`.
  ///
  /// - updates blacklisted qualifiers
  /// - applies the current classification to the data we're backtracking to
  ///
  /// Returns `None` iff `unfinished` was empty meaning the learning process
  /// is over.
  pub fn backtrack(& mut self, pred: PrdIdx) -> Option<(Branch, CData)> {
    profile!{ self tick "learning", "backtrack" }
    // self.qualifiers.clear_blacklist() ;
    // Backtracking or exit loop.
    if let Some( (nu_branch, mut nu_data) ) = self.unfinished.pop() {
      // Update blacklisted qualifiers.
      // for & (ref t, _) in & nu_branch {
      //   self.qualifiers.blacklist(t)
      // }
      // Update data, some previously unclassified data may be classified now.
      self.data.classify(pred, & mut nu_data) ;
      profile!{ self mark "learning", "backtrack" }
      Some( (nu_branch, nu_data) )
    } else {
      profile!{ self mark "learning", "backtrack" }
      None
    }
  }

  /// Looks for a classifier for a given predicate.
  pub fn pred_learn(
    & mut self, pred: PrdIdx, mut data: CData, simple: bool
  ) -> Res< Option<Term> > {
    debug_assert!( self.finished.is_empty() ) ;
    debug_assert!( self.unfinished.is_empty() ) ;
    self.classifier.clear() ;

    msg!(
      self => "  working on predicate {} (pos: {}, neg: {}, unc: {})",
      self.instance[pred], data.pos.len(), data.neg.len(), data.unc.len()
    ) ;

    let mut branch = Vec::with_capacity(17) ;

    'learning: loop {


      // Checking whether we can close this branch.

      if data.neg.is_empty() && self.is_legal(
        pred, & data.unc, true
      ).chain_err(|| "while checking possibility of assuming positive") ? {
        msg!(
          self =>
            "  no more negative data, is_legal check ok\n  \
            forcing {} unclassifieds positive...", data.unc.len()
        ) ;
        profile!{ self tick "learning", "data" }
        for unc in data.unc {
          // let prev = self.classifier.insert(unc, true) ;
          // debug_assert!( prev.is_none() )
          self.data.stage_pos(pred, unc)
        }
        self.data.propagate() ? ;
        profile!{ self mark "learning", "data" }
        branch.shrink_to_fit() ;
        if branch.is_empty() {
          debug_assert!( self.finished.is_empty() ) ;
          debug_assert!( self.unfinished.is_empty() ) ;
          return Ok(
            Some( term::tru() )
          )
        } else {
          self.finished.push(branch) ;
        }
        if let Some((nu_branch, nu_data)) = self.backtrack(pred) {
          branch = nu_branch ;
          data = nu_data ;
          continue 'learning
        } else {
          break 'learning
        }
      }

      if data.pos.is_empty() && self.is_legal(
        pred, & data.unc, false
      ).chain_err(|| "while checking possibility of assuming negative") ? {
        msg!(
          self =>
            "  no more positive data, is_legal check ok\n  \
            forcing {} unclassifieds negative...", data.unc.len()
        ) ;
        profile!{ self tick "learning", "data" }
        for unc in data.unc {
          // let prev = self.classifier.insert(unc, false) ;
          // debug_assert!( prev.is_none() )
          self.data.stage_neg(pred, unc)
        }
        self.data.propagate() ? ;
        profile!{ self mark "learning", "data" }
        if branch.is_empty() {
          debug_assert!( self.finished.is_empty() ) ;
          debug_assert!( self.unfinished.is_empty() ) ;
          return Ok(
            Some( term::fls() )
          )
        }
        if let Some((nu_branch, nu_data)) = self.backtrack(pred) {
          branch = nu_branch ;
          data = nu_data ;
          continue 'learning
        } else {
          break 'learning
        }
      }



      // Could not close the branch, look for a qualifier.
      profile!{ self tick "learning", "qual" }
      let (qual, q_data, nq_data) = self.get_qualifier(pred, data, simple) ? ;
      profile!{ self mark "learning", "qual" }
      // msg!{ self => "qual: {}", qual } ;
      // self.qualifiers.blacklist(& qual) ;

      // Remember the branch where qualifier is false.
      let mut nq_branch = branch.clone() ;
      nq_branch.push( (qual.clone(), false) ) ;
      self.unfinished.push( (nq_branch, nq_data) ) ;

      // Update current branch and data.
      branch.push( (qual, true) ) ;
      data = q_data ;

      // Keep going.
    }

    profile!{ self tick "learning", "pred finalize" }
    debug_assert!( self.unfinished.is_empty() ) ;
    let mut or_args = Vec::with_capacity( self.finished.len() ) ;
    for branch in self.finished.drain(0..) {
      let mut and_args = Vec::with_capacity( branch.len() ) ;
      for (term, pos) in branch {
        if pos {
          and_args.push(term)
        } else {
          and_args.push( term::app(Op::Not, vec![term]) )
        }
      }
      or_args.push( term::app(Op::And, and_args) )
    }
    profile!{ self mark "learning", "pred finalize" }
    Ok(
      Some( term::app(Op::Or, or_args) )
    )
  }

  /// Looks for a qualifier. Requires a mutable `self` in case it needs to
  /// synthesize a qualifier.
  ///
  /// Does **not** blacklist the qualifier it returns.
  ///
  /// Be careful when modifying this function as it as a (tail-)recursive call.
  /// The recursive call is logically guaranteed not cause further calls and
  /// terminate right away. Please be careful to preserve this.
  ///
  /// The `simple` flag forces to use simple, unclassified-agnostic gain.
  pub fn get_qualifier(
    & mut self, pred: PrdIdx, data: CData, simple: bool
  ) -> Res< (Term, CData, CData) > {

    macro_rules! best_qual {
      (only new: $new:expr) => ({
        if simple {
          profile!{ self tick "learning", "qual", "simple gain" }
          let res = self.qualifiers.maximize(
            pred, |qual| data.simple_gain(qual), $new
          ) ? ;
          profile!{ self mark "learning", "qual", "simple gain" }
          if res.is_none() {
            let qualifiers = & mut self.qualifiers ;
            let all_data = & self.data ;
            profile!{ self tick "learning", "qual", "gain" }
            let res = qualifiers.maximize(
              pred, |qual| data.gain(pred, all_data, qual), false
            ) ;
            profile!{ self mark "learning", "qual", "gain" }
            res
          } else {
            Ok(res)
          }
        } else {
          let qualifiers = & mut self.qualifiers ;
          let all_data = & self.data ;
          profile!{ self tick "learning", "qual", "gain" }
          let res = qualifiers.maximize(
            pred, |qual| data.gain(pred, all_data, qual), $new
          ) ;
          profile!{ self mark "learning", "qual", "gain" }
          res
        }
      }) ;
    }

    if conf.ice.qual_print {
      self.qualifiers.log()
    }

    let mut best_qual = best_qual! ( only new: false ) ? ;

    if let Some((qual, gain)) = best_qual {
      // println!("gain: {}", gain) ;
      best_qual = if gain >= conf.ice.gain_pivot {
        // This qualifier is satisfactory.
        profile!{ self tick "learning", "qual", "data split" }
        let (q_data, nq_data) = data.split(& qual) ;
        profile!{ self mark "learning", "qual", "data split" }
        return Ok( (qual, q_data, nq_data) )
      } else {
        // Not good enough, maybe synthesis can do better.
        Some((qual, gain))
      }
    }

    // if_verb!{
    //   let mut msg = format!(
    //     "\ncould not split remaining data for {}:\n", self.instance[pred]
    //   ) ;
    //   msg.push_str("pos (") ;
    //   for pos in & data.pos {
    //     msg.push_str( & format!("\n    {}", pos) )
    //   }
    //   msg.push_str("\n) neg (") ;
    //   for neg in & data.neg {
    //     msg.push_str( & format!("\n    {}", neg) )
    //   }
    //   msg.push_str("\n) unc (") ;
    //   for unc in & data.unc {
    //     msg.push_str( & format!("\n    {}", unc) )
    //   }
    //   msg.push_str("\n)") ;
    //   msg!{ self => msg } ;
    // }

    if data.pos.is_empty() && data.neg.is_empty() && data.unc.is_empty() {
      bail!("[bug] cannot synthesize qualifier based on no data")
    }

    // Synthesize qualifier separating the data.
    self.synthesize(pred, & data, & mut best_qual) ? ;

    if let Some((qual, _)) = best_qual {
      profile!{ self tick "learning", "qual", "data split" }
      let (q_data, nq_data) = data.split(& qual) ;
      profile!{ self mark "learning", "qual", "data split" }
      Ok( (qual, q_data, nq_data) )
    } else {
      bail!("unable to split data after synthesis...")
    }
  }

  /// Qualifier synthesis.
  pub fn synthesize(
    & mut self, pred: PrdIdx, data: & CData, best: & mut Option<(Term, f64)>
  ) -> Res<()> {

    // println!("synth") ;

    profile!{ self tick "learning", "qual", "synthesis" }
    scoped! {
      let self_data = & self.data ;
      let quals = & mut self.qualifiers ;
      let instance = & self.instance ;
      let profiler = & self._profiler ;
      let self_msg = & self.core ;

      let mut treatment = |term: Term| {
        if let Some(gain) = data.gain(pred, self_data, & term) ? {
          if gain >= conf.ice.gain_pivot {
            quals.insert(& term, pred) ? ;
            ()
          }
          if let Some( (ref mut old_term, ref mut old_gain) ) = * best {
            if * old_gain < gain {
              * old_gain = gain ;
              * old_term = term
            }
          } else {
            * best = Some((term, gain))
          }
          Ok(gain >= conf.ice.gain_pivot_synth)
        } else {
          Ok(false)
        }
      } ;

      use self::synth::SynthSys ;
      let mut synth_sys = SynthSys::new( & instance[pred].sig ) ;

      'synth: loop {

        for sample in data.iter() {
          msg! { * self_msg => "starting synthesis" } ;
          let done = synth_sys.sample_synth(
            sample, & mut treatment, profiler
          ).chain_err(
            || "during synthesis from sample"
          ) ? ;
          msg! { * self_msg => "done with synthesis" } ;
          if done { break }
        }

        synth_sys.increment() ;
        if synth_sys.is_done() {
          break 'synth
        }

      }
    }
    profile!{ self mark "learning", "qual", "synthesis" } ;
    Ok(())
  }


  /// Checks whether assuming some data as positive (if `pos` is true,
  /// negative otherwise) is legal.
  ///
  /// **NB**: if assuming the data positive / negative is legal,
  /// the data will be forced to be positive / negative in the solver
  /// automatically. Otherwise, the actlit is deactivated.
  pub fn is_legal(
    & mut self, pred: PrdIdx, unc: & HSamples, pos: bool
  ) -> Res<bool> {
    if unc.is_empty() { return Ok(true) }
    profile!{ self tick "learning", "smt", "legal" }

    // Wrap actlit and increment counter.
    let actlit = self.solver.get_actlit() ? ;
    let actlit = ActWrap { actlit, pred, unc, pos } ;
    self.solver.assert( & actlit ) ? ;
    let actlit = actlit.destroy() ;

    let legal = if self.solver.check_sat_act( Some(& actlit) ) ? {
      profile!{ self mark "learning", "smt", "legal" }
      true
    } else {
      profile!{ self mark "learning", "smt", "legal" }
      false
    } ;
    self.solver.set_actlit(actlit, legal) ? ;
    Ok(legal)
  }


  /// Checks whether assuming **all** the unclassified data from a predicate as
  /// `pos` is legal.
  ///
  /// **NB**: if assuming the data positive / negative is legal, the data will
  /// be forced to be positive / negative in the solver automatically.
  /// Otherwise, the actlit is deactivated (`assert (not <actlit>)`).
  pub fn is_legal_pred(
    & mut self, pred: PrdIdx, pos: bool
  ) -> Res<bool> {
    profile!{ self tick "learning", "smt", "all legal" }
    let unc = & self.data.map[pred] ;
    if unc.is_empty() {
      profile!{ self mark "learning", "smt", "all legal" }
      return Ok(true)
    }

    // Wrap actlit and increment counter.
    let actlit = self.solver.get_actlit() ? ;
    let actlit = ActWrap { actlit, pred, unc, pos } ;
    self.solver.assert( & actlit ) ? ;
    let actlit = actlit.destroy() ;

    let legal = if self.solver.check_sat_act( Some(& actlit) ) ? {
      profile!{ self mark "learning", "smt", "all legal" }
      true
    } else {
      profile!{ self mark "learning", "smt", "all legal" }
      false
    } ;
    self.solver.set_actlit(actlit, legal) ? ;
    Ok(legal)
  }


  /// Sets the solver to check that constraints are respected.
  ///
  /// Returns `true` if a contradiction was found.
  ///
  /// - **does not** reset the solver or clean declaration memory (must be
  ///   done before sending previous candidates)
  /// - **defines** pos (neg) data as `true` (`false`)
  /// - **declares** samples that neither pos nor neg
  /// - asserts constraints
  pub fn setup_solver(& mut self) -> Res<bool> {
    profile!{ self tick "learning", "smt", "setup" }
    
    // Dummy arguments used in the `define_fun` for pos (neg) data.
    let args: [ (SWrap, Typ) ; 0 ] = [] ;

    // Positive data.
    self.solver.comment("Positive data:") ? ;
    for (pred, set) in self.data.pos.index_iter() {
      for sample in set.iter() {
        let is_new = self.dec_mem[pred].insert( sample.uid() ) ;
        debug_assert!(is_new) ;
        self.solver.define_fun(
          & SWrap(pred, sample), & args, & Typ::Bool, & "true"
        ) ?
      }
    }
    // Negative data.
    self.solver.comment("Negative data:") ? ;
    for (pred, set) in self.data.neg.index_iter() {
      for sample in set.iter() {
        let is_new = self.dec_mem[pred].insert( sample.uid() ) ;
        if ! is_new {
          // Contradiction found.
          return Ok(true)
        }
        self.solver.define_fun(
          & SWrap(pred, sample), & args, & Typ::Bool, & "false"
        ) ?
      }
    }

    self.solver.comment("Sample declarations for constraints:") ? ;
    // Declare all samples used in constraints.
    for (pred, map) in self.data.map.index_iter() {
      // if let Some(term) = self.instance.term_of(pred) {
      //   if term.is_true() {
      //     self.solver.comment(
      //       & format!(
      //         "Predicate {} is forced to be `true`:", self.instance[pred]
      //       )
      //     ) ? ;
      //     for (sample, _) in map.read().map_err(corrupted_err)?.iter() {
      //       let uid = sample.uid() ;
      //       if ! self.dec_mem[pred].contains(& uid) {
      //         let _ = self.dec_mem[pred].insert(uid) ;
      //         self.solver.define_fun(
      //           & SWrap(pred, sample), & args, & Typ::Bool, & "true", & ()
      //         ) ?
      //       }
      //     }
      //   } else {
      //     bail!(
      //       "predicate {} is forced to {}, unsupported for now",
      //       self.instance[pred], term
      //     )
      //   }
      // } else {
        for (sample, _) in map.iter() {
          let uid = sample.uid() ;
          if ! self.dec_mem[pred].contains(& uid) {
            let _ = self.dec_mem[pred].insert(uid) ;
            self.solver.declare_const(
              & SWrap(pred, sample), & Typ::Bool
            ) ?
          }
        }
      // }
    }

    self.solver.comment("Constraints:") ? ;
    // Assert all constraints.
    for constraint in self.data.constraints.iter() {
      if ! constraint.is_tautology() {
        self.solver.assert( & CWrap(constraint) ) ?
      }
    }
    profile!{ self mark "learning", "smt", "setup" }

    Ok(false)
  }
}

impl<
  'core, 'kid, Slver: Solver<'kid, Parser>
> HasLearnerCore for IceLearner<'core, Slver> {
  fn core(& self) -> & LearnerCore { self.core }
}




/// Smt-related things.
pub mod smt {
  use std::str::FromStr ;
  use std::io::BufRead ;

  use rsmt2::parse::{ IdentParser, ValueParser, SmtParser } ;
  use rsmt2::to_smt::* ;
  use rsmt2::actlit::Actlit ;

  use common::* ;
  use common::data::* ;



  /// Can parse values (int) and idents (`VarIdx`).
  ///
  /// In the ice learner, parsing is only used for synthesizing, not for
  /// conflict detection.
  #[derive(Clone, Copy)]
  pub struct Parser ;

  impl<'a> IdentParser<Option<VarIdx>, (), & 'a str> for Parser {
    fn parse_ident(self, input: & 'a str) -> SmtRes< Option<VarIdx> > {
      if input ==  "v" { return Ok(None) }

      debug_assert_eq!( & input[0..2], "v_" ) ;
      match usize::from_str(& input[2..]) {
        Ok(idx) => Ok( Some(idx.into()) ),
        Err(e) => bail!(
          "could not retrieve var index from `{}`: {}", input, e
        ),
      }
    }
    fn parse_type(self, _: & 'a str) -> SmtRes<()> {
      Ok(())
    }
  }

  impl<'a, Br> ValueParser<Int, & 'a mut SmtParser<Br>> for Parser
  where Br: BufRead {
    fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Int> {
      if let Some(val) = input.try_int::<
        _, _, ::num::bigint::ParseBigIntError
      >(
        |int, pos| {
          let int = Int::from_str(int) ? ;
          Ok( if ! pos { - int } else { int } )
        }
      ) ? {
        Ok(val)
      } else {
        input.fail_with("unexpected value")
      }
    }
  }

  /// Wrapper around predicate / sample that forces smt printing.
  pub struct SWrap<'a>(pub PrdIdx, pub & 'a HSample) ;
  impl<'a> Expr2Smt<()> for SWrap<'a> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: ()
    ) -> SmtRes<()> {
      write!( w, "|p_{} {}|", self.0, self.1.uid() ) ? ;
      Ok(())
    }
  }
  impl<'a> Sym2Smt<()> for SWrap<'a> {
    fn sym_to_smt2<Writer>(
      & self, w: & mut Writer, _: ()
    ) -> SmtRes<()> where Writer: Write {
      self.expr_to_smt2(w, ())
    }
  }


  /// Wrapper around constraints that forces smt printing consistent with
  /// [`SWrap`](struct.SWrap.html).
  pub struct CWrap<'a>(pub & 'a Constraint) ;
  impl<'a> Expr2Smt<()> for CWrap<'a> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: ()
    ) -> SmtRes<()> {
      write!(w, "(=> (and") ? ;
      for lhs in & self.0.lhs {
        write!(w, " ", ) ? ;
        SWrap(lhs.pred, & lhs.args).expr_to_smt2(w, ()) ?
      }
      write!(w, ") ") ? ;
      if let Some(rhs) = self.0.rhs.as_ref() {
        SWrap(rhs.pred, & rhs.args).expr_to_smt2(w, ()) ?
      } else {
        write!(w, "false") ? ;
      }
      write!(w, ")") ? ;
      Ok(())
    }
  }

  /// Wrapper for activation literals activating samples for some predicate.
  ///
  /// `Sym2Smt` implementation just yields the actlit, used to declare said
  /// actlit. `Expr2Smt` is the actual activation expression
  ///
  /// ```bash
  /// (=> <actlit> (and <samples>))
  /// ```
  pub struct ActWrap<Samples> {
    /// Activation literal.
    pub actlit: Actlit,
    /// Predicate.
    pub pred: PrdIdx,
    /// Samples.
    pub unc: Samples,
    /// Indicates whether we're assuming the samples positive or negative.
    pub pos: bool,
  }
  impl<Samples> ActWrap<Samples> {
    /// Retrieve the actlit by destroying the wrapper.
    pub fn destroy(self) -> Actlit { self.actlit }
  }
  impl<'a> Expr2Smt<()> for ActWrap<& 'a HSamples> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: ()
    ) -> SmtRes<()> {
      write!(w, "(=> ") ? ;
      self.actlit.write(w) ? ;
      write!(
        w, " ({}", if self.pos { "and" } else { "not (or" }
      ) ? ;
      for unc in self.unc {
        write!(w, " ", ) ? ;
        SWrap(self.pred, unc).expr_to_smt2(w, ()) ?
      }
      write!(w, "))") ? ;
      if ! self.pos {
        write!(w, ")") ?
      }
      Ok(())
    }
  }
  impl<'a, T> Expr2Smt<()> for ActWrap<
    & 'a HConMap<HSample, T>
  > {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: ()
    ) -> SmtRes<()> {
      write!(w, "(=> ") ? ;
      self.actlit.write(w) ? ;
      write!(
        w, " ({}", if self.pos { "and" } else { "not (or" }
      ) ? ;
      for (unc, _) in self.unc {
        write!(w, " ", ) ? ;
        SWrap(self.pred, unc).expr_to_smt2(w, ()) ?
      }
      write!(w, "))") ? ;
      if ! self.pos {
        write!(w, ")") ?
      }
      Ok(())
    }
  }


  /// Wrapper around some values and some coefficients, used by
  /// [synthesize](../struct.IceLearner.html#method.synthesize) to assert the
  /// constraints on its points.
  ///
  /// The expression it encodes is
  ///
  /// ```bash
  /// v_1 * c_1 + ... + v_n * c_n + self.cst >= 0 # if `self.pos`
  /// v_1 * c_1 + ... + v_n * c_n + self.cst  < 0 # otherwise
  /// ```
  ///
  /// where `[ v_1, ..., v_n ] = self.vals` and
  /// `[ c_1, ..., c_n ] = self.coefs`.
  pub struct ValCoefWrap<'a> {
    /// Values.
    pub vals: & 'a Vec<Int>,
    /// Coefficients.
    pub coefs: & 'a Vec<VarIdx>,
    /// Constant.
    pub cst: & 'static str,
    /// Positivity of the values.
    pub pos: bool,
  }
  impl<'a> ValCoefWrap<'a> {
    /// Constructor.
    pub fn new(
      vals: & 'a Vec<Int>, coefs: & 'a Vec<VarIdx>,
      cst: & 'static str, pos: bool
    ) -> Self {
      debug_assert!( vals.len() == coefs.len() ) ;
      ValCoefWrap { vals, coefs, cst, pos }
    }
  }
  impl<'a> Expr2Smt<()> for ValCoefWrap<'a> {
    fn expr_to_smt2<Writer>(
      & self, w: & mut Writer, _: ()
    ) -> SmtRes<()> where Writer: Write {
      if self.pos { write!(w, "(>= (+") } else { write!(w, "(< (+") } ? ;
      for (val, coef) in self.vals.iter().zip( self.coefs ) {
        write!(w, " (* {} ", val) ? ;
        coef.sym_to_smt2(w, ()) ? ;
        write!(w, ")") ?
      }
      write!(w, " {}) 0)", self.cst) ? ;
      Ok(())
    }
  }
}

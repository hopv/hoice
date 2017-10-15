//! ICE learner.

use common::* ;
use common::data::* ;
use common::msg::* ;
use self::mining::* ;
use self::smt::* ;

pub mod mining ;

pub use self::svm::SvmSynth ;




/// Launcher.
pub struct Launcher ;
unsafe impl Sync for Launcher {}
unsafe impl Send for Launcher {}
impl Launcher {
  /// Launches an smt learner.
  pub fn launch(
    core: & LearnerCore, instance: Arc<Instance>, data: Data
  ) -> Res<()> {
    use rsmt2::{ solver, Kid } ;
    let mut kid = Kid::new( conf.solver.conf() ).chain_err(
      || "while spawning the teacher's solver"
    ) ? ;
    let conflict_solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    let mut synth_kid = Kid::new( conf.solver.conf() ).chain_err(
      || "while spawning the teacher's synthesis solver"
    ) ? ;
    let synth_solver = solver(& mut synth_kid, Parser).chain_err(
      || "while constructing the teacher's synthesis solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("ice_learner") ? {
      let synth_log = conf.solver.log_file("ice_learner_synth")?.expect(
        "[unreachable] log mod is active"
      ) ;
      IceLearner::new(
        & core, instance, data,
        conflict_solver.tee(log), synth_solver.tee(synth_log)
      ).chain_err(
        || "while creating ice learner"
      )?.run()
    } else {
      IceLearner::new(
        & core, instance, data, conflict_solver, synth_solver
      ).chain_err(
        || "while creating ice learner"
      )?.run()
    }
  }
}
impl Learner for Launcher {
  fn run(
    & self, core: LearnerCore, instance: Arc<Instance>, data: Data
  ) {
    if let Err(e) = Self::launch(& core, instance, data) {
      let _ = core.err(e) ;
    }
  }
  fn description(& self) -> String {
    "ice".into()
  }
}

/// Ice learner.
pub struct IceLearner<'core, Slver> {
  /// Arc to the instance.
  pub instance: Arc<Instance>,
  /// Qualifiers for the predicates.
  pub qualifiers: Qualifiers,
  /// Current data.
  data: Data,
  /// Solver used to check if the constraints are respected.
  solver: Slver,
  /// Solver used to synthesize an hyperplane separating two points.
  synth_solver: Slver,
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
  /// Activation literal counter.
  actlit: usize,
  /// Set storing new qualifiers during synthesis (avoids allocation).
  new_quals: Quals,
  /// Profiler.
  _profiler: Profiler,
  /// SVM synthesizer.
  _svm_synth: SvmSynth,
}
impl<'core, 'kid, Slver> IceLearner<'core, Slver>
where Slver: Solver<'kid, Parser> {
  /// Ice learner constructor.
  pub fn new(
    core: & 'core LearnerCore, instance: Arc<Instance>, data: Data,
    solver: Slver, synth_solver: Slver
  ) -> Res<Self> {
    let _profiler = Profiler::new() ;
    profile!{ |_profiler| tick "mining" }
    let qualifiers = Qualifiers::new(& * instance).chain_err(
      || "while creating qualifier structure"
    ) ? ;
    let mut new_quals = Quals::with_capacity(
      qualifiers.qualifiers().len()
    ) ;
    for map in qualifiers.qualifiers() {
      new_quals.push( HConMap::with_capacity( map.len() ) )
    }
    profile!{ |_profiler| mark "mining" }
    if_verb!{
      log_info!{ "qualifiers:" } ;
      for quals in qualifiers.qualifiers() {
        for (qual, _) in quals {
          log_info!("- {}", qual)
        }
      }
    }
    let dec_mem = vec![
      HashSet::with_capacity(103) ; instance.preds().len()
    ].into() ;
    let candidate = vec![ None ; instance.preds().len() ].into() ;
    Ok(
      IceLearner {
        instance, qualifiers, data, solver, synth_solver, core,
        finished: Vec::with_capacity(103),
        unfinished: Vec::with_capacity(103),
        classifier: HashMap::with_capacity(1003),
        dec_mem, candidate, actlit: 0,
        new_quals,
        _profiler,
        _svm_synth: SvmSynth::new(),
      }
    )
  }

  /// Runs the learner.
  pub fn run(mut self) -> Res<()> {
    let mut teacher_alive = true ;
    profile!{ self "qualifier synthesized" => add 0 }
    profile!{ self "qualifiers initially" => add self.qualifiers.count() }
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
            teacher_alive = self.send_cands(candidates) ?
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
    profile!{ self "qualifiers once done" => add self.qualifiers.count() }

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

  // /// Applies the information in the classifier to some data.
  // pub fn classify(& self, data: & mut CData) {
  //   let mut count = 0 ;
  //   for (classified, val) in & self.classifier {
  //     let val = * val ;
  //     let classified = data.unc.take(classified) ;
  //     if let Some(sample) = classified {
  //       count += 1 ;
  //       if val {
  //         let _ = data.pos.insert( sample ) ;
  //       } else if ! val {
  //         let _ = data.neg.insert( sample ) ;
  //       }
  //     }
  //   }
  //   if count != 0 {
  //     println!("classified {} samples", count)
  //   } else {
  //     msg!{ self => "no new classification detected" } ;
  //   }
  // }

  /// Looks for a classifier.
  ///
  /// # TO DO
  ///
  /// - factor vectors created in this function to avoid reallocation
  pub fn learn(
    & mut self, mut data: Data
  ) -> Res< Option<Candidates> > {
    profile!{ self tick "learning" }
    profile!{ self tick "learning", "setup" }
    let _new_samples = data.drain_new_samples() ;
    self.data = data ;
    self.qualifiers.clear_blacklist() ;
    profile!{ self mark "learning", "setup" }
    // profile!{ self tick "learning", "new sample registration" }
    // self.qualifiers.register_samples( new_samples ) ? ;
    // profile!{ self mark "learning", "new sample registration" }

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
    let mut predicates = Vec::with_capacity(prd_count) ;

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
      predicates.push((
        unc_len, pos_len + neg_len, pred
      ))
    }

    profile!{ self tick "learning", "predicate sorting" }
    predicates.sort_by(
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

    let mut used_quals = HConSet::with_capacity(107) ;

    'pred_iter: for (_unc, _cla, pred) in predicates {
      msg!(
        self => "{}: {} unclassified, {} classified",
                self.instance[pred], _unc, _cla
      ) ;
      let data = self.data.data_of(pred) ;
      if let Some(term) = self.pred_learn(pred, data, & mut used_quals) ? {
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

    if conf.ice.decay {
      profile!{ self tick "decay" }
      let _brushed = self.qualifiers.brush_quals(
        used_quals, conf.ice.max_decay
      ) ;
      profile!{ self "brushed qualifiers" => add _brushed }
      profile!{ self mark "decay" }
    }

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
    self.qualifiers.clear_blacklist() ;
    // Backtracking or exit loop.
    if let Some( (nu_branch, mut nu_data) ) = self.unfinished.pop() {
      // Update blacklisted qualifiers.
      for & (ref t, _) in & nu_branch {
        self.qualifiers.blacklist(t)
      }
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
    & mut self, pred: PrdIdx, mut data: CData, used_quals: & mut HConSet<RTerm>
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
      msg!{ self => "looking for qualifier..." } ;
      let (qual, q_data, nq_data) = self.get_qualifier(
        pred, data, used_quals
      ) ? ;
      profile!{ self mark "learning", "qual" }
      // msg!{ self => "qual: {}", qual } ;
      self.qualifiers.blacklist(& qual) ;

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

  /// Gets the best qualifier if any, parallel version using `rayon`.
  pub fn get_best_qualifier_para<
    'a, Key: Send, I: ::rayon::iter::IntoParallelIterator<
      Item = (Key, & 'a mut QualValues)
    >
  >(
    _profiler: & Profiler, all_data: & Data,
    pred: PrdIdx, data: & CData, quals: I,
    used_quals: & mut HConSet<RTerm>
  ) -> Res< Option< (f64, & 'a mut QualValues) > > {
    use rayon::prelude::* ;

    profile!{ |_profiler| tick "learning", "qual", "// gain" }

    let mut gains: Vec<_> = quals.into_par_iter().map(
      |(_, values)| match data.gain(pred, all_data, values) {
        Ok( Some((gain, _, _)) ) => Ok( Some( (gain, values) ) ),
        Ok( None ) => Ok(None),
        Err(e) => Err(e),
      }
    ).collect() ;

    profile!{ |_profiler| mark "learning", "qual", "// gain" }

    profile!{ |_profiler| tick "learning", "qual", "gain sort" }

    gains.sort_by(
      |lft, rgt| {
        use ::std::cmp::Ordering::* ;
        match (lft, rgt) {
          ( & Err(_), _   ) |
          ( _, & Ok(None) ) => Greater,
          ( _, & Err(_)   ) |
          ( & Ok(None), _ ) => Less,

          (
            & Ok( Some((lft_gain, ref lft_values)) ),
            & Ok( Some((rgt_gain, ref rgt_values)) )
          ) => match lft_gain.partial_cmp(& rgt_gain) {
            None | Some(Equal) => lft_values.qual.cmp(& rgt_values.qual),
            Some(res) => res
          }
        }
      }
    ) ;

    profile!{ |_profiler| mark "learning", "qual", "gain sort" }

    let res = if let Some(res) = gains.pop() { res } else {
      bail!("[bug] empty QualIter")
    } ;
    if conf.ice.decay {
      if let & Ok( Some( (best_gain, ref qual) ) ) = & res {
        let _ = used_quals.insert( qual.qual.clone() ) ;
        while let Some( Ok( Some( (gain, qual) ) ) ) = gains.pop() {
          if best_gain == gain {
            let _ = used_quals.insert( qual.qual.clone() ) ;
          } else {
            break
          }
        }
      }
    }
    res
  }

  /// Gets the best qualifier if any, sequential version.
  pub fn get_best_qualifier_seq<
    'a, Key, I: IntoIterator<Item = (Key, & 'a mut QualValues)>
  >(
    _profiler: & Profiler, all_data: & Data,
    pred: PrdIdx, data: & CData, quals: I,
  ) -> Res< Option< (f64, & 'a mut QualValues) > > {
    let mut maybe_qual: Option<(f64, & mut QualValues)> = None ;

    profile!{ |_profiler| tick "learning", "qual", "gain" }
    'search_qual: for (_, values) in quals {
      if let Some(
        (gain, (_q_pos, _q_neg, _q_unc), (_nq_pos, _nq_neg, _nq_unc))
      ) = data.gain(pred, all_data, values) ? {
        let better = if let Some( (old_gain, _) ) = maybe_qual {
          old_gain < gain
        } else { true } ;
        if better {
          maybe_qual = Some( (gain, values) )
        }
        if gain == 1. { break 'search_qual }
      }
    }
    profile!{ |_profiler| mark "learning", "qual", "gain" }

    Ok( maybe_qual )
  }

  /// Gets the best qualifier if any.
  pub fn get_best_qualifier<
    'a, Key: Send, I: IntoIterator<Item = (Key, & 'a mut QualValues)>
  >(
    profiler: & Profiler, all_data: & Data,
    pred: PrdIdx, data: & CData, quals: I,
    used_quals: & mut HConSet<RTerm>,
  ) -> Res< Option< (f64, & 'a mut QualValues) > > {
    if conf.ice.gain_threads == 1 {
      match Self::get_best_qualifier_seq(
        profiler, all_data, pred, data, quals.into_iter()
      ) {
        Ok( Some( (gain, qual) ) ) => {
          let _ = used_quals.insert( qual.qual.clone() ) ;
          Ok( Some( (gain, qual) ) )
        },
        res => res,
      }
    } else {
      let quals: Vec<_> = quals.into_iter().collect() ;
      Self::get_best_qualifier_para(
        profiler, all_data, pred, data, quals, used_quals
      )
    }
  }

  /// Looks for a qualifier. Requires a mutable `self` in case it needs to
  /// synthesize a qualifier.
  ///
  /// Does **not** blacklist the qualifier it returns.
  ///
  /// Be careful when modifying this function as it as a (tail-)recursive call.
  /// The recursive call is logically guaranteed not cause further calls and
  /// terminate right away. Please be careful to preserve this.
  pub fn get_qualifier(
    & mut self, pred: PrdIdx, data: CData, used_quals: & mut HConSet<RTerm>
  ) -> Res< (Term, CData, CData) > {

    // println!("running svm synthesis...") ;
    // if let Some(plan_sum) = self._svm_synth.synthesize(
    //   & self.instance[pred].sig, & data.pos, & data.neg
    // ).chain_err(|| "during SVM synthesis") ? {
    //   println!("  it works: {}", plan_sum) ;
    //   if let Some(var) = plan_sum.highest_var() {
    //     let arity: Arity = ( (* var) + 1 ).into() ;
    //     self.qualifiers.add_quals(
    //       arity, vec![
    //         term::ge( plan_sum.clone(), term::int(0) ),
    //         term::le( plan_sum, term::int(0) ),
    //       ]
    //     ) ?
    //   }
    // } else {
    //   println!("  failed")
    // }

    if let Some( (_gain, values) ) = Self::get_best_qualifier(
      & self._profiler, & self.data, pred, & data, self.qualifiers.of(pred),
      used_quals
    ) ? {
      let (q_data, nq_data) = data.split(values) ;
      // msg!(
      //   self.core =>
      //     "  using qualifier {} | \
      //     gain: {}, pos: ({},{},{}), neg: ({},{},{})",
      //     values.qual.string_do(
      //       & self.instance[pred].sig.index_iter().map(
      //         |(idx, typ)| ::instance::info::VarInfo {
      //           name: format!("v_{}", idx), typ: * typ, idx
      //         }
      //       ).collect(), |s| s.to_string()
      //     ).unwrap(),
      //     _gain,
      //     q_data.pos.len(),
      //     q_data.neg.len(),
      //     q_data.unc.len(),
      //     nq_data.pos.len(),
      //     nq_data.neg.len(),
      //     nq_data.unc.len(),
      // ) ;
      return Ok( (values.qual.clone(), q_data, nq_data) )
    }

    // Reachable only if none of our qualifiers can split the data.

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

    if_not_bench!{
      for map in & self.new_quals {
        debug_assert!( map.is_empty() )
      }
    }

    // Synthesize qualifier separating the data.
    profile!{ self tick "learning", "qual", "synthesis" }
    if conf.ice.fpice_synth {
      if data.pos.is_empty() && data.neg.is_empty() && data.unc.is_empty() {
        bail!("[bug] cannot synthesize qualifier based on no data")
      }

      // // println!("running svm synthesis...") ;
      // if let Some(plan_sum) = self.svm_synth.synthesize(
      //   & self.instance[pred].sig, & data.pos, & data.neg
      // ).chain_err(|| "during SVM synthesis") ? {
      //   // println!("  it works: {}", plan_sum)
      // } else {
      //   // println!("  failed")
      // }

      for sample in & data.pos {
        self.synthesize(sample)
      }
      for sample in & data.neg {
        self.synthesize(sample)
      }
      for sample in & data.unc {
        self.synthesize(sample)
      }

      profile!{ self "qualifier synthesized" => add self.new_quals.len() }
    } else {
      let qual = match (
        data.pos.is_empty(), data.neg.is_empty(), data.unc.is_empty()
      ) {
        (false, false, _) => Self::smt_synthesize(
          & mut self.synth_solver, & data.pos[0], true, & data.neg[0]
        ) ?,
        (false, _, false) => Self::smt_synthesize(
          & mut self.synth_solver, & data.pos[0], true, & data.unc[0]
        ) ?,
        (true, false, false) => Self::smt_synthesize(
          & mut self.synth_solver, & data.neg[0], false, & data.unc[0]
        ) ?,
        (true, true, false) if data.unc.len() > 1 => Self::smt_synthesize(
          & mut self.synth_solver, & data.unc[0], true, & data.unc[1]
        ) ?,
        _ => bail!(
          "[unreachable] illegal status reached on predicate {}:\n\
          cannot synthesize candidate for data\n\
          pos: {:?}\n\
          neg: {:?}\n\
          unc: {:?}\n",
          self.instance[pred], data.pos, data.neg, data.unc
        ),
      } ;
      profile!{ self "qualifier synthesized" => add 1 }
      let arity: Arity = if let Some(max_var) = qual.highest_var() {
        (1 + * max_var).into()
      } else {
        bail!("[bug] trying to add constant qualifier")
      } ;
      self.new_quals[arity].insert( qual.clone(), QualValues::new(qual) ) ;
    } ;
    profile!{ self mark "learning", "qual", "synthesis" }

    
    let res = if let Some( (_gain, values) ) = Self::get_best_qualifier(
      & self._profiler, & self.data, pred, & data,
      self.new_quals.iter_mut().flat_map(
        |map| map.iter_mut()
      ),
      used_quals
    ) ? {
      let (q_data, nq_data) = data.split(values) ;
      // msg!(
      //   self.core =>
      //     "  using synthetic qualifier {} | \
      //     gain: {}, pos: ({},{},{}), neg: ({},{},{})",
      //     values.qual.string_do(
      //       & self.instance[pred].sig.index_iter().map(
      //         |(idx, typ)| ::instance::info::VarInfo {
      //           name: format!("v_{}", idx), typ: * typ, idx
      //         }
      //       ).collect(), |s| s.to_string()
      //     ).unwrap(),
      //     _gain,
      //     q_data.pos.len(),
      //     q_data.neg.len(),
      //     q_data.unc.len(),
      //     nq_data.pos.len(),
      //     nq_data.neg.len(),
      //     nq_data.unc.len(),
      // ) ;
      Ok( (values.qual.clone(), q_data, nq_data) )
    } else {
      bail!("[bug] unable to split the data after synthesis...")
    } ;

    self.qualifiers.add_qual_values(& mut self.new_quals) ? ;

    res
  }


  /// Checks whether assuming some data as positive (if `pos` is true,
  /// negative otherwise) is legal.
  ///
  /// **NB**: if assuming the data positive / negative is legal,
  /// the data will be forced to be positive / negative in the solver
  /// automatically. Otherwise, the actlit is deactivated
  /// (`assert (not <actlit>)`).
  pub fn is_legal(
    & mut self, pred: PrdIdx, unc: & HSamples, pos: bool
  ) -> Res<bool> {
    if unc.is_empty() { return Ok(true) }
    profile!{ self tick "learning", "smt", "legal" }

    // Wrap actlit and increment counter.
    let actlit = ActWrap { actlit: self.actlit, pred, unc, pos } ;
    self.actlit += 1 ;

    // Declare and assert.
    self.solver.declare_const(& actlit, & Typ::Bool, & ()) ? ;
    self.solver.assert( & actlit, & () ) ? ;

    let actlits = [actlit] ;

    if self.solver.check_sat_assuming(& actlits, & ()) ? {
      self.solver.assert( & actlits[0].as_ident(), & () ) ? ;
      profile!{ self mark "learning", "smt", "legal" }
      Ok(true)
    } else {
      self.solver.assert(
        & format!("(not {})", actlits[0].as_ident()), & ()
      ) ? ;
      profile!{ self mark "learning", "smt", "legal" }
      Ok(false)
    }
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
    let actlit = ActWrap { actlit: self.actlit, pred, unc, pos } ;
    self.actlit += 1 ;

    // Declare and assert.
    self.solver.declare_const(& actlit, & Typ::Bool, & ()) ? ;
    self.solver.assert( & actlit, & () ) ? ;

    let actlits = [actlit] ;

    if self.solver.check_sat_assuming(& actlits, & ()) ? {
      self.solver.assert( & actlits[0].as_ident(), & () ) ? ;
      profile!{ self mark "learning", "smt", "all legal" }
      Ok(true)
    } else {
      self.solver.assert(
        & format!("(not {})", actlits[0].as_ident()), & ()
      ) ? ;
      profile!{ self mark "learning", "smt", "all legal" }
      Ok(false)
    }
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
    self.actlit = 0 ;
    
    // Dummy arguments used in the `define_fun` for pos (neg) data.
    let args: [ (SWrap, Typ) ; 0 ] = [] ;

    // Positive data.
    self.solver.comment("Positive data:") ? ;
    for (pred, set) in self.data.pos.index_iter() {
      for sample in set.iter() {
        let is_new = self.dec_mem[pred].insert( sample.uid() ) ;
        debug_assert!(is_new) ;
        self.solver.define_fun(
          & SWrap(pred, sample), & args, & Typ::Bool, & "true", & ()
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
          & SWrap(pred, sample), & args, & Typ::Bool, & "false", & ()
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
              & SWrap(pred, sample), & Typ::Bool, & ()
            ) ?
          }
        }
      // }
    }

    self.solver.comment("Constraints:") ? ;
    // Assert all constraints.
    for constraint in self.data.constraints.iter() {
      if ! constraint.is_tautology() {
        self.solver.assert( & CWrap(constraint), & () ) ?
      }
    }
    profile!{ self mark "learning", "smt", "setup" }

    Ok(false)
  }


  /// Qualifier synthesis, fpice style.
  pub fn synthesize(
    & mut self, sample: & HSample
  ) -> () {
    let mut previous_int: Vec<(Term, & Int)> = Vec::with_capacity(
      sample.len()
    ) ;
    let mut previous_bool: Vec<(Term, bool)> = Vec::with_capacity(
      sample.len()
    ) ;

    for (var_idx, val) in sample.index_iter() {
      let arity: Arity = (1 + * var_idx).into() ;
      let var = term::var(var_idx) ;
      
      match * val {
        Val::B(val) => {
          let term = if val {
            var.clone()
          } else {
            term::not( var.clone() )
          } ;
          if ! self.qualifiers.is_known(arity, & term) {
            self.new_quals.insert( arity, term.clone() )
          }

          for & (ref pre_var, pre_val) in & previous_bool {
            let other_term = if pre_val {
              pre_var.clone()
            } else {
              term::not( pre_var.clone() )
            } ;
            let and = term::and( vec![ term.clone(), other_term.clone() ] ) ;
            if ! self.qualifiers.is_known(arity, & term) {
              self.new_quals.insert( arity, and )
            }

          }

          previous_bool.push( (var, val) )
        },
        
        Val::I(ref val) => {
          let val_term = term::int( val.clone() ) ;
          let term = term::app(
            Op::Ge, vec![ var.clone(), val_term.clone() ]
          ) ;
          if ! self.qualifiers.is_known(arity, & term) {
            self.new_quals.insert( arity, term )
          }
          let term = term::app( Op::Le, vec![ var.clone(), val_term ] ) ;
          if ! self.qualifiers.is_known(arity, & term) {
            self.new_quals.insert( arity, term )
          }

          for & (ref pre_var, pre_val) in & previous_int {
            if val == pre_val {
              let eq = term::eq( pre_var.clone(), var.clone() ) ;
              if ! self.qualifiers.is_known(arity, & eq) {
                self.new_quals.insert( arity, eq )
              }
            }
            if - val == * pre_val {
              let eq = term::eq(
                pre_var.clone(), term::not( var.clone() )
              ) ;
              if ! self.qualifiers.is_known(arity, & eq) {
                self.new_quals.insert( arity, eq )
              }
            }
            let add = term::app(
              Op::Add, vec![ pre_var.clone(), var.clone() ]
            ) ;
            let add_val = term::int( pre_val + val ) ;
            let term = term::app(
              Op::Ge, vec![ add.clone(), add_val.clone() ]
            ) ;
            if ! self.qualifiers.is_known(arity, & term) {
              self.new_quals.insert( arity, term )
            }
            let term = term::app( Op::Le, vec![ add, add_val ] ) ;
            if ! self.qualifiers.is_known(arity, & term) {
              self.new_quals.insert( arity, term )
            }
            let sub = term::app(
              Op::Sub, vec![ pre_var.clone(), var.clone() ]
            ) ;
            let sub_val = term::int( pre_val - val ) ;
            let term = term::app(
              Op::Ge, vec![ sub.clone(), sub_val.clone() ]
            ) ;
            if ! self.qualifiers.is_known(arity, & term) {
              self.new_quals.insert( arity, term )
            }
            let term = term::app( Op::Le, vec![ sub, sub_val ] ) ;
            if ! self.qualifiers.is_known(arity, & term) {
              self.new_quals.insert( arity, term )
            }
          }

          previous_int.push( (var, val) )
        },

        Val::N => continue,

      }

    }
  }


  /// Synthesizes a term representing a demi-space separating two points in an
  /// integer multidimensional space.
  ///
  /// Parameter `pos` indicates whether the demi-space should include `s_1`
  /// (`pos`) or not (`! pos`). The `solver` parameter should be the
  /// `synth_solver`. It is passed explicitely here (for now) for ownership
  /// reasons.
  ///
  /// The two points are given as
  /// [`HSample`s](../../common/data/type.HSample.html). These two points must
  /// come from the same signature, *i.e.* they are samples for the same
  /// predicate.
  ///
  /// # How it works
  ///
  /// If the two points have `n` integers in them, then the demi-space
  /// synthesized is of the form `c_1 * x_1 + ... + c_n * x_n + c >= 0`.
  ///
  /// It is constructed with the `synth_solver` in one `check-sat`.
  ///
  /// # Assumptions
  ///
  /// The two samples should be such that the vectors obtained by keeping only
  /// their integers composants are different.
  ///
  /// # TO DO
  ///
  /// - package the `synth_solver` with an instance and define `synthesize` on
  ///   that structure to avoid this ugly function (check no deadlock occurs)
  pub fn smt_synthesize(
    solver: & mut Slver, s_1: & HSample, pos: bool, s_2: & HSample
  ) -> Res<Term> {
    debug_assert!( s_1.len() == s_2.len() ) ;
    let mut p_1 = Vec::with_capacity( s_1.len() ) ;
    let mut p_2 = p_1.clone() ;
    let mut coefs = Vec::with_capacity( s_1.len() ) ;
    let mut coef: VarIdx = 0.into() ;

    for val in s_1.get() {
      if let Val::I(ref i) = * val {
        coefs.push(coef) ;
        p_1.push( i.clone() )
      }
      coef.inc()
    }
    for val in s_2.get() {
      if let Val::I(ref i) = * val {
        p_2.push( i.clone() )
      }
    }
    debug_assert!( p_1.len() == p_2.len() ) ;
    debug_assert!({
      let mut diff = false ;
      for (v_1, v_2) in p_1.iter().zip(& p_2) {
        diff = diff || (v_1 != v_2)
      }
      diff
    }) ;

    let cst = "v" ;

    let constraint_1 = ValCoefWrap::new(& p_1, & coefs, cst, pos) ;
    let constraint_2 = ValCoefWrap::new(& p_2, & coefs, cst, ! pos) ;

    solver.reset() ? ;
    // Declare coefs and constant.
    solver.declare_const(& cst, & Typ::Int, & ()) ? ;
    for coef in & coefs {
      solver.declare_const(coef, & Typ::Int, & ()) ?
    }
    solver.assert( & constraint_1, & () ) ? ;
    solver.assert( & constraint_2, & () ) ? ;

    let model = if solver.check_sat() ? {
      solver.get_model_const() ?
    } else {
      bail!("[unreachable] could not separate points {:?} and {:?}", p_1, p_2)
    } ;

    let mut sum = Vec::with_capacity( coefs.len() ) ;
    for (var_opt, (), val) in model {
      use num::Zero ;
      if ! val.is_zero() {
        let val = term::int(val) ;
        if let Some(var) = var_opt {
          let var = term::var(var) ;
          sum.push(
            term::app( Op::Mul, vec![val, var] )
          )
        } else {
          sum.push(val)
        }
      }
    }
    let lhs = term::app( Op::Add, sum ) ;
    let rhs = term::zero() ;

    let term = term::ge(lhs, rhs) ;
    // println!("synthesis: {}", term) ;

    Ok(term)
  }
}

impl<
  'core, 'kid, Slver: Solver<'kid, Parser>
> HasLearnerCore for IceLearner<'core, Slver> {
  fn core(& self) -> & LearnerCore { self.core }
}






/// A branch of a decision tree.
///
/// Boolean is `false` if the term should be negated.
pub type Branch = Vec<(Term, bool)> ;

/// Projected data to classify.
#[derive(Clone)]
pub struct CData {
  /// Positive samples.
  pub pos: HSamples,
  /// Negative samples.
  pub neg: HSamples,
  /// Unclassified samples.
  pub unc: HSamples,
}
impl CData {

  /// Shannon entropy given the number of positive and negative samples.
  fn shannon_entropy(pos: f64, neg: f64) -> f64 {
    if pos == 0. && neg == 0. { return 1. }
    // println!("| pos: {}, neg: {}", pos, neg) ;
    let den = pos + neg ;
    // println!("| den: {}", den) ;
    let (pos, neg) = (pos / den, neg / den) ;
    // println!("| /den: (pos: {}, neg: {})", pos, neg) ;
    let (pos, neg) = (
      if pos <= 0. { 0. } else { - ( pos * pos.log2() ) },
      if neg <= 0. { 0. } else { - ( neg * neg.log2() ) }
    ) ;
    // println!("| final: (pos: {}, neg: {})", pos, neg) ;
    pos + neg
  }

  /// Shannon-entropy-based information gain of a qualifier (simple, ignores
  /// unclassified data).
  pub fn simple_gain(& self, qual: & mut QualValues) -> Option<f64> {
    // println!("my entropy") ;
    let my_entropy = Self::shannon_entropy(
      self.pos.len() as f64, self.neg.len() as f64
    ) ;
    let card = (self.pos.len() as f64) + (self.neg.len() as f64) ;
    let (
      mut q_pos, mut q_neg, mut q_unc, mut nq_pos, mut nq_neg, mut nq_unc
    ) = (0., 0., 0., 0., 0., 0.) ;
    for pos in & self.pos {
      match qual.eval(pos) {
        Some(true) => q_pos += 1.,
        Some(false) => nq_pos += 1.,
        None => return None,
      }
    }
    for neg in & self.neg {
      match qual.eval(neg) {
        Some(true) => q_neg += 1.,
        Some(false) => nq_neg += 1.,
        None => return None,
      }
    }
    for unc in & self.unc {
      match qual.eval(unc) {
        Some(true) => q_unc += 1.,
        Some(false) => nq_unc += 1.,
        None => return None,
      }
    }
    if q_pos + q_neg + q_unc == 0. || nq_pos + nq_neg + nq_unc == 0. {
      None
    } else {
      let (q_entropy, nq_entropy) = (
        Self::shannon_entropy( q_pos,  q_neg),
        Self::shannon_entropy(nq_pos, nq_neg)
      ) ;
      // println!("{} | q: {}, nq: {}", my_entropy, q_entropy, nq_entropy) ;
      Some(
        my_entropy - (
          ( (q_pos + q_neg) *  q_entropy / card ) +
          ( (nq_pos + nq_neg) * nq_entropy / card )
        )
      )
    }
  }


  /// Modified entropy, uses [`EntropyBuilder`](struct.EntropyBuilder.html).
  pub fn entropy(& self, pred: PrdIdx, data: & Data) -> Res<f64> {
    let mut proba = EntropyBuilder::new() ;
    proba.set_pos_count( self.pos.len() ) ;
    proba.set_neg_count( self.neg.len() ) ;
    for unc in & self.unc {
      proba.add_unc(data, pred, unc) ?
    }
    Ok( proba.entropy() )
  }

  /// Modified gain, uses `entropy`.
  pub fn gain(
    & self, pred: PrdIdx, data: & Data, qual: & mut QualValues
  ) -> Res< Option< (f64, (f64, f64, f64), (f64, f64, f64) ) > > {
    let my_entropy = self.entropy(pred, data) ? ;
    let my_card = (
      self.pos.len() + self.neg.len() + self.unc.len()
    ) as f64 ;
    let (mut q_ent, mut nq_ent) = (
      EntropyBuilder::new(), EntropyBuilder::new()
    ) ;
    let (
      mut q_pos, mut q_neg, mut q_unc, mut nq_pos, mut nq_neg, mut nq_unc
    ) = (0, 0, 0., 0, 0, 0.) ;
    for pos in & self.pos {
      match qual.eval(pos) {
        Some(true) => q_pos += 1,
        Some(false) => nq_pos += 1,
        None => return Ok(None),
      }
    }
    q_ent.set_pos_count(q_pos) ;
    nq_ent.set_pos_count(nq_pos) ;

    for neg in & self.neg {
      match qual.eval(neg) {
        Some(true) => q_neg += 1,
        Some(false) => nq_neg += 1,
        None => return Ok(None),
      }
    }
    q_ent.set_neg_count(q_neg) ;
    nq_ent.set_neg_count(nq_neg) ;

    for unc in & self.unc {
      match qual.eval(unc) {
        Some(true) => {
          q_unc += 1. ;
          q_ent.add_unc(data, pred, unc) ?
        },
        Some(false) => {
          nq_unc += 1. ;
          nq_ent.add_unc(data, pred, unc) ?
        },
        None => return Ok(None),
      }
    }
    
    let (q_pos, q_neg, nq_pos, nq_neg) = (
      q_pos as f64, q_neg as f64, nq_pos as f64, nq_neg as f64
    ) ;

    // Is this qualifier separating anything?
    if q_pos + q_neg + q_unc == 0.
    || nq_pos + nq_neg + nq_unc == 0. {
      return Ok(None)
    }

    // let (q_proba, nq_proba) = (q_ent.proba(), nq_ent.proba()) ;
    let (q_entropy, nq_entropy) = (q_ent.entropy(), nq_ent.entropy()) ;

    // if my_entropy.is_nan() {
    //   println!("data entropy is nan...")
    // }
    // println!(
    //   "q entropy: {} ({},{},{} -> {})",
    //   q_entropy, q_pos, q_neg, q_unc, q_proba
    // ) ;
    // println!(
    //   "nq entropy: {} ({},{},{} -> {})",
    //   nq_entropy, nq_pos, nq_neg, nq_unc, nq_proba
    // ) ;

    let gain = my_entropy - (
      (q_pos + q_neg + q_unc) * q_entropy / my_card +
      (nq_pos + nq_neg + nq_unc) * nq_entropy / my_card
    ) ;
    // println!("gain: {}", gain) ;
    // println!("") ;

    Ok( Some( (gain, (q_pos, q_neg, q_unc), (nq_pos, nq_neg, nq_unc)) ) )
  }

  /// Splits the data given some qualifier. First is the data for which the
  /// qualifier is true.
  pub fn split(self, qual: & mut QualValues) -> (Self, Self) {
    let (mut q, mut nq) = (
      CData {
        pos: Vec::with_capacity( self.pos.len() ),
        neg: Vec::with_capacity( self.neg.len() ),
        unc: Vec::with_capacity( self.unc.len() ),
      },
      CData {
        pos: Vec::with_capacity( self.pos.len() ),
        neg: Vec::with_capacity( self.neg.len() ),
        unc: Vec::with_capacity( self.unc.len() ),
      }
    ) ;

    for pos in self.pos {
      if qual.eval(& pos).expect("error evaluating qualifier") {
        q.pos.push( pos )
      } else {
        nq.pos.push( pos )
      }
    }
    for neg in self.neg {
      if qual.eval(& neg).expect("error evaluating qualifier") {
        q.neg.push( neg )
      } else {
        nq.neg.push( neg )
      }
    }
    for unc in self.unc {
      if qual.eval(& unc).expect("error evaluating qualifier") {
        q.unc.push( unc )
      } else {
        nq.unc.push( unc )
      }
    }

    q.pos.shrink_to_fit() ;
    q.neg.shrink_to_fit() ;
    q.unc.shrink_to_fit() ;
    nq.pos.shrink_to_fit() ;
    nq.neg.shrink_to_fit() ;
    nq.unc.shrink_to_fit() ;

    (q, nq)
  }
}



/// Wrapper around an `f64` used to compute an approximation of the ratio
/// between legal positive classifications and negative ones, without actually
/// splitting the data.
///
/// See the paper for more details.
pub struct EntropyBuilder { num: f64, den: usize }
impl EntropyBuilder {
  /// Constructor.
  pub fn new() -> Self {
    EntropyBuilder { num: 0., den: 0 }
  }

  /// Sets the number of positive samples.
  pub fn set_pos_count(& mut self, pos: usize) {
    self.num += pos as f64 ;
    self.den += pos
  }
  /// Sets the number of negative samples.
  pub fn set_neg_count(& mut self, neg: usize) {
    self.den += neg
  }

  /// Adds the degree of an unclassified example.
  pub fn add_unc(
    & mut self, data: & Data, prd: PrdIdx, sample: & HSample
  ) -> Res<()> {
    self.den += 1 ;
    self.num += (1. / 2.) + (
      Self::degree(data, prd, sample) ? / ::std::f64::consts::PI
    ).atan() ;
    Ok(())
  }

  /// Probability stored in the builder.
  pub fn proba(& self) -> f64 {
    self.num / (self.den as f64)
  }

  /// Destroys the builder and returns the entropy.
  pub fn entropy(self) -> f64 {
    let proba = self.proba() ;
    let (pos, neg) = (
      if proba == 0. { 0. } else {
        proba * proba.log2()
      },
      if proba == 1. { 0. } else {
        (1. - proba) * (1. - proba).log2()
      }
    ) ;
    - pos - neg
  }

  /// Degree of a sample, refer to the paper for details.
  pub fn degree(
    data: & Data, prd: PrdIdx, sample: & HSample
  ) -> Res<f64> {
    let (
      mut sum_imp_rhs,
      mut sum_imp_lhs,
      mut sum_neg,
    ) = (0., 0., 0.) ;

    if let Some(constraints) = data.map[prd].get(& sample) {
      for constraint in constraints {
        let constraint = & data.constraints[* constraint] ;
        match constraint.rhs {
          None => sum_neg = sum_neg + 1. / (constraint.lhs.len() as f64),
          Some( Sample { pred, ref args } )
          if pred == prd
          && args == sample => sum_imp_rhs = sum_imp_rhs + 1. / (
            1. + (constraint.lhs.len() as f64)
          ),
          _ => {
            debug_assert!(
              constraint.lhs.iter().fold(
                false,
                |b, & Sample { pred, ref args }|
                  b || ( pred == prd && args == sample )
              )
            ) ;
            sum_imp_lhs = sum_imp_lhs + 1. / (
              1. + (constraint.lhs.len() as f64)
            )
          },
        }
      }
    }

    Ok(sum_imp_rhs - sum_imp_lhs - sum_neg)
  }
}








/// Smt-related things.
pub mod smt {
  use std::str::FromStr ;
  use std::io::BufRead ;

  use rsmt2::parse::{ IdentParser, ValueParser, SmtParser } ;
  use rsmt2::to_smt::* ;

  use common::* ;
  use common::data::* ;



  /// Can parse values (int) and idents (`VarIdx`).
  ///
  /// In the ice learner, parsing is only used for synthesizing, not for
  /// conflict detection.
  #[derive(Clone, Copy)]
  pub struct Parser ;

  impl<'a> IdentParser<'a, Option<VarIdx>, (), & 'a str> for Parser {
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

  impl<'a, Br> ValueParser<'a, Int, & 'a mut SmtParser<Br>> for Parser
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
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      write!( w, "|p_{} {}|", self.0, self.1.uid() ) ? ;
      Ok(())
    }
  }
  impl<'a> Sym2Smt<()> for SWrap<'a> {
    fn sym_to_smt2<Writer>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> where Writer: Write {
      self.expr_to_smt2(w, & ())
    }
  }


  /// Wrapper around constraints that forces smt printing consistent with
  /// [`SWrap`](struct.SWrap.html).
  pub struct CWrap<'a>(pub & 'a Constraint) ;
  impl<'a> Expr2Smt<()> for CWrap<'a> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      write!(w, "(=> (and") ? ;
      for lhs in & self.0.lhs {
        write!(w, " ", ) ? ;
        SWrap(lhs.pred, & lhs.args).expr_to_smt2(w, & ()) ?
      }
      write!(w, ") ") ? ;
      if let Some(rhs) = self.0.rhs.as_ref() {
        SWrap(rhs.pred, & rhs.args).expr_to_smt2(w, & ()) ?
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
    /// Actlit counter.
    pub actlit: usize,
    /// Predicate.
    pub pred: PrdIdx,
    /// Samples.
    pub unc: Samples,
    /// Indicates whether we're assuming the samples positive or negative.
    pub pos: bool,
  }
  impl<Samples> ActWrap<Samples> {
    /// Identifier representation of the actlit.
    pub fn as_ident(& self) -> String {
      format!("act_{}", self.actlit)
    }
  }
  impl<'a> Expr2Smt<()> for ActWrap<& 'a HSamples> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      write!(
        w, "(=> act_{} ({}", self.actlit,
        if self.pos { "and" } else { "not (or" }
      ) ? ;
      for unc in self.unc {
        write!(w, " ", ) ? ;
        SWrap(self.pred, unc).expr_to_smt2(w, & ()) ?
      }
      write!(w, "))") ? ;
      if ! self.pos {
        write!(w, ")") ?
      }
      Ok(())
    }
  }
  impl<'a, T> Expr2Smt<()> for ActWrap<
    & 'a HConMap<Args, T>
  > {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      write!(
        w, "(=> act_{} ({}", self.actlit,
        if self.pos { "and" } else { "not (or" }
      ) ? ;
      for (unc, _) in self.unc {
        write!(w, " ", ) ? ;
        SWrap(self.pred, unc).expr_to_smt2(w, & ()) ?
      }
      write!(w, "))") ? ;
      if ! self.pos {
        write!(w, ")") ?
      }
      Ok(())
    }
  }
  impl<Samples> Sym2Smt<()> for ActWrap<Samples> {
    fn sym_to_smt2<Writer>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> where Writer: Write {
      write!(w, "act_{}", self.actlit) ? ;
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
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> where Writer: Write {
      if self.pos { write!(w, "(>= (+") } else { write!(w, "(< (+") } ? ;
      for (val, coef) in self.vals.iter().zip( self.coefs ) {
        write!(w, " (* {} ", val) ? ;
        coef.sym_to_smt2(w, & ()) ? ;
        write!(w, ")") ?
      }
      write!(w, " {}) 0)", self.cst) ? ;
      Ok(())
    }
  }
}






mod svm {



  /// SVM types.
  use rustlearn::svm::libsvm::svc::* ;
  use rustlearn::prelude::* ;

  use common::* ;
  use common::data::* ;



  /// Data used by SVM synthesis (avoids re-allocations).
  pub struct SvmSynth {
    /// Maps SVM variables to predicate variables.
    var_map: Vec<VarIdx>,
  }
  impl SvmSynth {
    /// Constructor.
    pub fn new() -> SvmSynth {
      SvmSynth {
        var_map: Vec::with_capacity(17),
      }
    }
    /// SVM-based qualifier synthesis.
    ///
    /// Returns the left-hand side (the sum part) of the hyperplan `a + a_1 *
    /// v_1 + ... + a_n * v_n = 0` separating `pos` from `neg`.
    ///
    /// **NB**: automatically returns `None` if `pos.len() < 3 || neg.len() <
    /// 3`. This is because in these cases, we consider there's not enough
    /// samples for the result to be interesting.
    pub fn synthesize(
      & mut self, pred_sig: & VarMap<Typ>, pos: & HSamples, neg: & HSamples
    ) -> Res< Option<Term> > {
      if pos.is_empty() || neg.is_empty() || pos.len() + neg.len() < 5 {
        // println!("  not enough data ({}/{})", pos.len(), neg.len()) ;
        return Ok(None)
      }
      self.var_map.clear() ;

      // All `f32` values will be multiplied by this coefficient.
      let correction = 1_000_000f32 ;

      // println!("  populating var_map...") ;

      // Populate `var_map`.
      for (var, typ) in pred_sig.index_iter() {
        if let Typ::Int = * typ {
          self.var_map.push(var)
        }
      }

      // println!("  creating svm...") ;

      // Create svm.
      let mut params = Hyperparameters::new(
        self.var_map.len(), KernelType::Linear, 2
      ) ;
      params.C(0.1) ;
      let mut svm = params.build() ;

      let mut data = Vec::with_capacity( pos.len() + neg.len() ) ;
      let mut target = Vec::with_capacity( pos.len() + neg.len() ) ;

      use num::ToPrimitive ;

      // println!("  pos ({})...", pos.len()) ;

      for pos in pos {
        let mut these_vals = Vec::with_capacity( self.var_map.len() ) ;
        for (var, val) in pos.index_iter() {
          if let Typ::Int = pred_sig[var] {
            match * val {
              Val::N => these_vals.push(0f32),
              Val::I(ref i) => if let Some(float) = i.to_f32() {
                these_vals.push(float)
              } else {
                // println!("  conversion to f32 failed") ;
                return Ok(None)
              },
              Val::B(_) => bail!("ill-typed learning data")
            }
          }
        }
        debug_assert_eq!( these_vals.len(), self.var_map.len() ) ;
        data.push(these_vals) ;
        target.push(0.)
      }

      // println!("  neg ({})...", neg.len()) ;

      for neg in neg {
        let mut these_vals = Vec::with_capacity( self.var_map.len() ) ;
        for (var, val) in neg.index_iter() {
          if let Typ::Int = pred_sig[var] {
            match * val {
              Val::N => these_vals.push(0f32),
              Val::I(ref i) => if let Some(float) = i.to_f32() {
                these_vals.push(float)
              } else {
                // println!("  conversion to f32 failed") ;
                return Ok(None)
              },
              Val::B(_) => bail!("ill-typed learning data")
            }
          }
        }
        debug_assert_eq!( these_vals.len(), self.var_map.len() ) ;
        data.push(these_vals) ;
        target.push(1.)
      }

      let data: Array = (& data).into() ;
      let target: Array = target.into() ;

      // println!("  learning...") ;

      // Learn...
      svm.fit(& data, & target).map_err(
        |e| format!("error during svm learning:\n{}", e)
      ) ? ;

      // Retrieve decision function.
      // `a + a_1 * v_1 + ... + a_n * v_n = 0`
      let mut sum = Vec::with_capacity( self.var_map.len() + 1 ) ;

      // First, retrieve `a`.
      // println!("  retrieving `a`...") ;
      let mut array = Array::zeros( 1, self.var_map.len() ) ;
      let res = svm.decision_function(& array).map_err(
        |e| format!("error retrieving svm decision function (1):\n{}", e)
      ) ? ;
      let slice = res.as_slice() ;
      debug_assert_eq!(slice.len(), 1) ;
      let coef_f32 = slice[0] * correction ;
      let constant = if let Some(coef) = to_i64( coef_f32 ) {
        sum.push( term::int(coef.clone()) ) ;
        // println!("  - {} ({})", coef, coef_f32) ;
        coef_f32
      } else {
        // println!("  conversion to int failed: a = {}", coef_f32) ;
        return Ok(None)
      } ;

      // Then retrieve all the other coefs.
      //
      // This is done by asking `svm` the value of the `a + a_1 * v_1 + ...`
      // for `(1, 0, 0, ...)` to retrieve `a_1`, `(0, 1, 0, 0, ...)` to
      // retrieve `a_2` *etc.*
      //
      // This yields `a_1 + a`, and we correct by `constant` (`a`) each time.
      let mut prev = None ;
      for n in 0..self.var_map.len() {
        // println!("  retrieving `a_{}` (v_{})...", n, self.var_map[n]) ;
        if let Some(prev) = prev {
          debug_assert_eq!( array.get(0, prev), 1f32 ) ;
          * array.get_mut(0, prev) = 0f32
        }
        prev = Some(n) ;
        debug_assert_eq!( array.get(0, n), 0f32 ) ;
        * array.get_mut(0, n) = 1f32 ;
        let res = svm.decision_function(& array).map_err(
          |e| format!("error retrieving svm decision function (2):\n{}", e)
        ) ? ;
        let slice = res.as_slice() ;
        debug_assert_eq!(slice.len(), 1) ;
        let coef_f32 = slice[0] * correction - constant ;
        if let Some(coef) = to_i64( coef_f32 ) {
          // println!("  - {} ({}, {})", coef, slice[0] * correction, coef_f32) ;
          if let Some(1) = coef.to_isize() {
            sum.push(
              term::var(* self.var_map[n])
            )
          } else if ! coef.is_zero() {
            sum.push(
              term::mul(
                vec![ term::int(coef), term::var(* self.var_map[n]) ]
              )
            )
          }
        } else {
        // println!(
        //   "  conversion to int failed: a + a_{} = {} (v_{})",
        //   n, slice[0], self.var_map[n]
        // ) ;
          return Ok(None)
        }
      }

      Ok( Some(term::add(sum)) )
    }
  }

  /// Tries to convert an `f32` to an `Int`, `None` if `f32` is not an integer.
  fn to_i64(float: f32) -> Option<Int> {
    use num::FromPrimitive ;
    let res = float as i64 ;
    if let Some(res) = Int::from_i64(res) {
      Some(res)
    } else {
      None
    }
  }


}
//! ICE learner.

use common::* ;
use common::data::Data ;
use common::msg::* ;
use common::smt::{
  SmtSample, SmtConstraint, SmtActSamples
} ;

pub mod quals ;
pub mod synth ;
pub mod data ;

use self::quals::NuQuals ;
use self::data::CData ;


/// Launcher.
pub struct Launcher ;
unsafe impl Sync for Launcher {}
unsafe impl Send for Launcher {}

impl Launcher {
  /// Launches an smt learner.
  pub fn launch(
    core: & MsgCore, instance: Arc<Instance>, data: Data, mine: bool
  ) -> Res<()> {

    let mut learner = IceLearner::new(
      & core, instance, data, mine
    ).chain_err(
      || "while creating ice learner"
    ) ? ;
    let res = learner.run() ;
    learner.finalize() ? ;
    res
  }
}
impl Learner for Launcher {
  fn run(
    & self, core: MsgCore,
    instance: Arc<Instance>, data: Data,
    mine: bool
  ) {
    match Self::launch(& core, instance, data, mine) {
      Ok(()) => core.exit(),
      Err(e) => core.err(e),
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
pub struct IceLearner<'core> {
  /// Arc to the instance.
  pub instance: Arc<Instance>,
  /// Qualifiers for the predicates.
  pub qualifiers: NuQuals,
  /// Current data.
  data: Data,
  /// Solver used to check if the constraints are respected.
  solver: Solver<()>,
  /// Learner core.
  core: & 'core MsgCore,
  /// Branches of the tree, used when constructing a decision tree.
  finished: Vec<Branch>,
  /// Branches to construct later, used when constructing a decision tree.
  unfinished: Vec< (Branch, CData) >,
  /// Classifier for constraint data.
  classifier: ArgsMap<bool>,
  /// Declaration memory: used when declaring samples in the solver to
  /// remember what's already declared. The `u64` is the sample's uid.
  dec_mem: PrdMap< HashSet<u64> >,
  /// Current candidate, cleared at the beginning of each learning phase.
  candidate: PrdMap< Option<Term> >,
  /// Vector used during learning, avoids re-allocation.
  predicates: Vec<(usize, usize, PrdIdx)>,
  /// Rng to decide when to sort predicates.
  sort_rng_1: ::rand::StdRng,
  /// Rng actually doing the predicate sorting.
  sort_rng_2: ::rand::StdRng,
  /// Rng to decide when to use simple gain.
  simple_rng: ::rand::StdRng,
  /// Rng to decide when skip preliminary.
  pre_skip_rng: ::rand::StdRng,
  /// Luby counter for restarts.
  luby: Option<LubyCount>,
  /// Known qualifiers, factored for no reallocation. Used by synthesis.
  known_quals: HConSet<Term>,
  /// Gain pivot.
  gain_pivot: f64,
  /// Gain pivot synth.
  gain_pivot_synth: Option<f64>,
  /// Learn step counter.
  count: usize,
}
impl<'core> IceLearner<'core> {

  /// Ice learner constructor.
  pub fn new(
    core: & 'core MsgCore, instance: Arc<Instance>, data: Data,
    mine: bool// synth_solver: Slver
  ) -> Res<Self> {
    let solver = conf.solver.spawn(
      "ice_learner", (), & instance
    ) ? ;

    profile!{ |core._profiler| tick "mining" }
    let qualifiers = NuQuals::new( instance.clone(), mine ).chain_err(
      || "while creating qualifier structure"
    ) ? ;
    profile!{ |core._profiler| mark "mining" }
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
        classifier: HConMap::with_capacity(1003),
        dec_mem, candidate, predicates,
        sort_rng_1: {
          use rand::SeedableRng ;
          ::rand::StdRng::from_seed(& [ 42 ])
        },
        sort_rng_2: {
          use rand::SeedableRng ;
          ::rand::StdRng::from_seed(& [ 79 ])
        },
        simple_rng: {
          use rand::SeedableRng ;
          ::rand::StdRng::from_seed(& [ 107 ])
        },
        pre_skip_rng: {
          use rand::SeedableRng ;
          ::rand::StdRng::from_seed(& [ 666 ])
        },
        luby: if mine { None } else {
          Some( LubyCount::new() )
        },
        known_quals: HConSet::new(),
        gain_pivot: conf.ice.gain_pivot,
        gain_pivot_synth: conf.ice.gain_pivot_synth,
        count: 0,
      }
    )
  }

  /// Returns true if all qualifiers should be wiped out.
  pub fn restart(& mut self) -> bool {
    self.luby.as_mut().map( |l| l.inc() ).unwrap_or(false)
  }

  /// Runs the learner.
  pub fn run(& mut self) -> Res<()> {
    profile!{ self "quals synthesized" => add 0 }
    profile!{
      self "quals initially" =>
        add self.qualifiers.real_qual_count()
    }

    'learn: loop {

      match profile! (
        |self.core._profiler| wrap { self.recv() } "waiting"
      ) {
        Ok(data) => {
          self.count += 1 ;
          if self.count % 50 == 0 {
            self.solver.reset() ?
          }
          profile! { self "learn steps" => add 1 }
          if let Some(candidates) = profile!(
            |self.core._profiler| wrap {
              self.solver.push(1) ? ;
              let res = self.learn(data) ;
              self.solver.pop(1) ? ;
              res
            } "learning"
          ) ? {
            self.send_cands(candidates).chain_err(
              || "while sending candidates"
            ) ? ;
            if self.restart() {
              profile! { self "restarts" => add 1 }
              self.qualifiers.wipe()
            }
          } else {
            return Ok(())
          }
        },
        Err(e) => bail!(e),
      }

    }
  }

  /// Finalizes the learning process and exits.
  #[cfg( not(feature = "bench") )]
  pub fn finalize(mut self) -> Res<()> {
    self.solver.kill() ? ;
    profile! {
      self "quals once done" => add self.qualifiers.real_qual_count()
    }
    Ok(())
  }
  #[cfg(feature = "bench")]
  pub fn finalize(mut self) -> Res<()> {
    self.solver.kill() ? ;
    Ok(())
  }

  /// Sends some candidates.
  ///
  /// Also resets the solver and clears declaration memory.
  pub fn send_cands(& mut self, candidates: Candidates) -> Res<()> {
    profile!(
      | self._profiler | wrap {
        self.send_candidates(
          candidates
        )
      } "sending"
    ) ? ;
    // // Reset and clear declaration memory.
    // self.solver.reset().chain_err(
    //   || "during solver reset"
    // ) ? ;
    for set in self.dec_mem.iter_mut() {
      set.clear()
    } ;
    Ok(())
  }

  /// Looks for a classifier.
  ///
  /// Returns `None` if asked to exit.
  pub fn learn(
    & mut self, mut data: Data
  ) -> Res< Option<Candidates> > {
    use rand::Rng ;

    ::std::mem::swap(& mut data, & mut self.data) ;
    self.core.merge_prof( "data", data.destroy() ) ;

    if self.count % conf.ice.gain_pivot_mod == 0 {
      self.gain_pivot = self.gain_pivot + conf.ice.gain_pivot_inc ;
      if self.gain_pivot > 1.0 {
        self.gain_pivot = 1.0
      }
      if let Some(gain_pivot_synth) = self.gain_pivot_synth.as_mut() {
        * gain_pivot_synth = * gain_pivot_synth + conf.ice.gain_pivot_inc ;
        if * gain_pivot_synth > 1.0 {
          * gain_pivot_synth = 1.0
        }
      }
    }

    if conf.ice.qual_print {
      self.qualifiers.log()
    }

    let contradiction = profile!(
      |self.core._profiler| wrap {
        self.setup_solver().chain_err(
          || "while initializing the solver"
        )
      } "learning", "setup"
    ) ? ;

    if contradiction {
      unsat!("by contradiction in ICE solver")
    }

    self.check_exit() ? ;

    let prd_count = self.instance.preds().len() ;
    debug_assert!{
      scoped! {
        let mut okay = true ;
        for term_opt in & self.candidate {
          okay = okay && term_opt.is_none() ;
        }
        okay
      }
    }

    // Decide whether to use simple gain.
    let simple = self.simple_rng.next_f64() <= conf.ice.simple_gain_ratio ;
    // Decide whether to sort the predicates.
    let sorted = self.sort_rng_1.next_f64() <= conf.ice.sort_preds ;
    // Skip preliminary decision 20% of the time.
    let skip_prelim = self.pre_skip_rng.next_f64() <= 0.20 ;

    msg! { @verb
      self =>
      "starting learning\n  \
      simple:      {},\n  \
      sorted:      {},\n  \
      skip_prelim: {},",
      simple, sorted, skip_prelim
    }

    // Stores `(<unclassified_count>, <classified_count>, <prd_index>)`
    debug_assert! { self.predicates.is_empty() }

    let mut all_preds: Vec<_> = PrdRange::zero_to(prd_count).filter_map(
      |pred| if self.instance.is_known(pred) {
        None
      } else {
        Some(pred)
      }
    ).collect() ;

    if sorted {
      all_preds.sort_unstable_by(
        |p_1, p_2| {
          let sum_1 = self.data.pos[* p_1].len() + self.data.neg[* p_1].len() ;
          let unc_1 = self.data.map()[* p_1].len() ;
          let sum_1 = sum_1 - ::std::cmp::min(
            sum_1, unc_1
          ) ;

          let sum_2 = self.data.pos[* p_2].len() + self.data.neg[* p_2].len() ;
          let unc_2 = self.data.map()[* p_2].len() ;
          let sum_2 = sum_2 - ::std::cmp::min(
            sum_2, unc_2
          ) ;

          sum_1.cmp(& sum_2).reverse()
        }
      )
    }

    for pred in all_preds {

      if self.instance.is_known(pred) {
        continue
      }

      let pos_len = self.data.pos[pred].len() ;
      let neg_len = self.data.neg[pred].len() ;
      let unc_len = self.data.map()[pred].len() ;

      if ! skip_prelim {

        if pos_len == 0 && neg_len > 0 {
          msg! { debug self => "legal_pred (1)" }
          // Maybe we can assert everything as negative right away?
          if self.is_legal_pred(pred, false) ? {
            msg! { @verb
              self =>
              "{} only has negative ({}) and unclassified ({}) data\n\
              legal check ok, assuming everything negative",
              self.instance[pred], neg_len, unc_len
            }
            self.candidate[pred] = Some( term::fls() ) ;
            profile!(
              |self.core._profiler| wrap {
                self.data.force_pred(pred, false).chain_err(
                  || format!(
                    "while setting all false for {}", self.instance[pred]
                  )
                )
              } "learning", "data"
            ) ? ;
            continue
          }
        }

        if neg_len == 0 && pos_len > 0 {
          msg! { debug self => "legal_pred (2)" }
          // Maybe we can assert everything as positive right away?
          if self.is_legal_pred(pred, true) ? {
            msg! { @verb
              self =>
              "{} only has positive ({}) and unclassified ({}) data\n\
              legal check ok, assuming everything positive",
              self.instance[pred], pos_len, unc_len
            }
            self.candidate[pred] = Some( term::tru() ) ;
            profile!(
              |self.core._profiler| wrap {
                self.data.force_pred(pred, true).chain_err(
                  || format!(
                    "while setting all true for {}", self.instance[pred]
                  )
                )
              } "learning", "data"
            ) ? ;
            continue
          }
        }

      }

      self.predicates.push((
        unc_len, pos_len + neg_len, pred
      ))
    }

    self.check_exit() ? ;

    if simple {
      profile! { self "simple" => add 1 }
    }

    if sorted {

      profile!{ self tick "learning", "predicate sorting" }

      // The iteration starts from the end of `predicates`. The first
      // predicates we want to synthesize should be last.
      self.predicates.sort_unstable_by(
        |
          & (
            unc_1, cla_1, _p_1
          ), & (
            unc_2, cla_2, _p_2
          )
        | {
          use std::cmp::Ordering::* ;
          match cla_1.cmp(& cla_2) {
            // Same amount of classified data, we want the one with fewer
            // unclassifieds last.
            Equal => unc_1.cmp(& unc_2).reverse(),
            // Otherwise we want the one with the most classified data last.
            cmp => cmp,
          }
        }
      ) ;
      profile!{ self mark "learning", "predicate sorting" }

    } else {

      // Not sorting, forcing random order.
      profile!{ self tick "learning", "predicate sorting" }
      let mut sort_rng = self.sort_rng_2 ;
      self.predicates.sort_unstable_by(
        |_, _| {
          use std::cmp::Ordering::* ;
          let rand = sort_rng.next_f64() ;
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

    self.check_exit() ? ;

    'pred_iter: while let Some(
      (_unc, _cla, pred)
    ) = self.predicates.pop() {
      msg! {
        debug self =>
        "{}: {} unclassified, {} classified",
        self.instance[pred], _unc, _cla
      }

      let data = profile!(
        |self.core._profiler| wrap {
          self.data.data_of(pred)
        } "learning", "data"
      ) ;
      self.check_exit() ? ;
      
      if let Some(term) = self.pred_learn(
        pred, data, simple
      ) ? {
        self.candidate[pred] = Some(term)
      } else {
        return Ok(None)
      }
      self.check_exit() ? ;
    }
    let mut candidates: PrdMap<_> = vec![
      None ; self.instance.preds().len()
    ].into() ;

    ::std::mem::swap(
      & mut candidates, & mut self.candidate
    ) ;

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

    // Backtracking or exit loop.
    let res = if let Some( (nu_branch, mut nu_data) ) = self.unfinished.pop() {
      // Update data, some previously unclassified data may be classified now.
      self.data.classify(pred, & mut nu_data) ;
      Some( (nu_branch, nu_data) )
    } else { None } ;

    profile!{ self mark "learning", "backtrack" }

    res
  }

  /// Looks for a classifier for a given predicate.
  pub fn pred_learn(
    & mut self, pred: PrdIdx, mut data: CData, simple: bool
  ) -> Res< Option<Term> > {
    debug_assert!( self.finished.is_empty() ) ;
    debug_assert!( self.unfinished.is_empty() ) ;
    self.classifier.clear() ;

    msg! { @verb
      self =>
      "working on predicate {} (pos: {}, neg: {}, unc: {})",
      self.instance[pred], data.pos().len(), data.neg().len(), data.unc().len()
    }

    let mut branch = Vec::with_capacity(17) ;

    'learning: loop {
      self.check_exit() ? ;

      // Checking whether we can close this branch.

      if data.neg().is_empty() && self.is_legal(
        pred, data.unc(), true
      ).chain_err(|| "while checking possibility of assuming positive") ? {
        if_verb! {
          let mut s = format!(
            "  no more negative data, is_legal check ok\n  \
            forcing {} unclassifieds positive...", data.unc().len()
          ) ;
          if_debug! {
            for unc in data.unc() {
              s = format!("{}\n  {}", s, unc)
            }
          }
          msg! { self => s }
        }

        let (_, _, unc) = data.destroy() ;

        profile!(
          |self.core._profiler| wrap {
            for unc in unc {
              self.data.add_pos_untracked(pred, unc) ;
            }
            self.data.propagate()
          } "learning", "data"
        ) ? ;

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

      if data.pos().is_empty() && self.is_legal(
        pred, & data.unc(), false
      ).chain_err(|| "while checking possibility of assuming negative") ? {
        if_verb! {
          let mut s = format!(
            "  no more positive data, is_legal check ok\n  \
            forcing {} unclassifieds negative...", data.unc().len()
          ) ;
          if_debug! {
            for unc in data.unc() {
              s = format!("{}\n  {}", s, unc)
            }
          }
          msg! { self => s }
        }

        let (_, _, unc) = data.destroy() ;

        profile!(
          |self.core._profiler| wrap {
            for unc in unc {
              self.data.add_neg_untracked(pred, unc) ;
            }
            self.data.propagate()
          } "learning", "data"
        ) ? ;

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

      self.check_exit() ? ;

      // Could not close the branch, look for a qualifier.
      profile!{ self tick "learning", "qual" }
      let res = self.get_qualifier(
        pred, data, simple
      ) ;
      profile!{ self mark "learning", "qual" }
      let (qual, q_data, nq_data) = if let Some(res) = res ? {
        res
      } else {
        return Ok(None)
      } ;

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
        let term = if pos {
          term
        } else {
          term::not(term)
        } ;
        and_args.push(term)
      }
      or_args.push( term::and(and_args) )
    }
    profile!{ self mark "learning", "pred finalize" }
    Ok(
      Some( term::or(or_args) )
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
  ) -> Res< Option< (Term, CData, CData) > > {
    let simple = data.unc().is_empty() || (
      simple && ! data.pos().is_empty() && ! data.neg().is_empty()
    )  ;

    if_debug! {
      let mut s = format!("data:") ;
      s = format!("{}\n  pos {{", s) ;
      for sample in data.pos() {
        s = format!("{}\n    {}", s, sample)
      }
      s = format!("{}\n  }} neg {{", s) ;
      for sample in data.neg() {
        s = format!("{}\n    {}", s, sample)
      }
      s = format!("{}\n  }} unc {{", s) ;
      for sample in data.unc() {
        s = format!("{}\n    {}", s, sample)
      }
      s = format!("{}\n  }}", s) ;
      msg! { self => s }
    }

    let mut best_qual = {
      let core = & self.core ;

      // Run simple if in simple mode.
      if simple {
        profile!{ self tick "learning", "qual", "simple gain" }
        let res = self.qualifiers.maximize(
          pred, |qual| {
            let res = data.simple_gain(qual) ? ;
            if conf.ice.qual_step {
              let _ = core.msg(
                format!(
                  "{}: {}", qual,
                  res.map(|g| format!("{}", g)).unwrap_or("none".into())
                )
              ) ;
              pause_msg(core, "to continue (--qual_step on)") ;
              ()
            }
            core.check_exit() ? ;
            Ok(res)
          }
        ) ;
        profile!{ self mark "learning", "qual", "simple gain" }
        res ?
      } else {

        let qualifiers = & mut self.qualifiers ;
        let self_core = & self.core ;
        let all_data = & self.data ;

        profile!{ |self.core._profiler| tick "learning", "qual", "gain" }
        let res = qualifiers.maximize(
          pred, |qual| {
            let res = data.gain(
              pred, all_data, qual, & self_core._profiler, false
            ) ? ;
            if conf.ice.qual_step {
              let _ = self_core.msg(
                format!(
                  "; {}: {}", qual,
                  res.map(|g| format!("{}", g)).unwrap_or("none".into())
                )
              ) ;
              pause_msg(self_core, "to continue (--qual_step on)") ;
              ()
            }
            core.check_exit() ? ;
            Ok(res)
          }
        ) ;
        profile!{ |self.core._profiler| mark "learning", "qual", "gain" }
        res ?
      }
    } ;

    if let Some((qual, gain)) = best_qual {
      best_qual = if gain >= self.gain_pivot && gain > 0.0 {
        msg! {
          self =>
          "  using qualifier {}, gain: {} >= {} (simple: {})",
          qual, gain, self.gain_pivot, simple
        }
        // This qualifier is satisfactory.
        profile!{ self tick "learning", "qual", "data split" }
        let (q_data, nq_data) = data.split(& qual) ;
        profile!{ self mark "learning", "qual", "data split" }
        return Ok( Some((qual, q_data, nq_data)) )
      } else {
        msg! {
          self =>
          "  qualifier {} is not good enough, gain: {} < {} (simple: {})",
          qual, gain, self.gain_pivot, simple
        }
        // Not good enough, maybe synthesis can do better.
        Some( (qual, gain) )
      }
    }

    if_verb!{
      let mut msg = format!(
        "  could not split remaining data for {}:\n", self.instance[pred]
      ) ;
      msg.push_str("  pos (") ;
      for pos in data.pos() {
        msg.push_str( & format!("\n    {}", pos) )
      }
      msg.push_str("\n  ) neg (") ;
      for neg in data.neg() {
        msg.push_str( & format!("\n    {}", neg) )
      }
      msg.push_str("\n  ) unc (") ;
      for unc in data.unc() {
        msg.push_str( & format!("\n    {}", unc) )
      }
      msg.push_str("\n  )") ;
      msg!{ self => msg } ;
    }

    if data.is_empty() {
      bail!("[bug] cannot synthesize qualifier based on no data")
    }

    self.check_exit() ? ;


    // Synthesize qualifier separating the data.
    let mut best_synth_qual = None ;
    msg! { self => "synthesizing" }
    profile!{ self tick "learning", "qual", "synthesis" } ;
    let res = self.synthesize(pred, & data, & mut best_synth_qual, simple) ;
    profile!{ self mark "learning", "qual", "synthesis" } ;
    if let None = res ? {
      return Ok(None)
    }

    let qual = match ( best_qual, best_synth_qual ) {
      ( Some((qual, gain)), Some((synth_qual, synth_gain)) ) => {
        if synth_gain > gain {
          msg! {
            self =>
            "using synth qualifier {}, gain {} >= {} (for {})",
            synth_qual, synth_gain, gain, qual
          }
          synth_qual
        } else {
          msg! {
            self =>
            "synth qualifier {} is not good enough, gain: {}\n\
            using qualifier {} instead, gain: {}",
            synth_qual, synth_gain, qual, gain
          }
          qual
        }
      },
      ( None, Some((synth_qual, _synth_gain)) ) => {
        msg! {
          self =>
          "using synth qualifier {}, gain {}", synth_qual, _synth_gain
        }
        synth_qual
      },
      // I think this should be unreachable.
      ( Some((qual, _gain)), None ) => {
        msg! {
          self =>
          "using qualifier {}, gain {}", qual, _gain
        }
        qual
      },
      (None, None) => {
        // let mut msg = format!(
        //   "\ncould not split remaining data for {} after synthesis:\n",
        //   self.instance[pred]
        // ) ;
        // msg.push_str("pos (") ;
        // for pos in data.pos() {
        //   msg.push_str( & format!("\n    {}", pos) )
        // }
        // msg.push_str("\n) neg (") ;
        // for neg in data.neg() {
        //   msg.push_str( & format!("\n    {}", neg) )
        // }
        // msg.push_str("\n) unc (") ;
        // for unc in data.unc() {
        //   msg.push_str( & format!("\n    {}", unc) )
        // }
        // msg.push_str("\n)") ;
        // bail!(msg)
        unsat!("by lack of (synth) qualifier")
      },
    } ;
    profile!{ self tick "learning", "qual", "data split" }
    let (q_data, nq_data) = data.split(& qual) ;
    profile!{ self mark "learning", "qual", "data split" }
    Ok( Some((qual, q_data, nq_data)) )
  }

  /// Qualifier synthesis.
  ///
  /// Returns `None` if it received `Exit`.
  pub fn synthesize(
    & mut self, pred: PrdIdx, data: & CData, best: & mut Option<(Term, f64)>,
    simple: bool
  ) -> Res< Option<()> > {

    scoped! {
      let self_data = & self.data ;
      let quals = & mut self.qualifiers ;
      let instance = & self.instance ;
      let self_core = & self.core ;
      let known_quals = & mut self.known_quals ;
      let gain_pivot_synth = self.gain_pivot_synth ;
      known_quals.clear() ;

      // println!("synthesizing") ;

      let mut treatment = |term: Term| {
        self_core.check_exit() ? ;
        let is_new = ! quals.quals_of_contains(
          pred, & term
        ) && known_quals.insert(
          term.clone()
        ) ;

        if ! is_new {
          // Term already known, skip.
          Ok(false)
        } else if let Some(gain) = {
          if simple {
            data.simple_gain(& term) ?
          } else {
            data.gain(
              pred, self_data, & term, & self_core._profiler, false
            ) ?
          }
        } {
          // println!("  - {}", gain) ;
          if conf.ice.qual_step {
            let _ = self_core.msg(
              format!(
                "{}: {} (synthesis)", term, gain
              )
            ) ;
            pause_msg(self_core, "to continue (--qual_step on)") ;
            ()
          }
          if conf.ice.add_synth && gain == 1.0 {
            msg! { self_core => "  adding synth qual {}", term }
            quals.insert(term.clone(), pred) ? ;
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

          let stop = gain >= 0.9999
          || if let Some(pivot) = gain_pivot_synth {
            gain >= pivot
          } else {
            false
          } ;

          if stop {
            msg! {
              self_core =>
              "  stopping on synth qual {}, gain {}",
              best.as_ref().unwrap().0, gain
            }
          }
          Ok(stop)
        } else {
          Ok(false)
        }
      } ;

      use self::synth::SynthSys ;
      let mut synth_sys = SynthSys::new( & instance[pred].sig ) ;

      'synth: loop {

        for sample in data.iter(! simple) {
          self_core.check_exit() ? ;
          let done = synth_sys.sample_synth(
            sample, & mut treatment, & self_core._profiler
          ) ? ;
          if done { break }
        }

        synth_sys.increment() ;
        if synth_sys.is_done() {
          break 'synth
        }

      }
    }

    Ok( Some(()) )
  }


  /// Checks whether assuming some data as positive (if `pos` is true,
  /// negative otherwise) is legal.
  ///
  /// **NB**: if assuming the data positive / negative is legal,
  /// the data will be forced to be positive / negative in the solver
  /// automatically. Otherwise, the actlit is deactivated.
  pub fn is_legal(
    & mut self, pred: PrdIdx, unc: & Vec<Args>, pos: bool
  ) -> Res<bool> {
    if unc.is_empty() { return Ok(true) }
    profile!{ self tick "learning", "smt", "legal" }

    // Wrap actlit and increment counter.
    let samples = SmtActSamples::new(
      & mut self.solver, pred, unc, pos
    ) ? ;
    self.solver.assert( & samples ) ? ;

    let legal = if self.solver.check_sat_act(
      Some(& samples.actlit)
    ) ? {
      profile!{ self mark "learning", "smt", "legal" }
      true
    } else {
      profile!{ self mark "learning", "smt", "legal" }
      false
    } ;

    samples.force(& mut self.solver, legal) ? ;

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
    let unc = & self.data.map()[pred] ;
    if unc.is_empty() {
      profile!{ self mark "learning", "smt", "all legal" }
      return Ok(true)
    }

    // Wrap actlit and increment counter.
    let samples = SmtActSamples::new(
      & mut self.solver, pred, unc, pos
    ) ? ;
    self.solver.assert(& samples) ? ;

    let legal = if self.solver.check_sat_act(
      Some(& samples.actlit)
    ) ? {
      profile!{ self mark "learning", "smt", "all legal" }
      true
    } else {
      profile!{ self mark "learning", "smt", "all legal" }
      false
    } ;

    samples.force(& mut self.solver, legal) ? ;

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

    // Positive data.
    self.solver.comment("Positive data:") ? ;
    for (pred, set) in self.data.pos.index_iter() {
      for sample in set.iter() {
        let is_new = self.dec_mem[pred].insert( sample.uid() ) ;
        debug_assert!(is_new) ;
        self.solver.define_const(
          & SmtSample::new(pred, sample),
          typ::bool().get(), & "true"
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
        self.solver.define_const(
          & SmtSample::new(pred, sample),
          typ::bool().get(), & "false"
        ) ?
      }
    }

    self.solver.comment("Sample declarations for constraints:") ? ;
    // Declare all samples used in constraints.
    for (pred, map) in self.data.map().index_iter() {
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
      //           & SmtSample(pred, sample), & args, & Typ::Bool, & "true", & ()
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
              & SmtSample::new(pred, sample), & typ::RTyp::Bool,
            ) ?
          }
        }
      // }
    }

    self.solver.comment("Constraints:") ? ;
    // Assert all constraints.
    for constraint in self.data.constraints.iter() {
      if ! constraint.is_tautology() {
        self.solver.assert(
          & SmtConstraint::new(constraint)
        ) ?
      }
    }

    Ok(false)
  }
}

impl<'core> ::std::ops::Deref for IceLearner<'core> {
  type Target = MsgCore ;
  fn deref(& self) -> & MsgCore { & self.core }
}


//! ICE learner.

pub mod mining ;

use common::* ;
use common::data::* ;
use common::msg::* ;
use instance::{ Instance, Term, Op, Typ } ;
use self::mining::* ;
use self::smt::* ;



/// Smt-related things.
pub mod smt {
  use common::* ;
  use common::data::* ;

  /// Wrapper around predicate / sample that forces smt printing.
  pub struct SWrap<'a>(pub PrdIdx, pub & 'a HSample) ;
  impl<'a> ::rsmt2::Expr2Smt<()> for SWrap<'a> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      smt_cast_io!(
        "writing sample as expression" => write!(
          w, "|p_{} {}|", self.0, self.1.uid()
        )
      )
    }
  }
  impl<'a> ::rsmt2::Sym2Smt<()> for SWrap<'a> {
    fn sym_to_smt2<Writer>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> where Writer: Write {
      use ::rsmt2::Expr2Smt ;
      self.expr_to_smt2(w, & ())
    }
  }


  /// Wrapper around constraints that forces smt printing consistent with
  /// [`SWrap`](struct.SWrap.html).
  pub struct CWrap<'a>(pub & 'a Constraint) ;
  impl<'a> ::rsmt2::Expr2Smt<()> for CWrap<'a> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      let blah = "writing constraint as expression" ;
      smtry_io!( blah => write!(w, "(=> (and") ) ;
      for lhs in & self.0.lhs {
        smtry_io!( blah => write!(w, " ", ) ) ;
        SWrap(lhs.pred, & lhs.args).expr_to_smt2(w, & ()) ?
      }
      smtry_io!( blah => write!(w, ") ") ) ;
      if let Some(rhs) = self.0.rhs.as_ref() {
        SWrap(rhs.pred, & rhs.args).expr_to_smt2(w, & ()) ?
      } else {
        smtry_io!( blah => write!(w, "false") ) ;
      }
      smtry_io!( blah => write!(w, ")") ) ;
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
  impl<'a> ::rsmt2::Expr2Smt<()> for ActWrap<& 'a HSamples> {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      let blah = "writing unclassified data activation as expression" ;
      smtry_io!(
        blah => write!(
          w, "(=> act_{} ({}", self.actlit,
          if self.pos { "and" } else { "not (or" }
        )
      ) ;
      for unc in self.unc {
        smtry_io!( blah => write!(w, " ", ) ) ;
        SWrap(self.pred, unc).expr_to_smt2(w, & ()) ?
      }
      smtry_io!( blah => write!(w, "))") ) ;
      if ! self.pos {
        smtry_io!( blah => write!(w, ")") )
      }
      Ok(())
    }
  }
  impl<'a, T> ::rsmt2::Expr2Smt<()> for ActWrap<
    & 'a HConMap<Args, T>
  > {
    fn expr_to_smt2<Writer: Write>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> {
      let blah = "writing unclassified data activation as expression" ;
      smtry_io!(
        blah => write!(
          w, "(=> act_{} ({}", self.actlit,
          if self.pos { "and" } else { "not (or" }
        )
      ) ;
      for (unc, _) in self.unc {
        smtry_io!( blah => write!(w, " ", ) ) ;
        SWrap(self.pred, unc).expr_to_smt2(w, & ()) ?
      }
      smtry_io!( blah => write!(w, "))") ) ;
      if ! self.pos {
        smtry_io!( blah => write!(w, ")") )
      }
      Ok(())
    }
  }
  impl<Samples> ::rsmt2::Sym2Smt<()> for ActWrap<Samples> {
    fn sym_to_smt2<Writer>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> where Writer: Write {
      smt_cast_io!(
        "writing actlit symbol" => write!(w, "act_{}", self.actlit)
      )
    }
  }


  /// Wrapper around some values and some coefficients, used by
  /// [synthesize](../struct.IceLearner.html#method.synthezise) to assert the
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
    pub fn mk(
      vals: & 'a Vec<Int>, coefs: & 'a Vec<VarIdx>,
      cst: & 'static str, pos: bool
    ) -> Self {
      debug_assert!( vals.len() == coefs.len() ) ;
      ValCoefWrap { vals, coefs, cst, pos }
    }
  }
  impl<'a> ::rsmt2::Expr2Smt<()> for ValCoefWrap<'a> {
    fn expr_to_smt2<Writer>(
      & self, w: & mut Writer, _: & ()
    ) -> SmtRes<()> where Writer: Write {
      let blah = "while writing `ValCoefWrap` as expression" ;
      smtry_io!(
        blah => if self.pos { write!(w, "(>= (+") } else { write!(w, "(< (+") }
      ) ;
      for (val, coef) in self.vals.iter().zip( self.coefs ) {
        use ::rsmt2::Sym2Smt ;
        smtry_io!(blah =>
          write!(w, " (* {} ", val) ;
          coef.sym_to_smt2(w, & ()) ;
          write!(w, ")")
        )
      }
      smtry_io!(
        blah => write!(w, " {}) 0)", self.cst)
      ) ;
      Ok(())
    }
  }
}




/// Launcher.
pub struct Launcher ;
unsafe impl Sync for Launcher {}
unsafe impl Send for Launcher {}
impl Launcher {
  /// Launches an smt learner.
  pub fn launch(
    core: & LearnerCore, instance: Arc<Instance>, data: Arc<Data>
  ) -> Res<()> {
    use rsmt2::{ solver, Kid } ;
    let mut kid = Kid::mk( conf.solver_conf() ).chain_err(
      || "while spawning the teacher's solver"
    ) ? ;
    let conflict_solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    let mut synth_kid = Kid::mk( conf.solver_conf() ).chain_err(
      || "while spawning the teacher's synthesis solver"
    ) ? ;
    let synth_solver = solver(& mut synth_kid, Parser).chain_err(
      || "while constructing the teacher's synthesis solver"
    ) ? ;
    if let Some(log) = conf.smt_log_file("ice_learner") ? {
      let synth_log = conf.smt_log_file("ice_learner_synthesizer")?.expect(
        "[unreachable] log mod is active"
      ) ;
      IceLearner::mk(
        & core, instance, data,
        conflict_solver.tee(log), synth_solver.tee(synth_log)
      ).run()
    } else {
      IceLearner::mk(
        & core, instance, data,
        conflict_solver, synth_solver
      ).run()
    }
  }
}
impl Learner for Launcher {
  fn run(
    & self, core: LearnerCore, instance: Arc<Instance>, data: Arc<Data>
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
  /// Learning data.
  pub data: Arc<Data>,
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
}
impl<'core, 'kid, Slver> IceLearner<'core, Slver>
where Slver: Solver<'kid, Parser> + ::rsmt2::QueryIdent<'kid, Parser, ()> {
  /// Ice learner constructor.
  pub fn mk(
    core: & 'core LearnerCore, instance: Arc<Instance>,
    data: Arc<Data>, solver: Slver, synth_solver: Slver
  ) -> Self {
    let qualifiers = Qualifiers::mk(& * instance) ;
    let dec_mem = vec![
      HashSet::with_capacity(103) ; instance.preds().len()
    ].into() ;
    let candidate = vec![ None ; instance.preds().len() ].into() ;
    IceLearner {
      instance, qualifiers, data, solver, synth_solver, core,
      finished: Vec::with_capacity(103),
      unfinished: Vec::with_capacity(103),
      classifier: HashMap::with_capacity(1003),
      dec_mem, candidate, actlit: 0,
    }
  }

  /// Runs the learner.
  pub fn run(mut self) -> Res<()> {
    let mut teacher_alive = true ;
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
      match self.recv() {
        Some(data) => if let Some(candidates) = self.learn(data) ? {
          teacher_alive = self.send_cands(candidates) ?
        } else {
          bail!("can't synthesize candidates for this, sorry")
        },
        None => teacher_alive = false,
      }
    }
  }

  /// Sends some candidates.
  ///
  /// Also resets the solver and clears declaration memory.
  pub fn send_cands(& mut self, candidates: Candidates) -> Res<bool> {
    let res = self.send_candidates(
      candidates
    ) ;
    // Reset and clear declaration memory.
    self.solver.reset() ? ;
    for set in self.dec_mem.iter_mut() {
      set.clear()
    } ;
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
  pub fn learn(& mut self, data: LearningData) -> Res< Option<Candidates> > {
    self.qualifiers.clear_blacklist() ;
    self.qualifiers.register_data(data) ? ;

    self.setup_solver().chain_err(
      || "while initializing the solver"
    ) ? ;

    let prd_count = self.instance.preds().len() ;
    debug_assert!{{
      let mut okay = true ;
      for term_opt in self.candidate.iter_mut() {
        okay = okay && term_opt.is_none() ;
      }
      okay
    }}
    // Stores `(<unclassified_count>, <classified_count>, <prd_index>)`
    let mut predicates = Vec::with_capacity(prd_count) ;

    for pred in PrdRange::zero_to(prd_count) {
      if let Some(term) = self.instance.term_of(pred) {
        self.candidate[pred] = Some( term.clone() ) ;
        continue
      }
      let pos_len = self.data.pos[pred].read().map_err(corrupted_err)?.len() ;
      let neg_len = self.data.neg[pred].read().map_err(corrupted_err)?.len() ;
      let unc_len = self.data.map[pred].read().map_err(corrupted_err)?.len() ;
      if pos_len == 0 && neg_len != 0 {
        // Maybe we can assert everything as negative right away?
        if self.is_legal_pred(pred, false) ? {
          msg!(
            self =>
            "{} only has negative ({}) and unclassified ({}) data\n\
            legal check ok, assuming everything negative",
            self.instance[pred], neg_len, unc_len
          ) ;
          self.candidate[pred] = Some( self.instance.bool(false) ) ;
          continue
        }
      } else if neg_len == 0 && pos_len != 0 {
        // Maybe we can assert everything as positive right away?
        if self.is_legal_pred(pred, true) ? {
          msg!(
            self =>
            "{} only has positive ({}) and unclassified ({}) data\n\
            legal check ok, assuming everything positive",
            self.instance[pred], pos_len, unc_len
          ) ;
          self.candidate[pred] = Some( self.instance.bool(true) ) ;
          continue
        }
      }
      predicates.push((
        unc_len, pos_len + neg_len, pred
      ))
    }

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

    'pred_iter: for (_unc, _cla, pred) in predicates {
      msg!(
        self => "{}: {} unclassified, {} classified",
                self.instance[pred], _unc, _cla
      ) ;
      let data = self.data.data_of(pred) ? ;
      if let Some(term) = self.instance.term_of(pred) {
        self.candidate[pred] = Some( term.clone() ) ;
        continue 'pred_iter
      }
      if let Some(term) = self.pred_learn(pred, data) ? {
        self.candidate[pred] = Some(term)
      } else {
        return Ok(None)
      }
    }
    let mut candidates = PrdMap::with_capacity(prd_count) ;
    for none_soon in self.candidate.iter_mut() {
      let mut term_opt = None ;
      ::std::mem::swap(none_soon, & mut term_opt) ;
      if let Some(term) = term_opt {
        candidates.push(term)
      } else {
        bail!(
          "[bug] done generating candidates but some of them are still `None`"
        )
      }
    }
    Ok( Some(candidates) )
  }


  /// Backtracks to the last element of `unfinished`. Updates blacklisted
  /// qualifiers. Returns `None` iff `unfinished` was empty meaning the
  /// learning process is over.
  pub fn backtrack(& mut self) -> Option<(Branch, CData)> {
    msg!{ self => "backtracking..." } ;
    // Backtracking or exit loop.
    if let Some( (nu_branch, nu_data) ) = self.unfinished.pop() {
      // Update blacklisted qualifiers.
      self.qualifiers.clear_blacklist() ;
      for & (ref t, _) in & nu_branch {
        self.qualifiers.blacklist(t)
      }
      // Update data, some previously unclassified data may be classified now.
      // (cannot happen currently)
      // self.classify(& mut nu_data) ;
      Some( (nu_branch, nu_data) )
    } else {
      None
    }
  }

  /// Looks for a classifier for a given predicate.
  pub fn pred_learn(
    & mut self, pred: PrdIdx, mut data: CData
  ) -> Res< Option<Term> > {
    debug_assert!( self.finished.is_empty() ) ;
    debug_assert!( self.unfinished.is_empty() ) ;
    self.classifier.clear() ;

    msg!(
      self => "  working on predicate {} (pos: {}, neg: {}, unc: {}",
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
        for unc in data.unc {
          let prev = self.classifier.insert(unc, true) ;
          debug_assert!( prev.is_none() )
        }
        branch.shrink_to_fit() ;
        if branch.is_empty() {
          debug_assert!( self.finished.is_empty() ) ;
          debug_assert!( self.unfinished.is_empty() ) ;
          return Ok(
            Some( self.instance.bool(true) )
          )
        } else {
          self.finished.push(branch) ;
        }
        if let Some((nu_branch, nu_data)) = self.backtrack() {
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
        for unc in data.unc {
          let prev = self.classifier.insert(unc, false) ;
          debug_assert!( prev.is_none() )
        }
        if branch.is_empty() {
          debug_assert!( self.finished.is_empty() ) ;
          debug_assert!( self.unfinished.is_empty() ) ;
          return Ok(
            Some( self.instance.bool(false) )
          )
        }
        if let Some((nu_branch, nu_data)) = self.backtrack() {
          branch = nu_branch ;
          data = nu_data ;
          continue 'learning
        } else {
          break 'learning
        }
      }



      // Could not close the branch, look for a qualifier.
      let (qual, q_data, nq_data) = self.get_qualifier(pred, data) ? ;
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

    debug_assert!( self.unfinished.is_empty() ) ;
    let mut or_args = Vec::with_capacity( self.finished.len() ) ;
    for branch in self.finished.drain(0..) {
      let mut and_args = Vec::with_capacity( branch.len() ) ;
      for (term, pos) in branch {
        if pos {
          and_args.push(term)
        } else {
          and_args.push( self.instance.op(Op::Not, vec![term]) )
        }
      }
      or_args.push( self.instance.op(Op::And, and_args) )
    }
    Ok(
      Some( self.instance.op(Op::Or, or_args) )
    )
  }

  /// Looks for a qualifier. Requires a mutable `self` in case it needs to
  /// synthesize a qualifier.
  ///
  /// Does **not** blacklist the qualifier it returns.
  pub fn get_qualifier(
    & mut self, pred: PrdIdx, data: CData
  ) -> Res< (Term, CData, CData) > {

    { // Try using an existing qualifier. Early return if one is found.
      let mut maybe_qual = None ;

      'search_qual: for (qual, values) in self.qualifiers.of(pred) {
        msg!{ debug self => "    {}:", qual } ;
        if let Some(
          (gain, (_q_pos, _q_neg, _q_unc), (_nq_pos, _nq_neg, _nq_unc))
        ) = data.gain(pred, & self.data, & values) ? {
          msg!{
            debug self =>
              "    gain is {} ({}, {}, {} / {}, {}, {})",
              gain, _q_pos, _q_neg, _q_unc, _nq_pos, _nq_neg, _nq_unc
          } ;
          let better = if let Some( (old_gain, _, _) ) = maybe_qual {
            old_gain < gain
          } else { true } ;
          if better {
            maybe_qual = Some( (gain, qual, values) )
          }
          if gain == 1. { break 'search_qual }
        } else {
          msg!{
            debug self =>
              "    does not split anything..."
          } ;
          ()
        }
      }

      if let Some( (_gain, qual, values) ) = maybe_qual {
        let (q_data, nq_data) = data.split(values) ;

        msg!(
          self =>
            "  using qualifier {} | \
            gain: {}, pos: ({},{},{}), neg: ({},{},{})",
            qual.string_do(
              & self.instance[pred].sig.index_iter().map(
                |(idx, typ)| ::instance::info::VarInfo {
                  name: format!("v_{}", idx), typ: * typ, idx
                }
              ).collect(), |s| s.to_string()
            ).unwrap(),
            _gain,
            q_data.pos.len(),
            q_data.neg.len(),
            q_data.unc.len(),
            nq_data.pos.len(),
            nq_data.neg.len(),
            nq_data.unc.len(),
        ) ;
        return Ok( (qual.clone(), q_data, nq_data) )
      }
    }

    // Reachable only if none of our qualifiers can split the data.

    if_verb!{
      let mut msg = "\ncould not split remaining data:\n".to_string() ;
      msg.push_str("pos (") ;
      for pos in & data.pos {
        msg.push_str( & format!("\n    {}", pos) )
      }
      msg.push_str("\n) neg (") ;
      for neg in & data.neg {
        msg.push_str( & format!("\n    {}", neg) )
      }
      msg.push_str("\n) unc (") ;
      for unc in & data.unc {
        msg.push_str( & format!("\n    {}", unc) )
      }
      msg.push_str(")") ;
      msg!{ self => msg } ;
    }
    // bail!( "qualifier synthesis is untested and offline for now" ) ;

    // Synthesize qualifier separating the data.
    let qual = match (
      data.pos.is_empty(), data.neg.is_empty(), data.unc.is_empty()
    ) {
      (false, false, _) => Self::synthesize(
        & mut self.synth_solver, & * self.instance,
        & data.pos[0], true, & data.neg[0]
      ) ?,
      (false, _, false) => Self::synthesize(
        & mut self.synth_solver, & * self.instance,
        & data.pos[0], true, & data.unc[0]
      ) ?,
      (true, false, false) => Self::synthesize(
        & mut self.synth_solver, & * self.instance,
        & data.neg[0], false, & data.unc[0]
      ) ?,
      (true, true, false) if data.unc.len() > 1 => Self::synthesize(
        & mut self.synth_solver, & * self.instance,
        & data.unc[0], true, & data.unc[1]
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

    // Insert new qualifier.
    let (q_data, nq_data) = {
      let values = self.qualifiers.add_qual(qual.clone(), & self.data) ? ;
      data.split(values)
    } ;
    msg!(
      self =>
        "  using synthetic qualifier {} | \
        pos: ({},{},{}), neg: ({},{},{})",
        qual,
        q_data.pos.len(),
        q_data.neg.len(),
        q_data.unc.len(),
        nq_data.pos.len(),
        nq_data.neg.len(),
        nq_data.unc.len(),
    ) ;
    Ok( (qual, q_data, nq_data) )
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

    // Wrap actlit and increment counter.
    let actlit = ActWrap { actlit: self.actlit, pred, unc, pos } ;
    self.actlit += 1 ;

    // Declare and assert.
    self.solver.declare_const(& actlit, & Typ::Bool, & ()) ? ;
    self.solver.assert( & actlit, & () ) ? ;

    let actlits = [actlit] ;

    if self.solver.check_sat_assuming(& actlits, & ()) ? {
      self.solver.assert( & actlits[0].as_ident(), & () ) ? ;
      Ok(true)
    } else {
      self.solver.assert(
        & format!("(not {})", actlits[0].as_ident()), & ()
      ) ? ;
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
    let unc = self.data.map[pred].read().map_err(corrupted_err) ? ;
    let unc = & * unc ;
    if unc.is_empty() { return Ok(true) }

    // Wrap actlit and increment counter.
    let actlit = ActWrap { actlit: self.actlit, pred, unc, pos } ;
    self.actlit += 1 ;

    // Declare and assert.
    self.solver.declare_const(& actlit, & Typ::Bool, & ()) ? ;
    self.solver.assert( & actlit, & () ) ? ;

    let actlits = [actlit] ;

    if self.solver.check_sat_assuming(& actlits, & ()) ? {
      self.solver.assert( & actlits[0].as_ident(), & () ) ? ;
      Ok(true)
    } else {
      self.solver.assert(
        & format!("(not {})", actlits[0].as_ident()), & ()
      ) ? ;
      Ok(false)
    }
  }


  /// Sets the solver to check that constraints are respected.
  ///
  /// - **does not** reset the solver or clean declaration memory (must be
  ///   done before sending previous candidates)
  /// - **defines** pos (neg) data as `true` (`false`)
  /// - **declares** samples that neither pos nor neg
  /// - asserts constraints
  pub fn setup_solver(& mut self) -> Res<()> {
    self.actlit = 0 ;
    
    // Dummy arguments used in the `define_fun` for pos (neg) data.
    let args: [ (SWrap, Typ) ; 0 ] = [] ;

    // Positive data.
    self.solver.comment("Positive data:") ? ;
    for (pred, set) in self.data.pos.index_iter() {
      for sample in set.read().map_err(corrupted_err)?.iter() {
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
      for sample in set.read().map_err(corrupted_err)?.iter() {
        let is_new = self.dec_mem[pred].insert( sample.uid() ) ;
        if ! is_new {
          bail!(
            "{} found:\n\
            predicate {} must be {} for inputs {}",
            conf.bad("contradiction"), self.instance[pred],
            conf.emph("true and false"), sample
          )
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
        for (sample, _) in map.read().map_err(corrupted_err)?.iter() {
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
    for constraint in self.data.constraints.read().map_err(
      corrupted_err
    )?.iter() {
      if ! constraint.is_tautology() {
        self.solver.assert( & CWrap(constraint), & () ) ?
      }
    }

    Ok(())
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
  pub fn synthesize(
    solver: & mut Slver, instance: & Instance,
    s_1: & HSample, pos: bool, s_2: & HSample
  ) -> Res<Term> {
    use instance::Val ;
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

    let constraint_1 = ValCoefWrap::mk(& p_1, & coefs, cst, pos) ;
    let constraint_2 = ValCoefWrap::mk(& p_2, & coefs, cst, ! pos) ;

    solver.reset() ? ;
    // Declare coefs and constant.
    solver.declare_const(& cst, & Typ::Int, & ()) ? ;
    for coef in & coefs {
      solver.declare_const(coef, & Typ::Int, & ()) ?
    }
    solver.assert( & constraint_1, & () ) ? ;
    solver.assert( & constraint_2, & () ) ? ;

    let model = if solver.check_sat() ? {
      solver.get_model() ?
    } else {
      bail!("[unreachable] could not separate points {:?} and {:?}", p_1, p_2)
    } ;

    let mut sum = Vec::with_capacity( coefs.len() ) ;
    for (var_opt, val) in model {
      use num::Zero ;
      if ! val.is_zero() {
        let val = instance.int(val) ;
        if let Some(var) = var_opt {
          let var = instance.var(var) ;
          sum.push(
            instance.op( Op::Mul, vec![val, var] )
          )
        } else {
          sum.push(val)
        }
      }
    }
    let lhs = instance.op( Op::Add, sum ) ;
    let rhs = instance.zero() ;

    Ok(
      instance.ge(lhs, rhs)
    )
  }
}

impl<
  'core, 'kid, Slver: Solver<'kid, Parser>
> HasLearnerCore for IceLearner<'core, Slver> {
  fn core(& self) -> & LearnerCore { self.core }
}






/// A branch of the a decision tree.
///
/// Boolean is `false` if the term should be negated.
pub type Branch = Vec<(Term, bool)> ;

/// Projected data to classify.
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
  pub fn simple_gain(& self, qual: & QualValues) -> Option<f64> {
    // println!("my entropy") ;
    let my_entropy = Self::shannon_entropy(
      self.pos.len() as f64, self.neg.len() as f64
    ) ;
    let card = (self.pos.len() as f64) + (self.neg.len() as f64) ;
    let (
      mut q_pos, mut q_neg, mut q_unc, mut nq_pos, mut nq_neg, mut nq_unc
    ) = (0., 0., 0., 0., 0., 0.) ;
    for pos in & self.pos {
      if qual.eval(pos) { q_pos += 1. } else { nq_pos += 1. }
    }
    for neg in & self.neg {
      if qual.eval(neg) { q_neg += 1. } else { nq_neg += 1. }
    }
    for unc in & self.unc {
      if qual.eval(unc) { q_unc += 1. } else { nq_unc += 1. }
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
    let mut proba = EntropyBuilder::mk() ;
    proba.set_pos_count( self.pos.len() ) ;
    proba.set_neg_count( self.neg.len() ) ;
    for unc in & self.unc {
      proba.add_unc(data, pred, unc) ?
    }
    Ok( proba.entropy() )
  }

  /// Modified gain, uses `entropy`.
  pub fn gain(
    & self, pred: PrdIdx, data: & Data, qual: & QualValues
  ) -> Res< Option< (f64, (f64, f64, f64), (f64, f64, f64) ) > > {
    let my_entropy = self.entropy(pred, data) ? ;
    let my_card = (
      self.pos.len() + self.neg.len() + self.unc.len()
    ) as f64 ;
    let (mut q_ent, mut nq_ent) = (
      EntropyBuilder::mk(), EntropyBuilder::mk()
    ) ;
    let (
      mut q_pos, mut q_neg, mut q_unc, mut nq_pos, mut nq_neg, mut nq_unc
    ) = (0, 0, 0., 0, 0, 0.) ;
    for pos in & self.pos {
      if qual.eval(pos) { q_pos += 1 } else { nq_pos += 1 }
    }
    q_ent.set_pos_count(q_pos) ;
    nq_ent.set_pos_count(nq_pos) ;

    for neg in & self.neg {
      if qual.eval(neg) { q_neg += 1 } else { nq_neg += 1 }
    }
    q_ent.set_neg_count(q_neg) ;
    nq_ent.set_neg_count(nq_neg) ;

    for unc in & self.unc {
      if qual.eval(unc) {
        q_unc += 1. ;
        q_ent.add_unc(data, pred, unc) ?
      } else {
        nq_unc += 1. ;
        nq_ent.add_unc(data, pred, unc) ?
      }
    }
    
    let (q_pos, q_neg, nq_pos, nq_neg) = (
      q_pos as f64, q_neg as f64, nq_pos as f64, nq_neg as f64
    ) ;

    // Is this qualifier separating anything?
    if q_pos + q_neg + q_unc == 0. {
      return Ok(None)
    }
    if nq_pos + nq_neg + nq_unc == 0. {
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
  pub fn split(self, qual: & QualValues) -> (Self, Self) {
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
      if qual.eval(& pos) {
        q.pos.push( pos )
      } else {
        nq.pos.push( pos )
      }
    }
    for neg in self.neg {
      if qual.eval(& neg) {
        q.neg.push( neg )
      } else {
        nq.neg.push( neg )
      }
    }
    for unc in self.unc {
      if qual.eval(& unc) {
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



/// Wrapper around an `f64` used to compute a the approximation of the ratio
/// between legal positive classifications and negative ones, without actually
/// splitting the data.
///
/// See the paper for more details.
pub struct EntropyBuilder { num: f64, den: usize }
impl EntropyBuilder {
  /// Constructor.
  pub fn mk() -> Self {
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

    if let Some(constraints) = data.map[prd].read().map_err(
      corrupted_err
    )?.get(& sample) {
      for constraint in constraints {
        let constraint = & data.constraints.read().map_err(
          corrupted_err
        )?[* constraint] ;
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






/// Can parse values (int) and idents (`VarIdx`).
///
/// In the ice learner, parsing is only used for synthesizing, not for
/// conflict detection.
pub struct Parser ;
impl ::rsmt2::ParseSmt2 for Parser {
  type Ident = Option<VarIdx> ;
  type Value = Int ;
  type Expr = () ;
  type Proof = () ;
  type I = () ;

  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], Option<VarIdx>> {
    use std::str::FromStr ;
    preceded!(
      bytes,
      char!('v'),
      opt!(
        preceded!(
          char!('_'),
          map!(
            map_res!(
              map_res!(
                re_bytes_find!("^[0-9][0-9]*"),
                ::std::str::from_utf8
              ),
              usize::from_str
            ),
            |n| n.into()
          )
        )
      )
    )
  }

  fn parse_value<'a>(
    & self, bytes: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], Int> {
    use instance::build::{ int, spc_cmt } ;
    dbg_dmp!(bytes, alt_complete!(
      // bytes,
      int | do_parse!(
        char!('(') >>
        spc_cmt >> char!('-') >>
        spc_cmt >> value: int >>
        spc_cmt >> char!(')') >>
        (- value)
      )
    ))
  }

  fn parse_expr<'a>(
    & self, _: & 'a [u8], _: & ()
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_expr` of the ICE parser should never be called")
  }

  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_proof` of the ICE parser should never be called")
  }
}



//! Sample storage used by the teacher and the learner(s).

use common::{
  *,
  var_to::vals::{
    RVarVals, VarValsSet, VarValsMap
  },
} ;
use learning::ice::data::CData ;
// use unsat_core::sample_graph::SampleGraph ;

pub mod sample ;
pub mod constraint ;
mod info ;

pub use self::sample::{ Sample } ;
pub use self::constraint::Constraint ;
use self::info::CstrInfo ;





/// Structure manipulating unprojected learning data.
pub struct Data {
  /// Instance, only used for printing.
  pub instance: Arc<Instance>,
  /// Positive examples.
  pub pos: PrdMap< VarValsSet >,
  /// Negative examples.
  pub neg: PrdMap< VarValsSet >,
  /// Constraints.
  pub constraints: CstrMap<Constraint>,

  /// Map from samples to constraints.
  map: PrdMap< VarValsMap<CstrSet> >,

  /// Stores pos/neg samples temporarily before they're added.
  staged: Staged,
  /// Constraint info.
  cstr_info: CstrInfo,
  // /// Sample dependency graph for unsat cores extraction.
  // ///
  // /// Different from `None` iff `conf.unsat_cores()`
  // graph: Option<SampleGraph>,

  /// Profiler.
  _profiler: Profiler,
}

impl Clone for Data {
  fn clone(& self) -> Self {
    Data {
      instance: self.instance.clone(),
      pos: self.pos.clone(),
      neg: self.neg.clone(),
      constraints: self.constraints.clone(),
      map: self.map.clone(),

      staged: self.staged.clone(), // Empty anyway.
      cstr_info: self.cstr_info.clone(),
      // graph: None,
      _profiler: Profiler::new(),
    }
  }
}


impl ::std::fmt::Debug for Data {
  fn fmt(& self, fmt: & mut ::std::fmt::Formatter) -> ::std::fmt::Result {
    write!(
      fmt,
      "Data {{ {} pos, {} neg, {} constraints }}",
      self.pos.iter().fold(0, |acc, argss| acc + argss.len()),
      self.neg.iter().fold(0, |acc, argss| acc + argss.len()),
      self.constraints.len(),
    )
  }
}


impl Data {

  /// Constructor.
  pub fn new(instance: Arc<Instance>) -> Self {
    let pred_count = instance.preds().len() ;

    let (
      mut map, mut pos, mut neg
    ) = (
      PrdMap::with_capacity(pred_count),
      PrdMap::with_capacity(pred_count),
      PrdMap::with_capacity(pred_count)
    ) ;
    for _ in instance.preds() {
      map.push( VarValsMap::with_capacity(103) ) ;
      pos.push( VarValsSet::with_capacity(103) ) ;
      neg.push( VarValsSet::with_capacity(103) ) ;
    }
    // let track_samples = instance.track_samples() ;

    let constraints = CstrMap::with_capacity(103) ;
    Data {
      instance, pos, neg, constraints, map,
      staged: Staged::with_capacity(pred_count),
      cstr_info: CstrInfo::new(),
      // graph: if track_samples {
      //   Some( SampleGraph::new() )
      // } else {
      //   None
      // },
      _profiler: Profiler::new(),
    }
  }

  /// Accessor for the map from samples to constraints.
  pub fn map(& self) -> & PrdMap< VarValsMap<CstrSet> > {
    & self.map
  }

  /// Destroys the data and returns profiling info.
  pub fn destroy(self) -> Profiler {
    let _pos_len = self.pos.iter().fold(
      0, |acc, samples| acc + samples.len()
    ) ;
    let _neg_len = self.neg.iter().fold(
      0, |acc, samples| acc + samples.len()
    ) ;
    let _all = _pos_len + _neg_len + self.map.iter().fold(
      0, |acc, map| acc + map.len()
    ) ;
    profile! {
      self "> constraints" => add self.constraints.len()
    }
    profile! {
      self "> pos samples" => add _pos_len
    }
    profile! {
      self "> neg samples" => add _neg_len
    }
    profile! {
      self "> all samples" => add _all
    }
    self._profiler
  }

  /// Clears the modified constraint set.
  pub fn clear_modded(& mut self) {
    self.cstr_info.clear_modded()
  }

  /// String representation of a constraint.
  #[allow(dead_code)]
  fn str_of(& self, c: CstrIdx) -> String {
    format!(
      "# {}\n{}", c,
      self.constraints[c].to_string_info(
        self.instance.preds()
      ).unwrap()
    )
  }

  // /// The sample graph, used for unsat cores.
  // pub fn sample_graph(& mut self) -> Option<SampleGraph> {
  //   if let Some(ref mut graph) = self.graph {
  //     let mut old_graph = SampleGraph::new() ;
  //     ::std::mem::swap(graph, & mut old_graph) ;
  //     Some(old_graph)
  //   } else {
  //     None
  //   }
  // }

  /// Clones the new/modded constraints to create a new `Data`.
  ///
  /// **Clears the set of modified constraints.**
  ///
  /// Used to send modified implications to the assistant.
  pub fn clone_new_constraints(& mut self) -> Res< Option<Data> > {
    let mut data = None ;
    for idx in self.cstr_info.modded() {
      let constraint = & self.constraints[* idx] ;
      if ! constraint.is_tautology() {
        data.get_or_insert_with(
          || Data::new( self.instance.clone() )
        ).raw_add_cstr( constraint.clone() ) ? ;
      }
    }
    self.cstr_info.clear_modded() ;
    Ok(data)
  }

  /// Merges the positive and negative samples in `other` to `self`.
  ///
  /// Does not propagate.
  ///
  /// Returns the number of new positive/negative examples.
  pub fn merge_samples(& mut self, other: Data) -> Res<(usize, usize)> {
    for (pred, samples) in other.pos.into_index_iter() {
      for sample in samples {
        self.staged.add_pos(pred, sample) ;
      }
    }
    for (pred, samples) in other.neg.into_index_iter() {
      for sample in samples {
        self.staged.add_neg(pred, sample) ;
      }
    }
    // if let Some(graph) = self.graph.as_mut() {
    //   if let Some(other) = other.graph {
    //     graph.merge(other)
    //   } else {
    //     bail!("inconsistent sample dependency tracking")
    //   }
    // }
    self.propagate()
  }


  /// Checks whether a constraint is useful.
  ///
  /// Remove all constraints that this constraint makes useless, including the
  /// one(s) it is equal to.
  pub fn cstr_useful(& mut self, index: CstrIdx) -> Res<bool> {
    profile! { self tick "constraint subsumption" }
    let mut to_check = CstrSet::new() ;
    scoped! {
      let constraint = & self.constraints[index] ;
      let similar = if let Some(
        & Sample { pred, ref args }
      ) = constraint.rhs() {
        if let Some(similar) = self.map[pred].get(args) {
          similar
        } else {
          bail!("sample to constraint map is inconsistent")
        }
      } else {
        self.cstr_info.neg()
      } ;
      for idx in similar { 
        if * idx != index {
          let is_new = to_check.insert(* idx) ;
          debug_assert! { is_new }
        }
      }
    }

    let mut useful = true ;

    for similar in to_check.drain() {
      use std::cmp::Ordering::* ;
      match self.constraints[index].compare(
        & self.constraints[similar]
      ).chain_err(
        || "in cstr_useful"
      ) ? {
        // `similar` is implied by `index`, drop it.
        Some(Equal) | Some(Greater) => {
          profile! { self "useless constraints" => add 1 }
          self.tautologize(similar) ?
        },
        // `index` is useless.
        Some(Less) => {
          profile! { self "useless constraints" => add 1 }
          useful = false
        },
        // Not comparable.
        None => (),
      }
    }
    profile! { self mark "constraint subsumption" }

    Ok(useful)
  }


  /// Adds a positive example.
  ///
  /// The `clause` input is necessary for unsat core extraction.
  ///
  /// Does not propagate.
  pub fn add_raw_pos(
    & mut self, clause: ClsIdx, pred: PrdIdx, args: RVarVals
  ) -> () {
    let args = var_to::vals::new(args) ;
    self.add_pos(clause, pred, args.clone()) ;
    ()
  }

  /// Adds a negative example.
  ///
  /// The `clause` input is necessary for unsat core extraction.
  ///
  /// Does not propagate.
  pub fn add_raw_neg(
    & mut self, clause: ClsIdx, pred: PrdIdx, args: RVarVals
  ) -> () {
    let args = var_to::vals::new(args) ;
    self.add_neg(clause, pred, args.clone()) ;
    ()
  }



  /// Adds a positive example.
  ///
  /// The `clause` input is necessary for unsat core extraction.
  ///
  /// Does not propagate.
  pub fn add_pos(
    & mut self, _clause: ClsIdx, pred: PrdIdx, args: VarVals
  ) -> bool {
    // if self.add_pos_untracked( pred, args.clone() ) {
    //   if let Some(graph) = self.graph.as_mut() {
    //     graph.add(
    //       pred, self.instance[clause].rhs().unwrap().1.clone(),
    //       args.clone(), clause, PrdHMap::new()
    //     )
    //   }
    //   true
    // } else {
    //   false
    // }
    self.add_pos_untracked(pred, args)
  }
  /// Adds a positive example.
  ///
  /// Does track dependencies for unsat core.
  ///
  /// Used by the learner(s).
  pub fn add_pos_untracked(
    & mut self, pred: PrdIdx, args: VarVals
  ) -> bool {
    self.staged.add_pos(pred, args)
  }

  /// Adds a new negative example.
  ///
  /// The `clause` input is necessary for unsat core extraction.
  ///
  /// Does not propagate.
  pub fn add_neg(
    & mut self, _clause: ClsIdx, pred: PrdIdx, args: VarVals
  ) -> bool {
    // if self.add_neg_untracked( pred, args.clone() ) {
    //   if let Some(graph) = self.graph.as_mut() {
    //     let mut lhs = PrdHMap::with_capacity(1) ;
    //     let mut farg_map = HConMap::new() ;
    //     // debug_assert_eq! { 1, self.instance[clause].lhs_preds().len() }

    //     let (
    //       p, argss
    //     ) = self.instance[clause].lhs_preds().iter().next().unwrap() ;
    //     debug_assert_eq! { pred, * p }
    //     debug_assert_eq! { 1, argss.len() }
    //     let prev = farg_map.insert(
    //       argss.iter().next().unwrap().clone(), args
    //     ) ;
    //     debug_assert! { prev.is_none() }

    //     let prev = lhs.insert(pred, farg_map) ;
    //     debug_assert! { prev.is_none() }
    //     graph.add_neg(clause, lhs)
    //   }
    //   true
    // } else {
    //   false
    // }
    self.add_neg_untracked(pred, args)
  }
  /// Adds a negative example.
  ///
  /// Does track dependencies for unsat core.
  ///
  /// Used by the learner(s).
  pub fn add_neg_untracked(
    & mut self, pred: PrdIdx, args: VarVals
  ) -> bool {
    self.staged.add_neg(pred, args)
  }




  /// Number of positive/negative samples.
  pub fn pos_neg_count(& self) -> (usize, usize) {
    let (mut pos, mut neg) = (0, 0) ;
    for samples in & self.pos {
      pos += samples.len()
    }
    for samples in & self.neg {
      neg += samples.len()
    }
    (pos, neg)
  }

  /// Shrinks the list of constraints.
  ///
  /// - pops all trailing empty constraints from [`self.constraints`][cstrs].
  ///
  /// Called at the end of [`propagate`][prop].
  ///
  /// [cstrs]: #structfield.constraints (constraints field)
  /// [prop]: #method.propagate (propagate function)
  fn shrink_constraints(& mut self) {
    for map in self.map.iter_mut() {
      map.retain(
        |_, set| ! set.is_empty()
      )
    }
    loop {
      scoped! {
        if let Some(last) = self.constraints.last() {
          if ! last.is_tautology() {
            return ()
          }
        } else {
          return ()
        }
      }
      let last = self.constraints.pop() ;
      debug_assert_eq!(
        last.map(|c| c.is_tautology()), Some(true)
      )
    }
  }

  /// Function used when tautologizing a constraint, to forget the samples.
  fn tauto_fun(
    map: & mut PrdMap< VarValsMap<CstrSet> >, constraint: CstrIdx,
    pred: PrdIdx, args: & VarVals
  ) -> Res<()> {
    let mut remove = false ;
    let was_there = map[pred].get_mut(& args).map(
      |set| {
        let was_there = set.remove(& constraint) ;
        remove = set.is_empty() ;
        was_there
      }
    ).unwrap_or(false) ;
    if ! was_there {
      bail!("tautology treatment failed: unknown arguments {}", args)
    }
    if remove {
      let prev = map[pred].remove(& args) ;
      debug_assert! { prev.is_some() }
    }
    Ok(())
  }

  /// Tautologizes a constraint and removes the links with its samples in
  /// the map.
  pub fn tautologize(
    & mut self, constraint: CstrIdx
  ) -> Res<()> {
    scoped! {
      let map = & mut self.map ;
      self.constraints[constraint].tautologize(
        |pred, args| Self::tauto_fun(map, constraint, pred, & args)
      ).chain_err(
        || "in tautologize"
      ) ? ;
    }
    self.cstr_info.forget(constraint) ;
    Ok(())
  }




  /// Retrieves all args `s` from `self.map` such that `args.subsumes(s)`
  fn remove_subs(
    & mut self, pred: PrdIdx, args: & VarVals
  ) -> Option<CstrSet> {
    if ! conf.teacher.partial || ! args.is_partial() {
      return self.map[pred].remove(args)
    }
    profile! { self tick "remove_sub" }
    let mut res = None ;
    self.map[pred].retain(
      |s, set| if args.subsumes(s) {
        res.get_or_insert_with(
          || CstrSet::with_capacity(set.len())
        ).extend( set.drain() ) ;
        false
      } else {
        true
      }
    ) ;
    profile! { self mark "remove_sub" }
    res
  }



  /// Checks whether the data is contradictory.
  pub fn is_unsat(& self) -> Option<
    Vec<(PrdIdx, VarVals)>
  > {
    for (pred, samples) in self.pos.index_iter() {
      for sample in samples {
        for neg in & self.neg[pred] {
          if sample.is_complementary(neg) {
            return Some(
              vec![(pred, sample.clone()), (pred, neg.clone())]
            )
          }
        }
      }
    }
    None
  }




  /// Propagates all staged samples.
  ///
  /// Returns the number of pos/neg samples added.
  pub fn propagate(& mut self) -> Res<(usize, usize)> {

    profile! { self tick "propagate" }

    // println!("{}", self.to_string_info(& ()).unwrap()) ;

    let (mut pos_cnt, mut neg_cnt) = (0, 0) ;

    // This is used to remember new constraints from this propagation phase, to
    // check for useless constraints after propagation is over.
    let mut modded_constraints = CstrSet::new() ;

    'propagate: while let Some(
      (pred, mut argss, pos)
    ) = self.staged.pop() {

      macro_rules! target_set {
        () => (
          if pos {
            & mut self.pos[pred]
          } else {
            & mut self.neg[pred]
          }
        ) ;
      }

      profile! { self tick "propagate", "filtering" }
      // Only keep those that are actually new.
      argss.retain(
        |s| {
          // Note that we're removing elements of the target set that are
          // subsumed by `s`.
          let (subsumed, rmed) = s.set_subsumed_rm(
            target_set!()
          ) ;
          if subsumed {
            debug_assert! { rmed == 0 }
            false
          } else {
            let is_new = target_set!().insert(s.clone()) ;
            debug_assert! { is_new }
            true
          }
        }
      ) ;
      profile! { self mark "propagate", "filtering" }

      // Move on if nothing's left.
      if argss.is_empty() { continue 'propagate }

      if pos {
        pos_cnt += argss.len()
      } else {
        neg_cnt += argss.len()
      }

      // Update the constraints that mention these new `pos` samples.
      for args in argss {
        profile! {
          self "partial samples" => add {
            if args.is_partial() { 1 } else { 0 }
          }
        }

        if let Some(constraints) = self.remove_subs(pred, & args) {

          profile! { self tick "propagate", "cstr update" }
          for constraint_idx in constraints {
            let constraint = & mut self.constraints[constraint_idx] ;
            let map = & mut self.map ;

            let tautology = constraint.force_sample(
              pred, & args, pos, |pred, args| Self::tauto_fun(
                map, constraint_idx, pred, & args
              )
            ).chain_err(
              || "in propagate"
            ) ? ;

            if tautology {
              // Tautology, discard.
              self.cstr_info.forget(constraint_idx)
            } else {

              match constraint.try_trivial() {
                Either::Left((Sample { pred, args }, pos)) => {
                  // Constraint is trivial: unlink and forget.
                  if let Some(set) = map[pred].get_mut(& args) {
                    let was_there = set.remove(& constraint_idx) ;
                    debug_assert! { was_there }
                  }
                  self.cstr_info.forget(constraint_idx) ;
                  // Stage the consequence of the triviality.
                  self.staged.add(pred, args, pos) ;
                },
                Either::Right(false) => {
                  // Otherwise, the constraint was modified and we're keeping
                  // it.
                  self.cstr_info.register_modded(
                    constraint_idx, & constraint
                  ) ? ;
                  modded_constraints.insert(constraint_idx) ;
                }
                Either::Right(true) => unsat!(
                  "by `true => false` in constraint (data, propagate)"
                ),
              }
            }
          }
          profile! { self mark "propagate", "cstr update" }

          for constraint in modded_constraints.drain() {
            if ! self.constraints[constraint].is_tautology()
            && ! self.cstr_useful(constraint).chain_err(
              || "in propagate"
            ) ? {
              self.tautologize(constraint) ?
            }
          }

        }
      }
    }

    profile! { self tick "propagate", "check shrink" }
    self.check("after propagate") ? ;

    self.shrink_constraints() ;
    profile! { self mark "propagate", "check shrink" }

    profile! { self mark "propagate" }

    Ok((pos_cnt, neg_cnt))
  }



  /// Length of positive/negative samples and constraints.
  pub fn metrics(& self) -> (usize, usize, usize) {
    (
      self.pos.iter().fold(0, |acc, samples| acc + samples.len()),
      self.neg.iter().fold(0, |acc, samples| acc + samples.len()),
      self.constraints.len()
    )
  }



  /// Adds a constraint, creates links, no trivial/tautology checks.
  ///
  /// - should only be called by `add_cstr`
  /// - shrinks the constraints first
  /// - registers the constraint in the constraint info structure
  /// - performs the usefulness check
  fn raw_add_cstr(& mut self, constraint: Constraint) -> Res<bool> {
    self.shrink_constraints() ;
    let cstr_index = self.constraints.next_index() ;

    // Create links.
    if let Some(lhs) = constraint.lhs() {
      for (pred, argss) in lhs {
        for args in argss {
          let is_new = self.map[* pred].entry( args.clone() ).or_insert_with(
            || CstrSet::with_capacity(17)
          ).insert(cstr_index) ;
          debug_assert! { is_new }
        }
      }
    }
    if let Some( & Sample { pred, ref args } ) = constraint.rhs() {
      let is_new = self.map[pred].entry( args.clone() ).or_insert_with(
        || CstrSet::with_capacity(17)
      ).insert(cstr_index) ;
      debug_assert! { is_new }
    }

    self.cstr_info.register_modded(
      cstr_index, & constraint
    ) ? ;

    self.constraints.push(constraint) ;

    if ! self.cstr_useful(cstr_index).chain_err(
      || "in raw_add_cstr"
    ) ? {
      self.tautologize(cstr_index) ? ;
      Ok(false)
    } else {
      Ok(true)
    }
  }

  /// Adds a sample or a constraint.
  pub fn add_data(
    & mut self, clause: ClsIdx,
    mut lhs: Vec< (PrdIdx, RVarVals) >, rhs: Option<(PrdIdx, RVarVals)>,
  ) -> Res<()> {

    let rhs = match rhs {

      Some((pred, sample)) => if lhs.is_empty() {
        // Positive sample.
        self.add_raw_pos(clause, pred, sample) ;
        return Ok(())
      } else {
        // Constraint.
        Some((pred, sample))
      },

      None => if lhs.len() == 1 {
        // Negative sample.
        let (pred, sample) = lhs.pop().expect(
          "failed pop on vector of length 1"
        ) ;
        debug_assert_eq! { lhs.len(), 0 }
        self.add_raw_neg(clause, pred, sample) ;
        return Ok(())
      } else {
        // Constraint.
        None
      }

    } ;

    // Only reachable if we're not adding a pos/neg sample, or the input isn't
    // legal.
    debug_assert! {
      lhs.len() > 1 || (
        lhs.len() == 1 && rhs.is_some()
      )
    }

    self.add_cstr(clause, lhs, rhs) ? ;

    Ok(())
  }


  /// Prunes the lhs and the rhs of a constraint.
  ///
  /// Removes samples that are known to be true/false. Returns `None` if the
  /// constraint is trivial.
  pub fn prune_cstr(
    & mut self, lhs: Vec<(PrdIdx, RVarVals)>, rhs: Option<(PrdIdx, RVarVals)>
  ) -> Res< Option<(
    PrdHMap<VarValsSet>, Option<Sample>
  )> > {
    let mut nu_lhs = PrdHMap::with_capacity( lhs.len() ) ;

    // Look at the lhs and remove stuff we know is true.
    'lhs_iter: for (pred, args) in lhs {
      let (args, is_new) = var_to::vals::new_is_new( args ) ;

      // If no partial examples and sample is new, no need to check anything.
      if conf.teacher.partial || ! is_new {
        if args.set_subsumed(& self.pos[pred]) {
          // Positive, skip.
          continue 'lhs_iter
        } else if args.set_subsumed(& self.neg[pred]) {
          // Negative, constraint is trivial.
          profile! { self mark "add cstr", "pre-checks" }
          profile! { self "trivial constraints" => add 1 }
          return Ok(None)
        }
      }

      let set = nu_lhs.entry(pred).or_insert_with(VarValsSet::new) ;

      // Partial samples are not allowed in constraints, no subsumption
      // check in set.
      set.insert(args) ;
      ()
    }

    let nu_rhs = if let Some((pred, args)) = rhs {
      let (args, is_new) = var_to::vals::new_is_new( args.clone() ) ;

      let args = if conf.teacher.partial || ! is_new {
        if args.set_subsumed(& self.pos[pred]) {
          profile! { self mark "add cstr", "pre-checks" }
          profile! { self "trivial constraints" => add 1 }
          // Positive, constraint is trivial.
          return Ok(None)
        } else if args.set_subsumed(& self.neg[pred]) {
          // Negative, ignore.
          None
        } else {
          Some(args)
        }
      } else {
        Some(args)
      } ;

      if let Some(args) = args.as_ref() {
        // Subsumed by lhs?
        if let Some(argss) = nu_lhs.get(& pred) {
          // Partial samples are not allowed in constraints, no subsumption
          // check.
          if argss.contains(& args) {
            profile! { self mark "add cstr", "pre-checks" }
            profile! { self "trivial constraints" => add 1 }
            // Trivially implied by lhs.
            return Ok(None)
          }
        }
      }

      args.map(|args| Sample { pred, args })
    } else {
      None
    } ;

    nu_lhs.shrink_to_fit() ;

    Ok( Some((nu_lhs, nu_rhs)) )
  }


  /// Adds a constraint.
  ///
  /// Returns `true` and if something new was added.
  ///
  /// The `clause` input is necessary for unsat core extraction.
  ///
  /// Partial samples ARE NOT ALLOWED in constraints.
  ///
  /// - propagates staged samples beforehand
  pub fn add_cstr(
    & mut self, _clause: ClsIdx,
    lhs: Vec<(PrdIdx, RVarVals)>, rhs: Option<(PrdIdx, RVarVals)>
  ) -> Res< bool > {
    profile!(
      self wrap { self.propagate() }
      "add cstr", "pre-propagate"
    ) ? ;

    if_log! { @4
      log! { @4 "adding constraint" }
      if let Some((pred, args)) = rhs.as_ref() {
        log! { @4 "({} {})", self.instance[* pred], args }
      } else {
        log! { @4 "false" }
      }
      let mut pref = "<=" ;
      for (pred, args) in & lhs {
          log! { @4 "{} ({} {})", pref, self.instance[* pred], args }
          pref = "  "
      }
    }

    profile! { self tick "add cstr", "pre-checks" }

    let (nu_lhs, nu_rhs) = if let Some(res) = self.prune_cstr(lhs, rhs) ? {
      res
    } else {
      return Ok(false)
    } ;

    let mut constraint = Constraint::new(nu_lhs, nu_rhs) ;
    constraint.check().chain_err(
      || format!(
        "while checking {}", constraint.to_string_info(
          self.instance.preds()
        ).unwrap()
      )
    ) ? ;
    debug_assert! { ! constraint.is_tautology() }

    profile! { self mark "add cstr", "pre-checks" }

    match constraint.try_trivial() {
      Either::Left((Sample { pred, args }, pos)) => {
        let is_new = self.staged.add(pred, args, pos) ;
        Ok(is_new)
      },
      Either::Right(false) => {
        // Handles linking and constraint info registration.
        let is_new = profile!(
          self wrap { self.raw_add_cstr(constraint) }
          "add cstr", "raw"
        ) ? ;

        self.check("after add_cstr") ? ;

        Ok(is_new)
      },
      Either::Right(true) => unsat!(
        "by `true => false` in constraint (data, add_cstr)"
      ),
    }
  }










  /// Sets all the unknown data of a given predicate to `pos`, and
  /// propagates.
  ///
  /// This is only used by learner(s).
  pub fn force_pred(
    & mut self, pred: PrdIdx, pos: bool
  ) -> Res<()> {
    profile! { self tick "force pred", "pre-checks" }
    let mut modded_constraints = CstrSet::new() ;
    scoped! {
      let map = & mut self.map ;
      let mut constraints = CstrSet::new() ;
      for (_, cs) in map[pred].drain() {
        for c in cs {
          constraints.insert(c) ;
        }
      }
      for constraint in constraints {
        let tautology = self.constraints[constraint].force(
          pred, pos, |pred, args| Self::tauto_fun(
            map, constraint, pred, & args
          )
        ) ? ;

        if tautology {
          // Tautology, discard.
          self.cstr_info.forget(constraint)
        } else {

          match self.constraints[constraint].try_trivial() {
            Either::Left((Sample { pred, args }, pos)) => {
              // Constraint is trivial: unlink and forget.
              if let Some(set) = map[pred].get_mut(& args) {
                let was_there = set.remove(& constraint) ;
                debug_assert! { was_there }
              }
              self.cstr_info.forget(constraint) ;
              // Stage the consequence of the triviality.
              self.staged.add(pred, args, pos) ;
            },
            Either::Right(false) => {
              // Otherwise, the constraint was modified and we're keeping it.
              self.cstr_info.register_modded(
                constraint, & self.constraints[constraint]
              ) ? ;
              modded_constraints.insert(constraint) ;
            },
            Either::Right(true) => unsat!(
              "by `true => false` in constraint (data, force_pred)"
            ),
          }
        }
      }
    }

    for constraint in modded_constraints.drain() {
      if ! self.constraints[constraint].is_tautology()
      && ! self.cstr_useful(constraint) ? {
        self.tautologize(constraint) ?
      }
    }
    profile! { self mark "force pred", "pre-checks" }

    profile!(
      self wrap { self.propagate() }
      "force pred", "propagate"
    ) ? ;

    Ok(())
  }

  /// The projected data for some predicate.
  pub fn data_of(& self, pred: PrdIdx) -> CData {
    profile! { self tick "data of" }
    let unc_set = & self.map[pred] ;
    let pos_set = & self.pos[pred] ;
    let neg_set = & self.neg[pred] ;
    let (mut pos, mut neg, mut unc) = (
      Vec::with_capacity( pos_set.len() ),
      Vec::with_capacity( neg_set.len() ),
      Vec::with_capacity( unc_set.len() )
    ) ;
    for sample in pos_set.iter() {
      pos.push( sample.clone() )
    }
    for sample in neg_set.iter() {
      neg.push( sample.clone() )
    }
    for (sample, set) in unc_set.iter() {
      if ! set.is_empty() {
        unc.push( sample.clone() )
      }
    }
    profile! { self mark "data of" }
    CData::new(pos, neg, unc)
  }


  /// Applies the classification represented by the data to some projected
  /// data.
  ///
  /// This is used when backtracking in the learner. The assumption is that all
  /// arguments in `data` are in `self`. That is, there is no subsumption
  /// checking.
  pub fn classify(
    & self, pred: PrdIdx, data: & mut CData
  ) {
    profile!{
      self wrap {
        data.classify(
          |sample| if self.pos[pred].contains(sample) {
            Some(true)
          } else if self.neg[pred].contains(sample) {
            Some(false)
          } else {
            None
          }
        )
      } "classify"
    }
  }





  /// Checks the state of the data. Does nothing in release.
  ///
  /// Checks:
  ///
  /// - no positive or negative examples staged
  /// - set of modified clauses makes sense
  /// - positive / negative samples are not redundant
  /// - no positive / negative data is linked to some constraints
  /// - `(pred, sample, constraint)` in [`self.map`][map] implies `(pred
  ///   sample)` in [`self.constraints`][cstrs]`[constraint]`'s lhs or rhs
  /// - ...and conversely
  /// - no redundant constraints
  ///
  /// [map]: #structfield.map (map field)
  /// [cstrs]: #structfield.constraints (constraints field)
  #[cfg(debug_assertions)]
  pub fn check(& self, blah: & 'static str) -> Res<()> {
    self.check_internal().chain_err(
      || self.string_do(& (), |s| s.to_string()).unwrap()
    ).chain_err(|| blah)
  }


  /// Checks the data is consistent.
  #[cfg(debug_assertions)]
  fn check_internal(& self) -> Res<()> {
    if ! self.staged.is_empty() {
      bail!("there are staged samples...")
    }

    self.check_modded() ? ;
    self.check_neg() ? ;
    self.check_pos() ? ;
    self.check_constraint_data() ? ;
    self.check_redundant() ? ;


    macro_rules! constraint_map {
      ($cstr:expr => |$pred:ident, $sample:ident| $body:expr) => (
        if let Some(lhs) = $cstr.lhs() {
          for (pred, samples) in lhs {
            let $pred = * pred ;
            for $sample in samples { $body }
          }
        }
        if let Some(
          & Sample { pred: $pred, args: ref $sample }
        ) = $cstr.rhs() {
          $body
        }
      ) ;
    }

    // Constraints are consistent with map.
    for (idx, constraint) in self.constraints.index_iter() {
      constraint_map!{
        constraint => |prd, sample| {
          if ! self.map[prd].get(sample).map(
            |set| set.contains(& idx)
          ).unwrap_or(false) {
            bail!(
              "{}\n({} {}) appears in constraint #{} \
              but is not registered in map",
              self.string_do(& (), |s| s.to_string()).unwrap(),
              self.instance[prd], sample, idx
            )
          }
        }
      }
    }

    // Map is consistent with constraints.
    for (pred, map) in self.map.index_iter() {
      for (sample, set) in map {
        for idx in set {
          let c = & self.constraints[* idx] ;
          let mut okay = false ;
          constraint_map! {
            c => |p, s| if p == pred && s == sample {
              okay = true
            }
          }
          if ! okay {
            bail!(
              "{}\n({} {}) registered in map for constraint #{} \
              but does not appear in this constraint",
              self.string_do(& (), |s| s.to_string()).unwrap(),
              self.instance[pred], sample, idx
            )
          }
        }
      }
    }

    for constraint in & self.constraints {
      constraint.check().chain_err(
        || format!(
          "while checking {}", constraint.to_string_info(
            self.instance.preds()
          ).unwrap()
        )
      ) ?
    }

    Ok(())
  }

  /// Checks modded constraints.
  #[cfg(debug_assertions)]
  fn check_modded(& self) -> Res<()> {
    for constraint in self.cstr_info.modded() {
      if * constraint >= self.constraints.len()
      || self.constraints[* constraint].is_tautology() {
        bail!("modded_constraints is out of sync")
      }
    }
    Ok(())
  }

  /// Checks negative constraints.
  #[cfg(debug_assertions)]
  fn check_neg(& self) -> Res<()> {
    for constraint in self.cstr_info.neg() {
      if * constraint >= self.constraints.len() {
        bail!("neg_constraints is out of sync")
      }
      if self.constraints[* constraint].rhs().is_some() {
        bail!(
          "neg_constraints contains non-negative constraint {}",
          self.constraints[* constraint].to_string_info(
            self.instance.preds()
          ).unwrap()
        )
      }
      if self.constraints[* constraint].is_tautology() {
        bail!(
          "neg_constraints contains tautology {}",
          self.constraints[* constraint].to_string_info(
            self.instance.preds()
          ).unwrap()
        )
      }
    }
    for (index, constraint) in self.constraints.index_iter() {
      if ! constraint.is_tautology()
      && constraint.rhs().is_none()
      && ! self.cstr_info.neg().contains(& index) {
        bail!(
          "unregistered negative constraint {}",
          constraint.to_string_info(
            self.instance.preds()
          ).unwrap()
        )
      }
    }
    Ok(())
  }

  /// Checks positive constraints.
  #[cfg(debug_assertions)]
  fn check_pos(& self) -> Res<()> {
    for set in & self.pos {
      for sample in set {
        for s in set {
          if sample.subsumes(s)
          && sample != s {
            bail!(
              "positive samples are redundant: {} => {}", sample, s
            )
          }
        }
      }
    }
    for set in & self.neg {
      for sample in set {
        for s in set {
          if sample.subsumes(s)
          && sample != s {
            bail!(
              "negative samples are redundant: {} => {}", sample, s
            )
          }
        }
      }
    }
    Ok(())
  }

  /// Checks pos/neg data does not appear in constraints.
  #[cfg(debug_assertions)]
  fn check_constraint_data(& self) -> Res<()> {
    for pred in self.instance.pred_indices() {
      let pos = self.pos[pred].iter().map(
        |p| (p, "positive")
      ) ;
      let neg = self.neg[pred].iter().map(
        |n| (n, "negative")
      ) ;
      for (sample, polarity) in pos.chain(neg) {
        for (s, set) in & self.map[pred] {
          if sample.subsumes(s) {
            let mut s: String = "{".into() ;
            for idx in set {
              s.push_str(& format!(" {}", idx))
            }
            s.push_str(" }") ;
            bail!(
              "({} {}) is {} but appears in constraint(s) {}",
              self.instance[pred], sample, polarity, s
            )
          }
        }
      }
    }
    Ok(())
  }

  /// Checks that there are no redundant constraints.
  #[cfg(debug_assertions)]
  fn check_redundant(& self) -> Res<()> {
    let mut constraint_iter = self.constraints.iter() ;
    while let Some(c_1) = constraint_iter.next() {
      c_1.check() ? ;
      for c_2 in constraint_iter.clone() {
        if ! c_1.is_tautology()
        && ! c_2.is_tautology()
        && c_1.compare(c_2)?.is_some() {
          bail!(
            format!(
              "found two redundant constraints:\n{}\n{}",
              c_1.string_do(
                & self.instance.preds(), |s| s.to_string()
              ).unwrap(),
              c_2.string_do(
                & self.instance.preds(), |s| s.to_string()
              ).unwrap(),
            )
          )
        }
      }
    }
    Ok(())
  }


  #[cfg(not(debug_assertions))]
  #[inline]
  pub fn check(& self, _: & 'static str) -> Res<()> { Ok(()) }

}

impl<'a> PebcakFmt<'a> for Data {
  type Info = & 'a () ;
  fn pebcak_err(& self) -> ErrorKind {
    "during data pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, _: & 'a ()
  ) -> IoRes<()> {
    let map = self.instance.preds() ;
    write!(w, "pos (") ? ;
    for (pred, set) in self.pos.index_iter() {
      for args in set.iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in args.iter() {
          write!(w, " {}", arg)?
        }
        write!(w, ")") ?
      }
    }
    write!(w, "\n) neg (") ? ;
    for (pred, set) in self.neg.index_iter() {
      for args in set.iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in args.iter() {
          write!(w, " {}", arg)?
        }
        write!(w, ")") ?
      }
    }
    write!(w, "\n) constraints (") ? ;
    for (index, cstr) in self.constraints.index_iter() {
      write!(w, "\n  {: >3} | ", index) ? ;
      if cstr.is_tautology() {
        write!(w, "_") ?
      } else {
        cstr.pebcak_io_fmt(w, map) ?
      }
    }
    write!(w, "\n) constraint map(") ? ;
    for (pred, samples) in self.map.index_iter() {
      for (sample, set) in samples.iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in sample.iter() {
          write!(w, " {}", arg) ?
        }
        write!(w, ") ->") ? ;
        for pred in set.iter() {
          write!(w, " {}", pred) ?
        }
      }
    }
    write!(w, "\n) positive examples staged (") ? ;
    for (pred, set) in & self.staged.pos {
      write!(w, "\n  {} |", self.instance[* pred]) ? ;
      for sample in set {
        write!(w, " ({})", sample) ?
      }
    }
    writeln!(w, "\n) negative examples staged (") ? ;
    for (pred, set) in & self.staged.neg {
      write!(w, "  {} |", self.instance[* pred]) ? ;
      for sample in set {
        write!(w, " ({})", sample) ?
      }
      writeln!(w) ?
    }
    writeln!(w, ") modded (") ? ;
    for cstr in self.cstr_info.modded() {
      writeln!(w, "  #{}", cstr) ?
    }
    writeln!(w, ") neg (") ? ;
    for cstr in self.cstr_info.neg() {
      writeln!(w, "  #{}", cstr) ?
    }
    writeln!(w, ")") ? ;
    // if let Some(graph) = self.graph.as_ref() {
    //   graph.write(w, "", & self.instance) ? ;
    // }
    Ok(())
  }
}




/// Tiny internal structure storing samples for future propagation.
#[derive(Clone)]
struct Staged {
  pos: PrdHMap<VarValsSet>,
  neg: PrdHMap<VarValsSet>,
}
impl Staged {
  /// Constructor.
  pub fn with_capacity(capa: usize) -> Self {
    Staged {
      pos: PrdHMap::with_capacity(capa),
      neg: PrdHMap::with_capacity(capa),     
    }
  }

  /// True if empty.
  #[allow(dead_code)]
  pub fn is_empty(& self) -> bool {
    self.pos.is_empty() && self.neg.is_empty()
  }

  /// Returns a predicate used as a key in `pos` or `neg`.
  ///
  /// # Guarantees
  ///
  /// - the predicate returned is in `pos` (`neg`) if the boolean is true
  ///   (false)
  fn get_pred(& self) -> Option<(PrdIdx, bool)> {
    if let Some(pred) = self.pos.keys().next() {
      Some( (* pred, true) )
    } else if let Some(pred) = self.neg.keys().next() {
      Some( (* pred, false) )
    } else {
      None
    }
  }

  /// Returns some staged arguments for a predicate.
  ///
  /// The boolean indicates whether the sample is positive.
  pub fn pop(& mut self) -> Option<(PrdIdx, VarValsSet, bool)> {
    if let Some((pred, pos)) = self.get_pred() {
      if let Some(argss) = {
        if pos {
          self.pos.remove(& pred)
        } else {
          self.neg.remove(& pred)
        }
      } {
        Some((pred, argss, pos))
      } else {
        fail_with!(
          "In `Staged`: illegal `get_pred` result"
        )
      }
    } else {
      None
    }
  }

  /// Adds a sample.
  pub fn add(& mut self, pred: PrdIdx, args: VarVals, pos: bool) -> bool {
    let map = if pos {
      & mut self.pos
    } else {
      & mut self.neg
    } ;
    let set = map.entry(pred).or_insert_with(
      || VarValsSet::with_capacity(11)
    ) ;
    let (subsumed, rmed) = args.set_subsumed_rm(set) ;
    if subsumed {
      debug_assert_eq! { rmed, 0 }
      return false
    }

    let is_new = set.insert(args) ;
    // We checked `args` is not subsumed already, so it's necessarily new.
    debug_assert! { is_new }
    true
  }

  /// Adds a positive sample.
  #[inline]
  pub fn add_pos(& mut self, pred: PrdIdx, args: VarVals) -> bool {
    self.add(pred, args, true)
  }

  /// Adds a negative sample.
  #[inline]
  pub fn add_neg(& mut self, pred: PrdIdx, args: VarVals) -> bool {
    self.add(pred, args, false)
  }
}




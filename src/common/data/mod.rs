// use hashconsing::{ HConsed } ;

use common::* ;
use learning::ice::data::CData ;

pub mod args ;
pub mod sample ;
pub mod constraint ;
mod info ;

pub use self::args::{ RArgs, Args, ArgsSet, ArgsMap } ;
use self::args::{ SubsumeExt, ArgFactory, new_factory } ;
pub use self::sample::{ Sample } ;
pub use self::constraint::Constraint ;
use self::info::CstrInfo ;





/// Structure manipulating unprojected learning data.
///
/// Cannot create new samples as it does not contain the factory. This is the
/// structure manipulated by learners.
#[derive(Clone)]
pub struct Data {
  /// Instance, only used for printing.
  pub instance: Arc<Instance>,
  /// Positive examples.
  pub pos: PrdMap< ArgsSet >,
  /// Negative examples.
  pub neg: PrdMap< ArgsSet >,
  /// Constraints.
  pub constraints: CstrMap<Constraint>,

  /// Map from samples to constraints.
  map: PrdMap< ArgsMap<CstrSet> >,
  /// Argument factory.
  factory: ArgFactory,
  /// Stores pos/neg samples temporarily before they're added.
  staged: Staged,
  /// Constraint info.
  cstr_info: CstrInfo,
  /// Profiler.
  _profiler: Profiler,
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
      map.push( ArgsMap::with_capacity(103) ) ;
      pos.push( ArgsSet::with_capacity(103) ) ;
      neg.push( ArgsSet::with_capacity(103) ) ;
    }

    let constraints = CstrMap::with_capacity(103) ;
    Data {
      instance, pos, neg, constraints, map,
      factory: new_factory(),
      staged: Staged::with_capacity(pred_count),
      cstr_info: CstrInfo::new(),
      _profiler: Profiler::new(),
    }
  }

  /// Accessor for the map from samples to constraints.
  pub fn map(& self) -> & PrdMap< ArgsMap<CstrSet> > {
    & self.map
  }

  /// Destroys the data and returns profiling info.
  pub fn destroy(self) -> Profiler {
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
      "{}",
      self.constraints[c].to_string_info(
        self.instance.preds()
      ).unwrap()
    )
  }

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
    self.propagate() ? ;
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
    self.propagate()
  }


  /// Checks whether a constraint is useful.
  ///
  /// Remove all constraints that this constraint makes useless, including the
  /// one(s) it is equal to.
  pub fn cstr_useful(& mut self, index: CstrIdx) -> Res<bool> {
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
        Some(Less) => useful = false,
        // Not comparable.
        None => (),
      }
    }
    profile! { self "useless constraints" => add 1 }

    Ok(useful)
  }


  /// Adds a new positive example.
  ///
  /// Does not propagate.
  pub fn add_raw_pos(& mut self, pred: PrdIdx, args: RArgs) -> bool {
    let (args, _) = self.mk_sample(args) ;
    self.staged.add_pos(pred, args)
  }

  /// Adds a new negative example.
  ///
  /// Does not propagate.
  pub fn add_raw_neg(& mut self, pred: PrdIdx, args: RArgs) -> bool {
    let (args, _) = self.mk_sample(args) ;
    self.staged.add_neg(pred, args)
  }



  /// Adds a new positive example.
  ///
  /// Does not propagate.
  pub fn add_pos(& mut self, pred: PrdIdx, args: Args) -> bool {
    self.staged.add_pos(pred, args)
  }

  /// Adds a new negative example.
  ///
  /// Does not propagate.
  pub fn add_neg(& mut self, pred: PrdIdx, args: Args) -> bool {
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
    map: & mut PrdMap< ArgsMap<CstrSet> >, constraint: CstrIdx,
    pred: PrdIdx, args: Args
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
        |pred, args| Self::tauto_fun(map, constraint, pred, args)
      ) ? ;
    }
    self.cstr_info.forget(constraint) ;
    Ok(())
  }




  /// Retrieves all args `s` from `self.map` such that `args.subsumes(s)`
  fn remove_subs(
    & mut self, pred: PrdIdx, args: & Args
  ) -> Option<CstrSet> {
    if ! conf.teacher.partial || ! args.is_partial() {
      return self.map[pred].remove(args)
    }
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
    res
  }




  /// Propagates all staged samples.
  ///
  /// Returns the number of pos/neg samples added.
  pub fn propagate(& mut self) -> Res<(usize, usize)> {

    profile! { self tick "sample_propagate" }

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

      // Move on if nothing's left.
      if argss.is_empty() { continue 'propagate }

      if pos {
        pos_cnt += argss.len()
      } else {
        neg_cnt += argss.len()
      }

      // Update the constraints that mention these new `pos` samples.
      for args in argss {

        if let Some(constraints) = self.remove_subs(pred, & args) {

          for constraint_idx in constraints {
            let blah = self.to_string_info(& ()).unwrap() ;
            let constraint = & mut self.constraints[constraint_idx] ;
            let preds = self.instance.preds() ;
            let map = & mut self.map ;

            let tautology = constraint.force_sample(
              pred, & args, pos, |pred, args| Self::tauto_fun(
                map, constraint_idx, pred, args
              )
            ).chain_err(
              || format!(
                "while forcing ({} {}) in {}",
                preds[pred], args,
                constraint.to_string_info(preds).unwrap()
              )
            ).chain_err(
              || format!(
                "in {}", blah
              )
            ) ? ;

            if tautology {
              // Tautology, discard.
              self.cstr_info.forget(constraint_idx)
            } else if let Some((
              Sample { pred, args }, pos
            )) = constraint.is_trivial() ? {
              // Constraint is trivial: unlink and forget.
              if let Some(set) = map[pred].get_mut(& args) {
                let was_there = set.remove(& constraint_idx) ;
                debug_assert! { was_there }
              }
              self.cstr_info.forget(constraint_idx) ;
              // Stage the consequence of the triviality.
              self.staged.add(pred, args, pos) ;
            } else {
              // Otherwise, the constraint was modified and we're keeping it.
              self.cstr_info.register_modded(
                constraint_idx, & constraint
              ) ? ;
              modded_constraints.insert(constraint_idx) ;
            }
          }

          for constraint in modded_constraints.drain() {
            if ! self.constraints[constraint].is_tautology() {
              if ! self.cstr_useful(constraint).chain_err(
                || "in propagate"
              ) ? {
                self.tautologize(constraint) ?
              }
            }
          }

        }
      }
    }

    profile! { self mark "sample_propagate" }

    self.check("after propagate") ? ;

    self.shrink_constraints() ;

    Ok((pos_cnt, neg_cnt))
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

  /// Creates a new sample. Returns true if it's new.
  fn mk_sample(
    & mut self, args: RArgs
  ) -> (Args, bool) {
    use hashconsing::HConser ;
    self.factory.mk_is_new( args.into() )
  }


  // /// Checks whether a constraint is redundant.
  // ///
  // /// Removes all constraints for which this constraint is more general.
  // fn cstr_redundant_rm(
  //   & mut self, constraint: CstrIdx
  // ) -> bool {

  // }


  /// Adds a constraint.
  ///
  /// Partial samples ARE NOT ALLOWED in constraints.
  ///
  /// - propagates staged samples beforehand
  pub fn add_cstr(
    & mut self, lhs: Vec<(PrdIdx, RArgs)>, rhs: Option<(PrdIdx, RArgs)>
  ) -> Res<bool> {
    self.propagate() ? ;

    let mut nu_lhs = PrdHMap::with_capacity( lhs.len() ) ;

    // Look at the lhs and remove stuff we know is true.
    'lhs_iter: for (pred, args) in lhs {
      let (args, is_new) = self.mk_sample(args) ;

      // If no partial examples and sample is new, no need to check anything.
      if conf.teacher.partial || ! is_new {
        if args.set_subsumed(& self.pos[pred]) {
          // Positive, skip.
          continue 'lhs_iter
        } else if args.set_subsumed(& self.neg[pred]) {
          // Negative, constraint is trivial.
          return Ok(false)
        }
      }

      let set = nu_lhs.entry(pred).or_insert_with(
        || ArgsSet::new()
      ) ;

      // Partial samples are not allowed in constraints, no subsumption
      // check in set.
      set.insert(args) ;
      ()
    }

    let nu_rhs = if let Some((pred, args)) = rhs {
      // Not a look, just makes early return easier thanks to breaking.
      'get_rhs: loop {
        let (args, is_new) = self.mk_sample(args) ;

        // If no partial examples and sample is new, no need to check anything.
        if conf.teacher.partial || ! is_new {
          if args.set_subsumed(& self.pos[pred]) {
            // Positive, constraint is trivial.
            return Ok(false)
          } else if args.set_subsumed(& self.neg[pred]) {
            // Negative, ignore.
            break 'get_rhs None
          }
        }

        // Subsumed by lhs?
        if let Some(argss) = nu_lhs.get(& pred) {
          // Partial samples are not allowed in constraints, no subsumption
          // check.
          if argss.contains(& args) {
            // Trivially implied by lhs.
            return Ok(false)
          }
        }

        break 'get_rhs Some( Sample { pred, args } )
      }
    } else {
      None
    } ;

    nu_lhs.shrink_to_fit() ;

    let mut constraint = Constraint::new(nu_lhs, nu_rhs) ;
    constraint.check().chain_err(
      || format!(
        "while checking {}", constraint.to_string_info(
          self.instance.preds()
        ).unwrap()
      )
    ) ? ;
    debug_assert! { ! constraint.is_tautology() }

    if let Some((Sample { pred, args }, pos)) = constraint.is_trivial() ? {
      let is_new = self.staged.add(pred, args, pos) ;
      Ok(is_new)
    } else {

      // Handles linking and constraint info registration.
      let is_new = self.raw_add_cstr(constraint) ? ;

      self.check("after add_cstr") ? ;

      Ok(is_new)
    }
  }










  /// Sets all the unknown data of a given predicate to `pos`, and
  /// propagates.
  ///
  /// This is only used by learner(s).
  pub fn force_pred(
    & mut self, pred: PrdIdx, pos: bool
  ) -> Res<()> {
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
            map, constraint, pred, args
          )
        ) ? ;

        if tautology {
          // Tautology, discard.
          self.cstr_info.forget(constraint)
        } else if let Some((
          Sample { pred, args }, pos
        )) = self.constraints[constraint].is_trivial() ? {
          // Constraint is trivial: unlink and forget.
          if let Some(set) = map[pred].get_mut(& args) {
            let was_there = set.remove(& constraint) ;
            debug_assert! { was_there }
          }
          self.cstr_info.forget(constraint) ;
          // Stage the consequence of the triviality.
          self.staged.add(pred, args, pos) ;
        } else {
          // Otherwise, the constraint was modified and we're keeping it.
          self.cstr_info.register_modded(
            constraint, & self.constraints[constraint]
          ) ? ;
          modded_constraints.insert(constraint) ;
        }
      }
    }

    for constraint in modded_constraints.drain() {
      if ! self.constraints[constraint].is_tautology()
      && ! self.cstr_useful(constraint) ? {
        self.tautologize(constraint) ?
      }
    }

    self.propagate() ? ;

    Ok(())
  }

  /// The projected data for some predicate.
  pub fn data_of(& self, pred: PrdIdx) -> CData {
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
    data.classify(
      |sample| if self.pos[pred].contains(sample) {
        Some(true)
      } else if self.neg[pred].contains(sample) {
        Some(false)
      } else {
        None
      }
    )
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
  #[cfg(debug_assertions)]
  fn check_internal(& self) -> Res<()> {
    if ! self.staged.is_empty() {
      bail!("there are staged samples...")
    }

    for constraint in self.cstr_info.modded() {
      if * constraint >= self.constraints.len()
      || self.constraints[* constraint].is_tautology() {
        bail!("modded_constraints is out of sync")
      }
    }

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

    // Pos/neg data cannot appear in constraints.
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

    // No redundant constraints.
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
    write!(w, "\n) negative examples staged (\n") ? ;
    for (pred, set) in & self.staged.neg {
      write!(w, "  {} |", self.instance[* pred]) ? ;
      for sample in set {
        write!(w, " ({})", sample) ?
      }
      write!(w, "\n") ?
    }
    write!(w, ") modded (\n") ? ;
    for cstr in self.cstr_info.modded() {
      write!(w, "  #{}\n", cstr) ?
    }
    write!(w, ") neg (\n") ? ;
    for cstr in self.cstr_info.neg() {
      write!(w, "  #{}\n", cstr) ?
    }
    write!(w, ")\n") ? ;
    Ok(())
  }
}




/// Tiny internal structure storing samples for future propagation.
#[derive(Clone)]
struct Staged {
  pos: PrdHMap<ArgsSet>,
  neg: PrdHMap<ArgsSet>,
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
    for pred in self.pos.keys() {
      return Some((* pred, true))
    }
    for pred in self.neg.keys() {
      return Some((* pred, false))
    }
    None
  }

  /// Returns some staged arguments for a predicate.
  ///
  /// The boolean indicates whether the sample is positive.
  pub fn pop(& mut self) -> Option<(PrdIdx, ArgsSet, bool)> {
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
  pub fn add(& mut self, pred: PrdIdx, args: Args, pos: bool) -> bool {
    let map = if pos {
      & mut self.pos
    } else {
      & mut self.neg
    } ;
    let set = map.entry(pred).or_insert_with(
      || HConSet::with_capacity(11)
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
  pub fn add_pos(& mut self, pred: PrdIdx, args: Args) -> bool {
    self.add(pred, args, true)
  }

  /// Adds a negative sample.
  #[inline]
  pub fn add_neg(& mut self, pred: PrdIdx, args: Args) -> bool {
    self.add(pred, args, false)
  }
}




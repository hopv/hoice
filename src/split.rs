//! Handles instance splitting.
//!
//! Used to reason separately on each positive/negative clause.

use common::* ;





/// Splits the instance if asked to do so, and solves it.
///
/// Assumes the instance is **already pre-processed**.
pub fn work(
  real_instance: Arc<Instance>, _profiler: & Profiler
) -> Res< Option<DnfCandidates> > {
  // Encodes a DNF.
  let mut model = DnfCandidates::new() ;
  let mut neg_models = PrdHMap::new() ;

  let mut pos_splitter = Splitter::new(& real_instance, true) ;

  while let Some(pre_proc_res) = profile!(
    |_profiler| wrap {
      if let Some((current, left)) = pos_splitter.info() {
        log! { @info
          "\nSplitting on positive clause {} of {}", current, left
        }
      }
      pos_splitter.next_instance()
    } "positive sub-preproc"
  ) ? {
    if let Some(prof) = pos_splitter.profiler() {
      print_stats("positive sub-preproc", prof)
    }

    let instance = match pre_proc_res {
      Either::Left(instance) => instance,
      Either::Right(maybe_model) => {
        profile! { |_profiler| "sub-systems" => add 1 }
        if let Some(_) = maybe_model {
          unimplemented!()
        } else {
          return Ok(None)
        }
      },
    } ;

    let mut neg_splitter = Splitter::new(& instance, false) ;
    debug_assert! { neg_models.is_empty() }

    while let Some(pre_proc_res) = profile!(
      |_profiler| wrap {
        if_verb! {
          if let Some((current, left)) = neg_splitter.info() {
            log! { @info
              "\nSplitting on negative clause {} of {}", current, left
            }
          }
        }
        neg_splitter.next_instance()
      } "negative sub-preproc"
    ) ? {
      if let Some(prof) = neg_splitter.profiler() {
        print_stats("negative sub-preproc", prof)
      }
      profile! { |_profiler| "sub-systems" => add 1 }

      let mut instance = match pre_proc_res {
        Either::Left(instance) => instance,
        Either::Right(None) => return Ok(None),
        Either::Right(Some(_)) => unimplemented!(),
      } ;

      if conf.teacher.step && (
        pos_splitter.info().is_some() ||
        neg_splitter.info().is_some()
      ) {
        pause("to start solving") ;
      }

      let teacher_profiler = Profiler::new() ;

      let res = profile!(
        |_profiler| wrap {
          run_teacher(instance.clone(), & model, & teacher_profiler)
        } "teaching"
      ) ? ;
      print_stats("teacher", teacher_profiler) ;

      if let Some(candidates) = res {
        log! { @info "sat\n" }
        let mut this_model = instance.model_of(candidates) ? ;
        if let Some(instance) = Arc::get_mut(& mut instance) {
          instance.simplify_pred_defs(& mut this_model) ?
        }
        for (pred, tterms) in this_model {
          if ! real_instance.is_known(pred) {
            let conj = neg_models.entry(pred).or_insert_with(
              || vec![]
            ) ;
            if ! conj.iter().any( |tts| tts == & tterms ) {
              if let Some(true) = tterms.bool() {
                ()
              } else {
                conj.push(tterms)
              }
            }
          }
        }
      } else {
        log! { @info "unsat\n" }
        return Ok(None)
      }

    }

    'update_model: for (pred, mut conj) in neg_models.drain() {
      let dnf = model.entry(pred).or_insert_with(
        || vec![]
      ) ;
      let mut cnt = 0 ;
      while cnt < conj.len() {
        match conj[cnt].bool() {
          Some(false) => continue 'update_model,
          Some(true) => {
            conj.swap_remove(cnt) ;
          },
          None => cnt += 1,
        }
      }
      if ! conj.is_empty()
      || dnf.iter().all( |conj| ! conj.is_empty() ) {
        dnf.push(conj)
      }
    }

  }

  Ok( Some(model) )
}


/// Runs the teacher on an instance.
pub fn run_teacher(
  instance: Arc<Instance>,
  model: & InitCandidates,
  _profiler: & Profiler
) -> Res< Option<Candidates> > {
  let teacher_profiler = Profiler::new() ;
  profile! { |_profiler| tick "solving" }
  let solve_res = ::teacher::start_class(
    & instance, model, & teacher_profiler
  ) ;
  profile! { |_profiler| mark "solving" }
  print_stats("teacher", teacher_profiler) ;
  solve_res
}




/// Creates new instances by splitting positive/negative clauses.
pub struct Splitter {
  /// The instance we're working on.
  instance: Arc<Instance>,
  /// True if the splitter works on positive clauses.
  pos: bool,
  /// Clauses to look at separately. Indices refer to `self.instance`.
  ///
  /// `Right(once)` means that this splitting is inactive, and `next_instance`
  /// will return `self.instance` if `! once` and `None` otherwise.
  clauses: Either<Vec<ClsIdx>, bool>,
  /// Profiler.
  _profiler: Option<Profiler>,
}
impl Splitter {

  /// Constructor.
  pub fn new(
    instance: & Arc<Instance>, pos: bool
  ) -> Self {
    let clauses = if pos
    && conf.split_pos
    && instance.pos_clauses().len() > 1 {
      Either::Left(
        instance.pos_clauses().iter().map(|c| * c).collect()
      )
    } else if ! pos
    && conf.split_neg
    && instance.neg_clauses().len() > 1 {
      Either::Left(
        instance.neg_clauses().iter().map(|c| * c).collect()
      )
    } else {
      Either::Right(false)
    } ;
    let instance = instance.clone() ;
    // let model = Vec::new() ;
    Splitter {
      instance, // model,
      pos, clauses, _profiler: None,
    }
  }

  /// Retrieves the profiler.
  pub fn profiler(& mut self) -> Option<Profiler> {
    let mut res = None ;
    ::std::mem::swap(& mut res, & mut self._profiler) ;
    res
  }

  /// Returns the number of clauses already treated and the total number of
  /// clauses to handle if active.
  pub fn info(& self) -> Option<(usize, usize)> {
    match self.clauses {
      Either::Left(ref clauses) => {
        let total = if self.pos {
          self.instance.pos_clauses().len()
        } else {
          self.instance.neg_clauses().len()
        } ;
        Some( (total + 1 - clauses.len(), total) )
      },
      Either::Right(_) => None,
    }
  }

  /// Returns the next instance to work on.
  pub fn next_instance(& mut self) -> Res<
    Option< Either<Arc<Instance>, Option<DnfModel>> >
  > {
    match self.clauses {
      Either::Left(ref mut clauses) => if let Some(clause) = clauses.pop() {
        let profiler = Profiler::new() ;
        let pre_proc_res = profile! (
          |profiler| wrap {
            pre_proc(
              self.instance.as_ref(), (self.pos, clause), & profiler
            )
          } if self.pos {
            "positive sub-preproc"
          } else {
            "negative sub-preproc"
          }
        ) ? ;
        self._profiler = Some(profiler) ;
        Ok(
          Some(
            pre_proc_res.map_left(
              |sub_instance| Arc::new(sub_instance)
            )
          )
        )
      } else {
        Ok(None)
      },
      Either::Right(ref mut once) => if * once {
        Ok(None)
      } else {
        * once = true ;
        Ok( Some( Either::Left(self.instance.clone()) ) )
      }
    }
  }

}



/// Applies pre-processing to a modified instance.
///
/// Generates the instance obtained by removing all positive (if `pos`,
/// negative otherwise) clauses but `clause`. Preprocesses it and returns the
/// result.
fn pre_proc(
  instance: & Instance, (pos, clause): (bool, ClsIdx),
  profiler: & Profiler
) -> Res< Either<Instance, Option<DnfModel>>> {

  debug_assert! {
    ( ! pos || instance[clause].lhs_preds().is_empty() ) &&
    (   pos || instance[clause].rhs().is_none()        )
  }

  let mut instance = if pos {
    instance.clone_with_one_pos(clause)
  } else {
    instance.clone_with_one_neg(clause)
  } ;

  if conf.preproc.active {
    ::instance::preproc::work(& mut instance, profiler, false) ?
  }
  instance.finalize() ? ;

  if let Some(maybe_model) = instance.is_trivial() ? {
    Ok( Either::Right(maybe_model) )
  } else {
    Ok( Either::Left(instance) )
  }
}
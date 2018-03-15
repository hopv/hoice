//! Handles instance splitting.
//!
//! Used to reason separately on each positive/negative clause.

use common::* ;



/// Prints the stats if asked. Does nothing in bench mode.
#[cfg(feature = "bench")]
fn print_stats(_: & 'static str, _: Profiler) {}
/// Prints the stats if asked. Does nothing in bench mode.
#[cfg( not(feature = "bench") )]
fn print_stats(name: & 'static str, profiler: Profiler) {
  if conf.stats {
    println!("") ;
    profiler.print( name, "", & [ "data" ] ) ;
    println!("") ;
  }
}





/// Splits the instance if asked to do so, and solves it.
///
/// Assumes the instance is **already pre-processed**.
pub fn work(
  real_instance: Arc<Instance>, _profiler: & Profiler
) -> Res< Option<DnfCandidates> > {
  // Encodes a DNF.
  let mut model = DnfCandidates::new() ;
  let mut neg_models = PrdHMap::new() ;


  let mut pos_splitter = Splitter::new(& real_instance, true, _profiler) ;


  while let Some(instance) = pos_splitter.next_instance() ? {
    let mut neg_splitter = Splitter::new(& instance, false, _profiler) ;

    while let Some(mut instance) = neg_splitter.next_instance() ? {
      debug_assert! { neg_models.is_empty() }

      if_verb! {
        if let Some((current, left)) = pos_splitter.info() {
          info! { "Splitting on positive clause {} of {}", current, left }
        }
        if let Some((current, left)) = neg_splitter.info() {
          info! { "Splitting on negative clause {} of {}", current, left }
        }
      }

      if let Some(candidates) = run_teacher(instance.clone(), _profiler) ? {
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
        return Ok(None)
      }

    }

    'update_model: for (pred, mut conj) in neg_models.drain() {
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
      if ! conj.is_empty() {
        model.entry(pred).or_insert_with(
          || vec![]
        ).push(conj)
      }
    }

  }

  Ok( Some(model) )
}


/// Runs the teacher on an instance.
pub fn run_teacher(
  instance: Arc<Instance>, _profiler: & Profiler
) -> Res< Option<Candidates> > {
  let teacher_profiler = Profiler::new() ;
  profile! { |_profiler| tick "solving" }
  let solve_res = ::teacher::start_class(
    & instance, & teacher_profiler
  ) ;
  profile! { |_profiler| mark "solving" }
  print_stats("teacher", teacher_profiler) ;
  solve_res
}




/// Creates new instances by splitting positive/negative clauses.
pub struct Splitter<'a> {
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
  _profiler: & 'a Profiler,
}
impl<'a> Splitter<'a> {

  /// Constructor.
  pub fn new(
    instance: & Arc<Instance>, pos: bool,
    _profiler: & 'a Profiler
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
      pos, clauses, _profiler
    }
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
        Some( (total - clauses.len(), total) )
      },
      Either::Right(_) => None,
    }
  }

  /// Returns the next instance to work on.
  pub fn next_instance(& mut self) -> Res< Option<Arc<Instance>> > {
    match self.clauses {
      Either::Left(ref mut clauses) => if let Some(clause) = clauses.pop() {
        Ok(
          Some(
            Arc::new(
              pre_proc(
                self.instance.as_ref(), (self.pos, clause), self._profiler
              ) ?
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
        Ok( Some(self.instance.clone()) )
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
) -> Res<Instance> {

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
    ::instance::preproc::work(& mut instance, profiler) ?
  }
  instance.finalize() ? ;

  Ok(instance)
}
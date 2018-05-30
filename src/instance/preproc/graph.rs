//! Module in charge of constructing an analyzing the graph of dependencies
//! between predicates.

use common::* ;
use var_to::terms::VarTermsSet ;
use instance::preproc::utils ;



/// Iterator over all the combinations of some length of a collection of
/// something.
///
/// In the following, `len` is the length of the combinations we generate.
///
/// # Fields
///
/// `current` is `None` if there are no more combinations. Otherwise it stores
/// a list of pairs of length `len`, where `current[i]` stores
///
/// - the `i`th element `e` of the **next** combination ;
/// - the elements that follow `e` in the original collection, as an iterator.
///
/// `next` will be used to pass the next combination, if any, when the `next`
/// function is called.
///
/// `head` is the first element of the collection.
///
/// `tail` is the rest of the collection.
///
/// # Invariants
///
/// - `self.current.as_ref().map(|v| v.len()).unwrap_or(self.len())`
///   is equal to `self.len`
/// - `self.next.capacity() == self.len()`
/// - There's `self.len - 1` elements in `self.tail`
struct CombinationIter<Iter: Iterator + Clone> {
  current: Option< Vec< (Iter::Item, Iter) > >,
  len: usize,
  next: Vec<Iter::Item>,
  head: Iter::Item,
  tail: Iter,
}

impl<Iter> CombinationIter<Iter>
where Iter: Iterator + ExactSizeIterator + Clone, Iter::Item: Clone {

  /// Constructor.
  ///
  /// Fails if `coll.next().is_none()`, or if `len == 0`.
  fn new(mut coll: Iter, len: usize) -> Res<Self> {
    if len == 0 {
      bail!("trying to create all combinations of length 0, illegal")
    }
    let (head, tail) = if let Some(first) = coll.next() {
      (first, coll)
    } else {
      bail!("trying to create all combinations of an empty collection")
    } ;

    Ok(
      CombinationIter {
        current: Some(
          vec![ (head.clone(), tail.clone()) ; len ]
        ),
        len,
        next: Vec::with_capacity(len),
        head, tail
      }
    )
  }

  /// Returns the next combination if any.
  fn next(& mut self) -> Option< & Vec<Iter::Item> > {
    let mut res = None ;

    if let Some(mut current) = ::std::mem::replace(
      & mut self.current, None
    ) {
      self.next.clear() ;

      // Construct result, easy part.
      for (item, _) in & current {
        self.next.push( item.clone() )
      }
      // Remember we have a next.
      res = Some(& self.next) ;

      // Tricky part.
      //
      // Remove from `current` the pairs that don't have a next element, until
      // we find one that does (starting from the end).
      'find_next: while let Some((_, mut curr)) = current.pop() {
        if let Some(next) = curr.next() {
          // Found an element with a next.
          current.push( (next, curr) ) ;
          // Now we restart all elements after this one (the elements we
          // removed).
          while current.len() < self.len {
            current.push(
              // Starting again from the beginning for this element.
              ( self.head.clone(), self.tail.clone() )
            )
          }
          // Done, update current and break out.
          self.current = Some(current) ;
          break 'find_next
        }
      }
    }
    res
  }

}




/// Maps predicates to the predicates they depend on.
pub type Dep = PrdMap< PrdMap<usize> > ;

/// Graph of dependencies.
#[derive(Clone)]
pub struct Graph {
  /// Forward dependencies.
  forward: Dep,
  /// Backward dependencies.
  bakward: Dep,
  /// Predicates appearing in a negative constraint.
  neg: PrdMap<usize>,
  /// Predicates appearing in a positive constraint.
  pos: PrdMap<usize>,
}
impl Graph {
  /// Constructs an empty graph.
  pub fn new(instance: & Instance) -> Self {
    let forward: Dep = vec![
      vec![ 0 ; instance.preds().len() ].into() ; instance.preds().len()
    ].into() ;
    let bakward = forward.clone() ;
    let neg: PrdMap<_> = vec![ 0 ; instance.preds().len() ].into() ;
    let pos: PrdMap<_> = vec![ 0 ; instance.preds().len() ].into() ;
    Graph { forward, bakward, neg, pos }
  }

  /// Resets the graph.
  fn reset(& mut self) {
    for forward in self.forward.iter_mut() {
      for count in forward.iter_mut() {
        * count = 0
      }
    }
    for bakward in self.bakward.iter_mut() {
      for count in bakward.iter_mut() {
        * count = 0
      }
    }
    for count in self.pos.iter_mut() {
      * count = 0
    }
    for count in self.neg.iter_mut() {
      * count = 0
    }
  }

  /// Clears itself and sets everything up for the input instance.
  pub fn setup(& mut self, instance: & Instance) {
    self.reset() ;

    for clause in instance.clauses() {
      if let Some((tgt, _)) = clause.rhs() {
        if clause.lhs_preds().is_empty() {
          self.pos[tgt] += 1 ;
        } else {
          for (prd, _) in clause.lhs_preds() {
            self.bakward[tgt][* prd] += 1 ;
            self.forward[* prd][tgt] += 1 ;
          }
        }
      } else {
        for (prd, _) in clause.lhs_preds() {
          self.neg[* prd] += 1 ;
        }
      }
    }
  }

  /// Dumps a graph in dot format.
  pub fn dot_write<W: Write>(
    & self, w: & mut W, instance: & Instance, hi_lite: & PrdSet
  ) -> Res<()> {
    writeln!(w, "digraph blah {{", ) ? ;
    writeln!(w, "  rankdir=LR ;") ? ;
    writeln!(w, "  edge [arrowhead=onormal] ;") ? ;
    writeln!(
      w, "  top[\
        label = \"top\", peripheries = 2, color = darkolivegreen3, \
        style = filled, fontcolor = white
      ] ;"
    ) ? ;
    writeln!(
      w, "  bot[\
        label = \"bot\", peripheries = 2, color = indianred1, \
        style = filled, fontcolor = white
      ] ;"
    ) ? ;
    for (prd, info) in instance.preds().index_iter() {
      if instance.forced_terms_of(prd).is_none() {
        if hi_lite.contains(& prd) {
          writeln!(
            w,
            "  p_{} [label = \"{}\", color = gray, style = filled] ;",
            prd, info.name
          ) ?
        } else {
          writeln!(w, "  p_{} [label = \"{}\"] ;", prd, info.name) ?
        }
      }
    }
    for (prd, count) in self.pos.index_iter() {
      if * count > 0 {
        writeln!(
          w, "  top -> p_{} [color = darkolivegreen3, label = \"{}\"] ;",
          prd, count
        ) ?
      }
    }
    for (prd, count) in self.neg.index_iter() {
      if * count > 0 {
        writeln!(
          w, "  p_{} -> bot [color = indianred1, label = \"{}\"] ;",
          prd, count
        ) ?
      }
    }
    for (prd, targets) in self.forward.index_iter() {
      for (tgt, count) in targets.index_iter() {
        let count = * count ;
        if count > 0 {
          writeln!(w, "  p_{} -> p_{} [label = \"{}\"] ;", prd, tgt, count) ?
        }
      }
    }
    writeln!(w, "}}\n") ? ;
    Ok(())
  }

  /// Dumps a graph to a file as a graphviz graph, and runs `dot`.
  #[inline]
  pub fn to_dot<S: AsRef<str>>(
    & self, instance: & Instance, file: S, hi_lite: & PrdSet
  ) -> Res<()> {
    if let Some(
      (mut pred_dep_file, path)
    ) = conf.preproc.pred_dep_file(file, instance) ? {
      use std::process::Command ;
      self.dot_write(& mut pred_dep_file, instance, hi_lite) ? ;
      let mut pdf_path = path.clone() ;
      pdf_path.set_extension("pdf") ;
      let output = match Command::new("dot").args(
        & ["-Tpdf", "-o"]
      ).arg(pdf_path).arg(& path).output() {
        Ok(output) => output,
        Err(ref e) if e.kind() == ::std::io::ErrorKind::NotFound => {
          warn!(
            "failed to run `{}` on predicate dependency graphviz file `{}`",
            conf.sad("dot"),
            conf.emph( path.to_string_lossy() ),
          ) ;
          return Ok(())
        },
        Err(e) => bail!(e),
      } ;
      if ! output.status.success() {
        let mut blah = format!(
          "while running `dot` on `{}`\n|=| stdout:",
          path.to_string_lossy()
        ) ;
        for line in String::from_utf8_lossy(& output.stdout).lines() {
          blah.push_str("\n  | ") ;
          blah.push_str(line)
        }
        blah.push_str("\n|=| stdout:") ;
        for line in String::from_utf8_lossy(& output.stderr).lines() {
          blah.push_str("\n  | ") ;
          blah.push_str(line)
        }
        blah.push_str("\n|=|") ;
        bail!(blah)
      }
    }
    Ok(())
  }

  /// Checks that the graph makes sense.
  #[cfg( not(debug_assertions) )]
  #[inline(always)]
  pub fn check(& self, _: & Instance) -> Res<()> {
    Ok(())
  }

  /// Checks that the graph makes sense.
  #[cfg(debug_assertions)]
  pub fn check(& self, instance: & Instance) -> Res<()> {
    fn sub_check(slf: & Graph, instance: & Instance) -> Res<()> {
      for (prd, targets) in slf.forward.index_iter() {
        for (tgt, count) in targets.index_iter() {
          let bak_count = & slf.bakward[tgt][prd] ;
          if bak_count != count {
            bail!(
              "\
                found {} forward dependencies for `{} -> {}`, \
                but {} (!= {}) backward dependencies\
              ", count, instance[prd], instance[tgt], bak_count, count
            )
          }
        }
      }
      for (prd, targets) in slf.bakward.index_iter() {
        for (tgt, count) in targets.index_iter() {
          let for_count = & slf.forward[tgt][prd] ;
          if for_count != count {
            bail!(
              "\
                found {} backward dependencies for `{} -> {}`, \
                but {} (!= {}) forward dependencies\
              ", count, instance[prd], instance[tgt], for_count, count
            )
          }
        }
      }
      Ok(())
    }
    sub_check(self, instance).chain_err(
      || "graph inconsistency:"
    )
  }

  /// Predicates that directly depend on this predicate.
  pub fn forward_dep(& self, pred: PrdIdx) -> & PrdMap<usize> {
    & self.forward[pred]
  }

  /// Predicates this predicate directly depends on.
  pub fn bakward_dep(& self, pred: PrdIdx) -> & PrdMap<usize> {
    & self.bakward[pred]
  }

  /// Follows a forward map. Returns the predicates it encountered and how many
  /// times it encountered them.
  pub fn follow(
    _instance: & Instance, start: PrdIdx, forward: & PrdHMap<PrdSet>
  ) -> Res< PrdHMap<usize> > {
    let mut known = PrdSet::new() ;
    let mut to_do = PrdSet::new() ;
    to_do.insert(start) ;
    known.insert(start) ;

    let mut res = PrdHMap::new() ;
    res.insert(start, 1) ;

    macro_rules! update {
      ($known:ident $to_do:ident $map:ident < $set:expr) => (
        for prd in $set {
          * $map.entry(* prd).or_insert(0) += 1 ;
          let unknown = $known.insert(* prd) ;
          if unknown {
            let is_new = $to_do.insert(* prd) ;
            debug_assert!( is_new )
          }
        }
      ) ;
    }

    while ! to_do.is_empty() {
      conf.check_timeout() ? ;
      let pred = * to_do.iter().next().unwrap() ;
      to_do.remove(& pred) ;
      if let Some(tgts) = forward.get(& pred) {
        if_debug! {
          log_debug! { "following {}", _instance[pred] } ;
          for pred in tgts {
            log_debug! { "- {}", _instance[* pred] }
          }
        }

        update!( known to_do res < tgts )
      }
    }

    Ok(res)
  }

  /// Merges two DNFs with quantifiers.
  ///
  /// Also returns the clause generation estimation.
  ///
  /// Returns `None` if inlining would have generated more clauses than `max`
  /// (by `estimate`).
  ///
  /// Used when inlining a predicate application of `p`. `lft` is understood as
  /// (part of) the definition of `p` different from `pred`. `subst` are its
  /// arguments.
  ///
  /// The arguments of `p` are applied to `lft`, and the quantified variables
  /// are bumped to the first variable index used by neither the formal
  /// arguments of `pred` and the quantified variables in `rgt`.
  ///
  /// Renames the quantified variables so that they don't clash.
  ///
  /// # TODO
  ///
  /// - improve performance, `rgt` could just receive the result
  fn merge(
    instance: & Instance, pred: PrdIdx,
    substs: & VarTermsSet,
    lft: & Vec<(Quantfed, TTermSet)>,
    rgt: & Vec<(Quantfed, TTermSet)>,
    max: Option<usize>,
  ) -> Res<
    Option< (Vec<(Quantfed, TTermSet)>, usize) >
  > {
    log! {
      @6 "merging for {}, {} substitutions", instance[pred], substs.len()
    }
    let fresh_index = instance.original_sig_of(pred).next_index() ;
    log! { @6 "fresh index: {}", fresh_index }

    let mut result = Vec::with_capacity( lft.len() * rgt.len() ) ;
    let mut estimation = 0 ;

    // This will map `lft` quantified variables to fresh index to avoid
    // quantified variable clashes.
    let mut qvar_map = VarHMap::with_capacity(0) ;

    'merge: for & (ref r_qvars, ref r_conj) in rgt {
      // Retrieve first legal index for new quantified variables.
      let mut fresh_index = fresh_index ;

      for (idx, _) in r_qvars {
        log! { @7 "- rgt qvar {}", idx }
        if * idx >= fresh_index {
          fresh_index = (1 + ** idx).into()
        }
      }
      log! { @7 "first legal index: {}", fresh_index }

      // All combinations of elements of `lft` of len `substs`.
      let mut all_lft_combinations = CombinationIter::new(
        lft.iter(), substs.len()
      ).chain_err(
        || format!(
          "while generating all combinations during merge for predicate {}",
          instance[pred]
        )
      ) ? ;

      // For each combination of elements of `lft` of len `substs`, add a new
      // definition to `r_conj`.
      'all_combinations: while let Some(
        combination
      ) = all_lft_combinations.next() {
        debug_assert_eq! { combination.len(), substs.len() }

        // Cloning `rgt`'s definition to add stuff from `lft` for this
        // combination.
        let mut r_conj = r_conj.clone() ;
        // Cloning `rgt`'s qvars to add the renamed qvars from `lft`.
        let mut r_qvars = r_qvars.clone() ;

        // Work on the current combination: apply a substitution to a member of
        // `lft`.
        for ( (l_qvars, l_conj), subst ) in combination.iter().zip(
          substs.iter()
        ) {
          conf.check_timeout() ? ;

          // Fresh map for this substitution.
          qvar_map.clear() ;

          // Generate fresh indices for `l_qvars` to avoid index clashes.
          qvar_map.reserve( l_qvars.len() ) ;
          r_qvars.reserve( l_qvars.len() ) ;
          for (qvar, typ) in l_qvars {
            let prev = qvar_map.insert(
              * qvar, term::var(fresh_index, typ.clone())
            ) ;
            debug_assert!( prev.is_none() ) ;
            // Update the new qvars for the result.
            let prev = r_qvars.insert( fresh_index, typ.clone() ) ;
            debug_assert!( prev.is_none() ) ;
            // Increment the fresh_index.
            fresh_index.inc()
          }

          // Apply substitution and add to `r_conj`.

          r_conj.reserve(
            l_conj.terms().len(), l_conj.preds().len()
          ) ;
          // Working on terms.
          for term in l_conj.terms() {
            let (term, _) = term.subst( & (& qvar_map, subst) ) ;

            let is_false = term::simplify::conj_term_insert(
              term, r_conj.terms_mut()
            ) ;

            if is_false {
              continue 'all_combinations
            }
          }

          // Working on pred applications.
          for (pred, argss) in l_conj.preds() {
            let mut nu_argss = VarTermsSet::with_capacity( argss.len() ) ;
            for args in argss {
              let mut nu_args = VarMap::with_capacity( args.len() ) ;
              for arg in args.iter() {
                let (arg, _) = arg.subst( & (& qvar_map, subst) ) ;
                nu_args.push(arg)
              }
              nu_argss.insert( nu_args.into() ) ;
            }
            r_conj.insert_pred_apps( * pred, nu_argss )
          }
        }

        // Done with this combination.
        let curr = (r_qvars, r_conj) ;
        // Only add if new (loose syntactic check).
        if result.iter().all(
          |other| other != & curr
        ) {
          result.push(curr) ;

          if let Some(max) = max {
            if let Some(e) = Self::estimate(
              instance, pred, result.len(), max
            ) {
              estimation += e
            } else {
              return Ok(None)
            }
          }
        }
      }
    }

    Ok( Some( (result, estimation) ) )
  }


  /// Retrieves the definition of a predicate from all its RHS occurences.
  ///
  /// Also returns the clause generation estimation.
  ///
  /// Returns `None` if inlining would have generated more clauses than `max`
  /// (by `estimate`).
  fn dnf_of(
    & mut self, instance: & Instance, pred: PrdIdx, max: Option<usize>,
    previous: & Vec< (PrdIdx, Vec<(Quantfed, TTermSet)>) >
  ) -> Res< Option< (Vec<(Quantfed, TTermSet)>, usize) > > {
    log! { @4 "dnf_of({}, {:?})", instance[pred], max }

    let forced_inlining = max.is_none() ;

    let mut estimation = 0 ;

    let clauses = instance.rhs_clauses_of(pred) ;
    let mut def = Vec::with_capacity( clauses.len() ) ;

    conf.check_timeout() ? ;

    'clause_iter: for clause in clauses {
      let mut to_merge: Vec<(
        PrdIdx, VarTermsSet, & Vec<(Quantfed, TTermSet)>
      )> = Vec::with_capacity(7) ;

      let clause = & instance[* clause] ;
      let args = if let Some((p, args)) = clause.rhs() {
        debug_assert_eq! { p, pred }
        args
      } else {
        bail!("instance inconsistency")
      } ;
      match utils::terms_of_rhs_app(
        true, instance, & clause.vars,
        clause.lhs_terms(), clause.lhs_preds(),
        pred, args
      ) ? {
        utils::ExtractRes::Success((qvars, mut tterms)) => {
          log! { @5
            "from clause {}", clause.to_string_info(& instance.preds()) ?
          }

          if ! forced_inlining && ! tterms.preds().is_empty() {
            for (pred, def) in previous {
              if tterms.preds().is_empty() { break }
              if let Some(argss) = tterms.preds_mut().remove(pred) {
                to_merge.push( (* pred, argss, def) )
              }
            }
          }

          if to_merge.is_empty() {
            def.push( (qvars, tterms) ) ;

            if let Some(max) = max {
              if let Some(e) = Self::estimate(
                instance, pred, def.len(), max
              ) {
                estimation += e
              } else {
                return Ok(None)
              }
            }
          } else {

            if_log! { @5
              log! { @5 "qvars {{" }
              for (var, typ) in & qvars {
                log! { @5 "  {}: {}", var.default_str(), typ }
              }
              log! { @5 "}}" }
              log! { @5 "conj {{" }
              for term in tterms.terms() {
                log! { @5 "  {}", term }
              }
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log! { @5 "  ({} {})", instance[* pred], args }
                }
              }
              log! { @5 "}}" }
            }

            let mut curr = vec![ (qvars, tterms) ] ;

            for (_this_pred, argss, p_def) in to_merge.drain(0..) {
              conf.check_timeout() ? ;
              if_log! { @6
                log! { @6 "curr {{" }
                let mut first = true ;
                for & (ref qv, ref tterms) in & curr {
                  if first { first = false } else { log! { @6 " " } }
                  for (var, typ) in qv {
                    log! { @6 "  {}: {}", var.default_str(), typ }
                  }
                  for term in tterms.terms() {
                    log! { @6 "  {}", term }
                  }
                  for (pred, argss) in tterms.preds() {
                    for args in argss {
                      log! { @6 "  ({} {})", instance[* pred], args }
                    }
                  }
                }
                log! { @6 "}}" }
                log! { @6 "argss for {} {{", instance[_this_pred] }
                for args in & argss {
                  let mut pref = "  > " ;
                  for (var, arg) in args.index_iter() {
                    log! { @6 "{}{} -> {}", pref, var.default_str(), arg }
                    pref = "    "
                  }
                }
                log! { @6 "}}" }
                log! { @6 "defs {{" }
                first = true ;
                for & (ref qv, ref tterms) in p_def {
                  if first { first = false } else { log! { @6 " " } }
                  for (var, typ) in qv {
                    log! { @6 "  {}: {}", var.default_str(), typ }
                  }
                  for term in tterms.terms() {
                    log! { @6 "  {}", term }
                  }
                  for (pred, argss) in tterms.preds() {
                    for args in argss {
                      log! { @6 "  ({} {})", instance[* pred], args }
                    }
                  }
                }
                log! { @6 "}}" }
              }

              if let Some((def, e)) = Self::merge(
                instance, pred, & argss, p_def, & curr, max
              ) ? {
                curr = def ;
                estimation = e
              } else {
                return Ok(None)
              }
            }

            for pair in curr {
              def.push(pair)
            }
          }

          if_log! { @5
            log! { @5 "current definition:" }
            for (qvars, tterms) in & def {
              log! { @5 "and" }
              if ! qvars.is_empty() {
                log! { @5 "  qvars {{" }
                for (var, typ) in qvars {
                  log! { @5 "    {}: {}", var.default_str(), typ }
                }
                log! { @5 "  }}" }
              }
              for term in tterms.terms() {
                log! { @5 "  {}", term }
              }
              for (pred, argss) in tterms.preds() {
                for args in argss {
                  log! { @5 "  ({} {})", instance[* pred], args }
                }
              }
            }
            log! { @5 " " }
          }

        },
        utils::ExtractRes::SuccessTrue => bail!(
          "unimplemented, predicate is true ({} {})", instance[pred], args
        ),
        utils::ExtractRes::Trivial |
        utils::ExtractRes::SuccessFalse => continue 'clause_iter,
        _ => bail!("failed to extract lhs terms"),
      }
    }

    Ok(
      Some( (def, estimation) )
    )
  }


  /// Constructs all the predicates not in `keep` by inlining the constraints.
  ///
  /// Returns a disjunction of conjunctions.
  pub fn inline(
    & mut self, instance: & Instance, keep: & mut PrdSet,
    mut upper_bound: usize
  ) -> Res<
    Vec< (PrdIdx, Vec<(Quantfed, TTermSet)>) >
  > {
    let mut res = Vec::with_capacity(
      instance.preds().len() - keep.len()
    ) ;
    macro_rules! res_contains {
      ($pred:expr) => ( res.iter().any( |(pred, _)| pred == $pred ) ) ;
    }

    let forced_inlining = keep.len() == 0 ;

    conf.check_timeout() ? ;

    'construct: loop {

      // Find a predicate that's not in `keep` with all its antecedents in
      // `keep`.
      let mut pred = None ;
      'find_pred: for (prd, srcs) in self.bakward.index_iter() {
        if keep.contains(& prd)
        || instance.forced_terms_of(prd).is_some()
        || res_contains!(& prd) { continue 'find_pred }
        log_debug! { "looking at {}", instance[prd] }
        'check_src: for (src, cnt) in srcs.index_iter() {
          if * cnt == 0 { continue 'check_src }
          log_debug! { "depends on {}", instance[src] }
          if ! keep.contains(& src)
          && ! res_contains!(& src) { continue 'find_pred }
        }
        pred = Some(prd) ;
        break 'find_pred
      }

      let pred = if let Some(p) = pred { p } else {
        log_debug! { "no predicate illeligible for inlining" }
        break 'construct
      } ;

      log_debug! { "investigating inlining {}", instance[pred] }

      macro_rules! keep_and_continue {
        ($pred:expr) => (
          keep.insert($pred) ;
          continue 'construct
        ) ;
        () => ({
          keep.insert(pred) ;
          continue 'construct
        }) ;
      }

      let def = if let Some((def, estimation)) = self.dnf_of(
        instance, pred,
        if ! forced_inlining { Some(upper_bound) } else { None },
        & res
      ) ? {
        upper_bound += estimation ;
        log! { @4
          "inlining {} (blow-up estimation: {})", instance[pred], estimation
        }
        def
      } else {
        keep_and_continue!()
      } ;

      if_log! { @4
        log! { @4 "definition:" }
        for (qvars, tterms) in & def {
          log! { @4 "and" }
          if ! qvars.is_empty() {
            log! { @4 "  qvars {{" }
            for (var, typ) in qvars {
              log! { @4 "    {}: {}", var.default_str(), typ }
            }
            log! { @4 "  }}" }
          }
          for term in tterms.terms() {
            log! { @4 "  {}", term }
          }
          for (pred, argss) in tterms.preds() {
            for args in argss {
              log! { @4 "  ({} {})", instance[* pred], args }
            }
          }
        }
        log! { @4 " " }
      }

      conf.check_timeout() ? ;

      debug_assert! { ! res_contains!(& pred) }

      res.push( (pred, def) )
    }

    Ok( res )
  }


  /// Estimates clause creation blow-up.
  ///
  /// Estimates whether inlining `pred` with a DNF of length `len` will
  /// generate more than `max` clauses. If yes, returns `None`, and returns its
  /// prediction otherwise.
  fn estimate(
    instance: & Instance, pred: PrdIdx, len: usize, max: usize
  ) -> Option<usize> {
    let max = max + instance.clauses_of(pred).1.len() ;
    let mut estimation: usize = 0 ;

    // println!("{}: {} / {}", instance[pred], len, max) ;

    for clause in instance.clauses_of(pred).0 {
      let argss_len = instance[* clause].lhs_preds().get(& pred).map(
        |argss| argss.len()
      ).expect("inconsistent instance state") ;
      // println!("  #{}: {}", clause, argss_len) ;

      let mut inc = len ;
      for _ in 1 .. argss_len {
        if inc > max {
          return None
        } else if let Some(nu_inc) = inc.checked_mul(len) {
          inc = nu_inc
        } else {
          return None
        }
      }

      // println!("  inc: {}", inc) ;

      if let Some(e) = estimation.checked_add(inc) {
        estimation = e ;
        if estimation <= max {
          // println!("  est: {}", estimation) ;
          continue
        }
      }
      // println!("blows up") ;
      log! { @6
        "inlining for {} blows up: {} > {} (len: {})",
        instance[pred], estimation, max, len
      }
      return None
    }

    Some(estimation)
  }



  /// Looks for a minimal set of predicates to infer by breaking cycles.
  ///
  /// Returns the set of predicates to keep, and the set of predicates to
  /// remove.
  pub fn break_cycles(
    & mut self, instance: & Instance
  ) -> Res<PrdSet> {
    log_debug! { "breaking cycles in pred dep graph..." }
    let mut set = PrdSet::with_capacity(instance.preds().len() / 3) ;

    conf.check_timeout() ? ;
    for (prd, prds) in self.forward.index_iter() {
      if prds[prd] > 0 {
        let is_new = set.insert(prd) ;
        debug_assert!( is_new )
      }
    }

    conf.check_timeout() ? ;
    let mut pos = PrdSet::new() ;
    for (prd, cnt) in self.pos.index_iter() {
      if set.contains(& prd) { continue }
      if * cnt > 0 {
        pos.insert(prd) ;
      }
    }

    conf.check_timeout() ? ;
    let mut forward = PrdHMap::new() ;
    for (prd, prds) in self.forward.index_iter() {
      if set.contains(& prd) { continue }
      for (tgt, cnt) in prds.index_iter() {
        if set.contains(& tgt) { continue }
        if * cnt > 0 {
          let is_new = forward.entry(prd).or_insert_with(
            || PrdSet::new()
          ).insert(tgt) ;
          debug_assert!( is_new )
        }
      }
    }

    let mut cnt = 0 ;

    conf.check_timeout() ? ;
    'break_cycles: while ! forward.is_empty() {

      cnt += 1 ;
      self.to_dot(instance, format!("pred_red_{}", cnt), & set) ? ;

      if_debug! {
        log_debug! { "  looking for a starting point with" }
        log_debug! { "  - pos {{" }
        for prd in & pos {
          log_debug! { "    {}", instance[* prd] }
        }
        log_debug! { "  }}" }
        log_debug! { "  - forward {{" }
        for (prd, set) in & forward {
          let mut s = String::new() ;
          for prd in set {
            s = format!("{} {}", s, instance[* prd])
          }
          log_debug! { "    {} ->{}", instance[* prd], s }
        }
      }
      // Find a starting point.
      let mut start = None ;
      for prd in & pos {
        start = Some(* prd) ;
        break
      }
      if let Some(pred) = start {
        log_debug! { "  found one in `pos`" }
        // There was something in `pos`, remove it and move on.
        start = Some(pred)
      } else {
        log_debug! { "  no preds in `pos`, looking in `forward`" }
        // There was nothing in `pos`, select something from `forward`.
        for (prd, _) in & forward {
          start = Some(* prd) ;
          break
        }
      } ;

      let start = if let Some(pred) = start { pred } else {
        log_debug! { "  no starting point found, done" }
        break 'break_cycles
      } ;

      log_debug! { "  starting point is {}, following it", instance[start] }

      // Follow it.
      let weights = Self::follow(instance, start, & forward) ? ;
      if weights.is_empty() {
        bail!("`follow` failed to construct weights...")
      }

      log_debug! { "  looking for the heaviest predicate" }

      // Representant.
      let mut rep = None ;
      for (prd, weight) in & weights {
        let (prd, weight) = (* prd, * weight) ;
        log_debug! { "    {} -> {}", instance[prd], weight }
        let curr_weight = if let Some(
          & (_, w)
        ) = rep.as_ref() { w } else { 0 } ;
        if weight > curr_weight {
          rep = Some((prd, weight))
        }
      }

      let rep = if let Some((prd, weight)) = rep {
        if weight < 2 {
          log_debug! { "  no cycle, forgetting everything" }
          // There's no cycle, forget everything in weight and keep going.
          for (prd, _weight) in weights {
            log_debug! { "  - forgetting {} ({})", instance[prd], _weight }
            pos.remove(& prd) ;
            forward.remove(& prd) ;
            for (_, set) in forward.iter_mut() {
              set.remove(& prd) ;
            }
            debug_assert!( _weight < 2 )
          }
          continue 'break_cycles
        } else {
          log_debug! { "  heaviest is {} ({})", instance[prd], weight }
          prd
        }
      } else {
        unreachable!()
      } ;

      log_debug! { "  removing it from everything" }
      // Remove the representative from everything.
      pos.remove(& rep) ;
      forward.remove(& rep) ;
      for (_, set) in forward.iter_mut() {
        set.remove(& rep) ;
      }

      log_debug! { "  remembering {}", instance[rep] }
      let is_new = set.insert(rep) ;
      debug_assert!( is_new ) ;

      log_debug! { "" }
    }

    set.shrink_to_fit() ;
    Ok(set)
  }
}
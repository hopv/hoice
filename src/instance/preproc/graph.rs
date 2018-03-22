//! Module in charge of constructing an analyzing the graph of dependencies
//! between predicates.

use common::* ;
use instance::preproc::utils ;

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
          log_debug! { "    following {}", _instance[pred] } ;
          for pred in tgts {
            log_debug! { "    - {}", _instance[* pred] }
          }
        }

        update!( known to_do res < tgts )
      }
    }

    Ok(res)
  }

  /// Merges two DNFs with quantifiers.
  ///
  /// Used when inlining a predicate application of `p`. `lft` is understood as
  /// (part of) the definition of `p` different from `pred`. `subst` are its
  /// arguments.
  ///
  /// The arguments of `p` are applied to `lft`, and the quantified variables
  /// are bumped, to the first variable index used by neither the formal
  /// arguments of `pred` and the quantified variables in `rgt`.
  ///
  /// Renames the quantified variables so that they don't clash.
  fn merge(
    instance: & Instance, pred: PrdIdx,
    substs: & HTArgss,
    lft: & Vec<(Quantfed, TTermSet)>,
    rgt: & Vec<(Quantfed, TTermSet)>
  ) -> Res< Vec<(Quantfed, TTermSet)> > {
    log_debug! { "    merging..." }
    let first_index = instance[pred].sig.next_index() ;
    log_debug! { "    first index: {}", first_index }

    let mut result = Vec::with_capacity( lft.len() * rgt.len() ) ;

    'merge: for & (ref r_qvars, ref r_conj) in rgt {
      // Retrieve first legal index for new quantified variables.
      let mut first_index = first_index ;
      for (idx, _) in r_qvars {
        log_debug! { "    - rgt qvar {}", idx }
        if * idx >= first_index { first_index = (1 + ** idx).into() }
      }
      log_debug! { "    first legal index: {}", first_index }

      // Generate map for substitution and update left qvars.
      let mut map = VarHMap::with_capacity(0) ;
      conf.check_timeout() ? ;
      for & (ref l_qvars, ref l_conj) in lft {
        let mut curr_qvar = first_index ;
        map.clear() ;
        map.reserve( l_qvars.len() ) ;
        let mut qvars = r_qvars.clone() ;
        qvars.reserve( l_qvars.len() ) ;
        for (qvar, typ) in l_qvars {
          log_debug! { "    - lft qvar {}", qvar }
          let prev = map.insert(* qvar, term::var(curr_qvar, * typ)) ;
          debug_assert!( prev.is_none() ) ;
          let prev = qvars.insert( curr_qvar, * typ ) ;
          debug_assert!( prev.is_none() ) ;
          curr_qvar.inc()
        }
        if_debug! {
          log_debug! { "    map {{" }
          for (var, term) in & map {
            log_debug! { "      {} -> {}", var.default_str(), term }
          }
          log_debug! { "    }}" }
          log_debug! { "    qvars {{" }
          for (var, typ) in & qvars {
            log_debug! { "      {}: {}", var.default_str(), typ }
          }
          log_debug! { "    }}" }
        }

        conf.check_timeout() ? ;

        'all_substitutions: for subst in substs {
          let mut conj = r_conj.clone() ;
          conj.reserve( l_conj.terms().len(), l_conj.preds().len() ) ;
          for term in l_conj.terms() {
            let (term, _) = term.subst( & (& map, subst) ) ;
            conj.insert_term( term ) ;
          }
          for (pred, argss) in l_conj.preds() {
            let mut nu_argss = HTArgss::with_capacity( argss.len() ) ;
            for args in argss {
              let mut nu_args = VarMap::with_capacity( args.len() ) ;
              for arg in args.iter() {
                let (arg, _) = arg.subst( & (& map, subst) ) ;
                nu_args.push(arg)
              }
              nu_argss.insert( nu_args.into() ) ;
            }
            conj.insert_pred_apps( * pred, nu_argss )
          }
          let curr = (qvars.clone(), conj) ;
          for prev in & result {
            if prev == & curr { continue 'all_substitutions }
          }
          result.push(curr)
        }
      }
    }

    Ok(result)
  }


  /// Constructs all the predicates not in `keep` by inlining the constraints.
  ///
  /// Returns a disjunction of conjunctions.
  pub fn inline(
    & mut self, instance: & Instance, keep: & mut PrdSet,
    upper_bound: usize
  ) -> Res<
    PrdHMap< Vec<(Quantfed, TTermSet)> >
  > {
    let mut res = PrdHMap::with_capacity(
      instance.preds().len() - keep.len()
    ) ;
    let mut increase: usize = 0 ;

    let forced_inlining = keep.len() == 0 ;

    conf.check_timeout() ? ;

    'construct: loop {

      // Find a predicate that's not in `keep` with all its antecedents in
      // `keep`.
      let mut pred = None ;
      'find_pred: for (prd, srcs) in self.bakward.index_iter() {
        if keep.contains(& prd)
        || instance.forced_terms_of(prd).is_some()
        || res.contains_key(& prd) { continue 'find_pred }
        log_debug! { "looking at {}", instance[prd] }
        'check_src: for (src, cnt) in srcs.index_iter() {
          if * cnt == 0 { continue 'check_src }
          log_debug! { "depends on {}", instance[src] }
          if ! keep.contains(& src)
          && ! res.contains_key(& src) { continue 'find_pred }
        }
        pred = Some(prd) ;
        break 'find_pred
      }

      let pred = if let Some(p) = pred { p } else {
        log_debug! { "  no predicate illeligible for inlining" }
        break 'construct
      } ;
      log_debug! { "  inlining {}", instance[pred] }

      // read_line("to continue...") ;

      let (lhs_clauses, clauses) = instance.clauses_of(pred) ;
      let mut def = Vec::with_capacity( clauses.len() ) ;

      conf.check_timeout() ? ;

      'clause_iter: for clause in clauses {
        let mut to_merge: Vec<(
          PrdIdx, HTArgss, & Vec<(Quantfed, TTermSet)>
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
            log_debug! {
              "from clause {}", clause.to_string_info(& instance.preds()) ?
            }
            if ! forced_inlining && ! tterms.preds().is_empty() {
              for (pred, def) in & res {
                if tterms.preds().is_empty() { break }
                if let Some(argss) = tterms.preds_mut().remove(pred) {
                  to_merge.push( (* pred, argss, def) )
                }
              }
            }
            debug_assert! {{
              let mut okay = true ;
              if ! forced_inlining {
                for (pred, _) in tterms.preds() {
                  if ! keep.contains( pred ) {
                    println!("can't find {} in keep", instance[* pred]) ;
                    okay = false
                  }
                }
              }
              okay
            }}

            if to_merge.is_empty() {
              def.push( (qvars, tterms) )
            } else {

              if_debug! {
                log_debug! { "  qvars {{" }
                for (var, typ) in & qvars {
                  log_debug! { "    {}: {}", var.default_str(), typ }
                }
                log_debug! { "  }}" }
                log_debug! { "  conj {{" }
                for term in tterms.terms() {
                  log_debug! { "    {}", term }
                }
                for (pred, argss) in tterms.preds() {
                  for args in argss {
                    log_debug! { "    ({} {})", instance[* pred], args }
                  }
                }
                log_debug! { "  }}" }
              }

              let mut curr = vec![ (qvars, tterms) ] ;

              for (_this_pred, argss, p_def) in to_merge.drain(0..) {
                conf.check_timeout() ? ;
                if_debug! {
                  let mut first = true ;
                  log_debug! { "  args for {} {{", instance[_this_pred] }
                  for (var, arg) in args.index_iter() {
                    log_debug! { "    {} -> {}", var.default_str(), arg }
                  }
                  log_debug! { "  }}" }
                  log_debug! { "  curr {{" }
                  for & (ref qv, ref tterms) in & curr {
                    if first { first = false } else { log_debug! { " " } }
                    for (var, typ) in qv {
                      log_debug! { "    {}: {}", var.default_str(), typ }
                    }
                    for term in tterms.terms() {
                      log_debug! { "    {}", term }
                    }
                    for (pred, argss) in tterms.preds() {
                      for args in argss {
                        log_debug! { "    ({} {})", instance[* pred], args }
                      }
                    }
                  }
                  log_debug! { "  }}" }
                  log_debug! { "  def {{" }
                  first = true ;
                  for & (ref qv, ref tterms) in p_def {
                    if first { first = false } else { log_debug! { " " } }
                    for (var, typ) in qv {
                      log_debug! { "    {}: {}", var.default_str(), typ }
                    }
                    for term in tterms.terms() {
                      log_debug! { "    {}", term }
                    }
                    for (pred, argss) in tterms.preds() {
                      for args in argss {
                        log_debug! { "    ({} {})", instance[* pred], args }
                      }
                    }
                  }
                  log_debug! { "  }}" }
                }
                curr = Self::merge(
                  instance, pred, & argss, p_def, & curr
                ) ?
              }
              // if_debug! {
              //   log_debug! { "  finally {{" }
              //   let dnf: Vec<_> = (& curr as & Vec<_>).clone() ;
              //   log_debug! { "    {}", TTerms::dnf(dnf) }
              //   log_debug! { "  }}" }
              // }
              for pair in curr {
                def.push(pair)
              }
            }
          },
          utils::ExtractRes::SuccessTrue => {
            bail!("unimplemented, predicate is true")
          },
          utils::ExtractRes::Trivial |
          utils::ExtractRes::SuccessFalse => continue 'clause_iter,
          _ => bail!("failed to extract lhs terms"),
        }
        
      }

      let mut this_pred_increase: usize = 0 ;

      macro_rules! keep_and_continue {
        ($pred:expr) => (
          keep.insert($pred) ;
          continue 'construct
        )
      }

      conf.check_timeout() ? ;
      for clause in lhs_clauses {
        let count = if let Some(argss) = instance[
          * clause
        ].lhs_preds().get(& pred) {
          argss.len()
        } else {
          bail!("inconsistent instance state")
        } ;

        let mut this_increase = def.len() ;
        for _ in 1 .. count {
          if let Some(val) = this_increase.checked_mul( def.len() ) {
            this_increase = val
          } else {
            keep_and_continue! { pred }
          }
        }
        if let Some(val) = this_pred_increase.checked_add(this_increase) {
          this_pred_increase = val
        } else {
          keep_and_continue! { pred }
        }

      }

      let rmed = instance.clauses_of(pred).1.len() ;
      this_pred_increase = if this_pred_increase >= rmed {
        this_pred_increase - rmed
      } else {
        0
      } ;

      if forced_inlining {
        let prev = res.insert( pred, def ) ;
        debug_assert! { prev.is_none() }
      } else {

        if let Some(sum_increase) = this_pred_increase.checked_add(increase) {
          log_info! {
            "  blow-up prediction for {}: {} + {} = {} / {}",
            instance[pred], this_pred_increase, increase,
            sum_increase, upper_bound
          }
          if sum_increase >= upper_bound {
            log_info! { "  -> blows up" }
            keep_and_continue! { pred }
          } else {
            log_info! { "  -> inlining" }
            increase = sum_increase ;
            let prev = res.insert( pred, def ) ;
            debug_assert! { prev.is_none() }
          }
        } else {
          keep_and_continue! { pred }
        }

      }
    }

    Ok( res )
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

      log_debug! { "  " }
    }

    set.shrink_to_fit() ;
    Ok(set)
  }
}
//! Module in charge of constructing an analyzing the graph of dependencies
//! between predicates.

use common::* ;

/// Maps predicates to the predicates they depend on.
pub type Dep = PrdMap< PrdMap<usize> > ;

/// Graph of dependencies.
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
  /// Constructor.
  pub fn new(instance: & Instance) -> Self {
    let mut forward: Dep = vec![
      vec![ 0 ; instance.preds().len() ].into() ; instance.preds().len()
    ].into() ;
    let mut bakward = forward.clone() ;
    let mut neg: PrdMap<_> = vec![ 0 ; instance.preds().len() ].into() ;
    let mut pos: PrdMap<_> = vec![ 0 ; instance.preds().len() ].into() ;

    for clause in instance.clauses() {
      if let Some((tgt, _)) = clause.rhs() {
        if clause.lhs_preds().is_empty() {
          pos[tgt] += 1 ;
        } else {
          for (prd, _) in clause.lhs_preds() {
            bakward[tgt][* prd] += 1 ;
            forward[* prd][tgt] += 1 ;
          }
        }
      } else {
        for (prd, _) in clause.lhs_preds() {
          neg[* prd] += 1 ;
        }
      }
    }

    Graph { forward, bakward, neg, pos }
  }

  /// Dumps a graph in dot format.
  pub fn dot_write<W: Write>(
    & self, w: & mut W, instance: & Instance
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
        writeln!(w, "  p_{} [label = \"{}\"] ;", prd, info.name) ?
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
    & self, instance: & Instance, file: S
  ) -> Res<()> {
    if let Some(
      (mut pred_dep_file, path)
    ) = conf.preproc.pred_dep_file(file) ? {
      use std::process::Command ;
      self.dot_write(& mut pred_dep_file, instance) ? ;
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
}
//! Module in charge of constructing an analyzing the graph of dependencies
//! between predicates.

use common::* ;

/// Maps predicates to the predicates they depend on.
pub type Dep = PrdMap< PrdSet > ;

/// Graph of dependencies.
pub struct Graph {
  /// Forward dependencies.
  forward: Dep,
  /// Backward dependencies.
  bakward: Dep,
  /// Predicates appearing in a negative constraint.
  neg: PrdSet,
  /// Predicates appearing in a positive constraint.
  pos: PrdSet,
}
impl Graph {
  /// Constructor.
  pub fn new(instance: & Instance) -> Self {
    let mut forward: PrdMap<_> = vec![
      PrdSet::with_capacity(10) ; instance.preds().len()
    ].into() ;
    let mut bakward = forward.clone() ;
    let mut neg = PrdSet::with_capacity(10) ;
    let mut pos = PrdSet::with_capacity(10) ;

    for clause in instance.clauses() {
      if let Some(tgt) = clause.rhs().pred() {
        if clause.lhs_preds().is_empty() {
          pos.insert(tgt) ;
        } else {
          for (prd, _) in clause.lhs_preds() {
            bakward[tgt].insert(* prd) ;
            forward[* prd].insert(tgt) ;
          }
        }
      } else {
        for (prd, _) in clause.lhs_preds() {
          neg.insert(* prd) ;
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
    writeln!(
      w, "  top[label=\"\\top\", peripheries=2, color=darkolivegreen3] ;"
    ) ? ;
    writeln!(
      w, "  bot[label=\"\\bot\", peripheries=2, color=indianred1] ;"
    ) ? ;
    for prd in & self.neg {
      writeln!(w, "  p_{} -> bot ;", prd) ?
    }
    for prd in & self.pos {
      writeln!(w, "  top -> p_{} ;", prd) ?
    }
    for (prd, info) in instance.preds().index_iter() {
      if ! (
        self.bakward[prd].is_empty() && self.forward[prd].is_empty()
      ) {
        writeln!(w, "  p_{}[label=\"{}\"] ;", prd, info.name) ?
      }
    }
    for (prd, targets) in self.forward.index_iter() {
      for tgt in targets {
        writeln!(w, "  p_{} -> p_{} ;", prd, tgt) ?
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
      let output = match Command::new("fuck_this_shit").args(
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
        for tgt in targets {
          if ! slf.bakward[* tgt].contains(& prd) {
            bail!(
              "\
                found `{} -> {}` in forward dependencies, \
                but not in backward dependencies\
              ", instance[prd], instance[* tgt]
            )
          }
        }
      }
      for (prd, targets) in slf.bakward.index_iter() {
        for tgt in targets {
          if ! slf.forward[* tgt].contains(& prd) {
            bail!(
              "\
                found `{} -> {}` in backward dependencies, \
                but not in forward dependencies\
              ", instance[prd], instance[* tgt]
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
  pub fn forward_dep(& self, pred: PrdIdx) -> & PrdSet {
    & self.forward[pred]
  }

  /// Predicates this predicate directly depends on.
  pub fn bakward_dep(& self, pred: PrdIdx) -> & PrdSet {
    & self.bakward[pred]
  }
}
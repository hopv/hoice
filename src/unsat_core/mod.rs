//! Unsat core extraction.

use common::* ;

pub mod sample_graph ;

pub use self::sample_graph::SampleGraph ;
use self::sample_graph::UnsatProof ;

/// An unsat result.
pub enum UnsatRes {
  /// Unsat cores were not active.
  None,
  /// A sample dependency graph: raw result from teacher.
  Graph(SampleGraph),
  /// A proof, obtained from a graph.
  Proof(UnsatProof),
  /// An unsat result from a single clause.
  Clause(ClsIdx),
}
impl UnsatRes {
  /// Constructor.
  pub fn new(graph: Option<SampleGraph>) -> Self {
    if let Some(graph) = graph {
      UnsatRes::Graph(graph)
    } else {
      UnsatRes::None
    }
  }

  /// True if none.
  pub fn is_none(& self) -> bool {
    match self { UnsatRes::None => true, _ => false }
  }

  /// Retrieves the unsat core.
  fn get_core(& mut self, instance: & Instance) -> Res<ClsSet> {
    let (nu_self, res) = match self {
      UnsatRes::None => bail!(
        "cannot produce unsat cores without `{}`",
        conf.emph("(set-option :produce-unsat-cores true)")
      ),
      UnsatRes::Graph(graph) => {
        let proof = graph.get_proof(instance) ? ;
        let core = proof.core() ;

        ( UnsatRes::Proof(proof), core )
      },
      UnsatRes::Proof(proof) => return Ok( proof.core() ),
      UnsatRes::Clause(clause) => {
        let mut set = ClsSet::new() ;
        set.insert(* clause) ;
        return Ok(set)
      },
    } ;

    * self = nu_self ;

    Ok(res)
  }

  /// Writes the unsat core.
  pub fn write_core<W: Write>(
    & mut self, w: & mut W, instance: & Instance
  ) -> Res<()> {
    let core = self.get_core(& instance) ? ;
    if ! conf.unsat_cores() {
      bail!(
        "cannot produce unsat cores without `{}`",
        conf.emph("(set-option :produce-unsat-cores true)")
      )
    }
    write!(w, "(") ? ;
    for clause in core {
      if let Some(name) = instance.name_of_old_clause(clause) {
        write!(w, " {}", name) ?
      }
    }
    writeln!(w, " )") ? ;
    Ok(())
  }

  /// Writes an unsat proof.
  pub fn write_proof<W: Write>(
    & mut self, w: & mut W, instance: & Instance
  ) -> Res<()> {
    let err = || ErrorKind::from(
      format!(
        "cannot produce proof without `{}`",
        conf.emph("(set-option :produce-proofs true)")
      )
    ) ;
    let nu_self = match self {
      _ if ! conf.proofs() => bail!( err() ),
      UnsatRes::None => bail!( err() ),
      UnsatRes::Graph(graph) => {
        let proof = graph.get_proof(instance) ? ;
        proof.write(w, instance) ? ;

        UnsatRes::Proof(proof)
      },
      UnsatRes::Proof(proof) => {
        proof.write(w, instance) ? ;
        return Ok(())
      },
      UnsatRes::Clause(_) => {
        writeln!(w, "( () () () )") ? ;
        return Ok(())
      },
    } ;

    * self = nu_self ;

    Ok(())
  }
}

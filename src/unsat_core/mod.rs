//! Unsat core extraction.
//!
//! Currently inactive.

use common::*;

pub mod entry_points;
pub mod sample_graph;

use self::entry_points::Entry;

pub use self::sample_graph::SampleGraph;
// use self::sample_graph::UnsatProof;

/// An unsat result.
pub enum UnsatRes {
    /// Unsat cores were not active.
    None,
    // /// A sample dependency graph: raw result from teacher.
    // Graph(SampleGraph),
    // /// A proof, obtained from a graph.
    // Proof(UnsatProof),
    // /// An unsat result from a single clause.
    // Clause(ClsIdx),
    /// Some entry points.
    Entry(Entry),
}
impl UnsatRes {
    /// Constructor.
    pub fn new(entry: Option<Entry>) -> Self {
        if let Some(entry) = entry {
            UnsatRes::Entry(entry)
        } else {
            UnsatRes::None
        }
    }

    /// True if none.
    pub fn is_none(&self) -> bool {
        match self {
            UnsatRes::None => true,
            _ => false,
        }
    }

    /// Tries to retrieve the unsat proof.
    fn get_proof(&self, instance: &Instance, original: &Instance) -> Res<Option<Entry>> {
        match self {
            UnsatRes::None => Ok(None),
            UnsatRes::Entry(entry) => Ok(Some(entry.reconstruct(instance, original)?)),
        }
    }

    /// Tries to write the unsat proof.
    pub fn write_proof<W: Write>(
        &self,
        w: &mut W,
        instance: &Instance,
        original: &Instance,
    ) -> Res<()> {
        if let Some(entry) = self.get_proof(instance, original)? {
            writeln!(w, "(")?;
            for sample in &entry.samples {
                writeln!(w, "  ({} {})", instance[sample.pred], sample.args)?
            }
            writeln!(w, ")")?;
        } else {
            bail!(
                "cannot produce unsat proof without `{}`",
                conf.emph("(set-option :produce-unsat-proof true)")
            )
        }
        Ok(())
    }
}

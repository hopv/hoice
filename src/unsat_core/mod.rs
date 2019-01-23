//! Unsat core and proof extraction.
//!
//! Right now, only unsat proof in the form of [`entry_points`] is active.
//!
//! [`entry_points`]: entry_points/index.html (entry_points module)

use crate::common::*;

pub mod entry_points;
mod sample_graph;

pub use self::entry_points::Entry;

/// An unsat result.
pub enum UnsatRes {
    /// Unsat cores were not active.
    None,
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

    /// Empty entry constructor.
    pub fn empty_entry() -> Self {
        UnsatRes::Entry(Entry::new(entry_points::SampleSet::new()))
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

use crate::{common::*, data::Constraint};

/// Maintains information about the constraints.
#[derive(Clone)]
pub struct CstrInfo {
    /// Set of negative constraints, for constraint pruning.
    neg_constraints: CstrSet,
    /// Constraints that have changed or are new since the last reset.
    modded_constraints: CstrSet,
}
impl CstrInfo {
    /// Constructor.
    pub fn new() -> Self {
        CstrInfo {
            neg_constraints: CstrSet::with_capacity(11),
            modded_constraints: CstrSet::with_capacity(11),
        }
    }

    /// Modified constraints accessor.
    pub fn modded(&self) -> &CstrSet {
        &self.modded_constraints
    }

    /// Negative constraints accessor.
    pub fn neg(&self) -> &CstrSet {
        &self.neg_constraints
    }

    /// Clears modified constraints.
    pub fn clear_modded(&mut self) {
        self.modded_constraints.clear()
    }

    /// Forget a constraint.
    ///
    /// Used when tautologizing.
    pub fn forget(&mut self, constraint: CstrIdx) {
        self.neg_constraints.remove(&constraint);
        self.modded_constraints.remove(&constraint);
        ()
    }

    /// Registers a constraint as modified.
    ///
    /// Error if the constraint is a tautology.
    pub fn register_modded(&mut self, index: CstrIdx, constraint: &Constraint) -> Res<()> {
        if constraint.is_tautology() {
            bail!("registering tautology")
        }
        self.modded_constraints.insert(index);
        if constraint.rhs().is_none() {
            self.neg_constraints.insert(index);
        }
        Ok(())
    }
}

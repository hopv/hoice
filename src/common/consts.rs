//! Constants of the crate.

/// Language keywords.
pub mod keywords {
  /// Predicate declaration keyword.
  pub static prd_dec: & 'static str = "declare-fun" ;
  /// Clause definition keyword.
  pub static clause_def: & 'static str = "clause" ;
  /// Assertion keyword.
  pub static assert: & 'static str = "assert" ;
  /// Forall keyword.
  pub static forall: & 'static str = "forall" ;
  /// Exists keyword.
  pub static exists: & 'static str = "exists" ;
  /// Check sat keyword.
  pub static check_sat: & 'static str = "check-sat" ;
}
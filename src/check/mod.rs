#![doc = r#"Checks the result of a `hoice` run.

This code is completely separated from the rest of the code, on purpose. It
basically takes the original `hc` file, a file containing the output of the
`hoice` run, and checks that the result makes sense.

It does so using an SMT solver, and performing string substitution (roughly)
to rewrite the problem as a pure SMT query. In particular, there is no real
notion of term here."#]

pub mod parse ;

/// A predicate is just a string.
pub type Pred = String ;
/// A type is just a string.
pub type Typ = String ;
/// A signature.
pub type Sig = Vec<Typ> ;

/// A predicate declaration.
pub struct PredDec {
  /// Predicate.
  pub pred: Pred,
  /// Signature.
  pub sig: Sig,
}

/// An ident is just a string.
pub type Ident = String ;
/// A list of arguments.
pub type Args = Vec<(Ident, Typ)> ;
/// A term is just a string.
pub type Term = String ;

/// A predicate definition.
pub struct PredDef {
  /// Predicate.
  pub pred: Pred,
  /// Arguments.
  pub args: Args,
  /// Body.
  pub body: Term,
}

/// A clause.
pub struct Clause {
  /// Arguments.
  pub args: Args,
  /// LHS.
  pub lhs: Vec<Term>,
  /// RHS.
  pub rhs: Term,
}
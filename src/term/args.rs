//! Hash-consed arguments for predicate applications.

use hashconsing::HConsed ;

use common::* ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<VarMap<Term>> > ;

lazy_static! {
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa / 10 )
  ) ;
}

/// Hashconsed arguments for predicate applications.
pub type HTArgs = HConsed< VarMap<Term> > ;
/// Set of hashconsed arguments for predicate applications.
pub type HTArgss = HConSet<HTArgs> ;

/// Creates some new arguments.
pub fn new(args: VarMap<Term>) -> HTArgs {
  use hashconsing::HConser ;
  factory.mk(args)
}
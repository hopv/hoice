/*! Hashconsed maps from variables to terms.
*/

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
pub type VarTerms = HConsed< VarMap<Term> > ;
/// Set of hashconsed arguments for predicate applications.
pub type VarTermsSet = HConSet<VarTerms> ;
///  Map from arguments for predicate applications to something.
pub type VarTermsMap<T> = HConMap<VarTerms, T> ;

/// Creates some new arguments.
pub fn new(args: VarMap<Term>) -> VarTerms {
  use hashconsing::HConser ;
  factory.mk(args)
}
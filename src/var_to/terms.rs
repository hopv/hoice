/*! Hashconsed maps from variables to terms.
*/

use hashconsing::{HConsed, HashConsign};

use crate::common::*;

hashconsing::consign! {
    /// Term factory.
    let factory = consign(conf.instance.term_capa / 10) for VarMap<Term> ;
}

/// Hashconsed arguments for predicate applications.
pub type VarTerms = HConsed<VarMap<Term>>;
/// Set of hashconsed arguments for predicate applications.
pub type VarTermsSet = HConSet<VarTerms>;
///  Map from arguments for predicate applications to something.
pub type VarTermsMap<T> = HConMap<VarTerms, T>;

/// Creates some new arguments.
pub fn new(args: VarMap<Term>) -> VarTerms {
    factory.mk(args)
}

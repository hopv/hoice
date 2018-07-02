//! Types for zipping over terms.

use common::* ;

use std::slice::Iter ;

/// Zip info for terms.
#[allow(dead_code)]
enum TermDer<'a, Info> {
  /// Constant array.
  CArray,

  /// Operator application.
  App {
    /// Operator.
    op: Op,
    /// Info already processed.
    lft_args: Info,
    /// Kids left to process.
    rgt_args: Iter<'a, Term>,
  },

  /// Datatype constructor.
  DTypNew {
    /// Type of the application.
    typ: Typ,
    /// Name of the constructor.
    name: String,
    /// Kids already processed.
    lft_args: Info,
    /// Kids left to process.
    rgt_args: Iter<'a, Term>,
  }
}


// /// Zips over a term.
// pub fn zip<CstF, ArrayF>(
//   term: & Term,
//   cst
// )

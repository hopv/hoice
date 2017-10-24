//! Zero-cost wrappers for safe indexing.

use std::io::Write ;
use std::fmt ;

use rsmt2::to_smt::* ;

use common::SmtRes ;

wrap_usize!{
  #[doc = "Predicate indices."]
  PrdIdx
  #[doc = "Range over predicates."]
  range: PrdRange
  #[doc = "Set of predicates."]
  set: PrdSet
  #[doc = "Hash map from predicates to something."]
  hash map: PrdHMap
  #[doc = "Total map from predicates to something."]
  map: PrdMap with iter: PrdMapIter
}


wrap_usize!{
  #[doc = "Variable indices."]
  VarIdx
  #[doc = "Range over variables."]
  range: VarRange
  #[doc = "Set of variables."]
  set: VarSet
  #[doc = "Hash map from variables to something."]
  hash map: VarHMap
  #[doc = "Total map from variables to something."]
  map: VarMap with iter: VarMapIter
}
impl VarIdx {
  /// Default way to write variables: `v_<idx>`.
  pub fn default_write<W>(& self, w: & mut W) -> ::std::io::Result<()>
  where W: Write {
    write!(w, "v_{}", self)
  }
  /// Default string representation of a variable.
  pub fn default_str(& self) -> String {
    let mut s = vec![] ;
    self.default_write(& mut s).unwrap() ;
    ::std::str::from_utf8(& s).unwrap().into()
  }
}

impl<T: fmt::Display> fmt::Display for VarMap<T> {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "(") ? ;
    for_first!{
      self.iter() => {
        |fst| write!(fmt, "{}", fst) ?,
        then |nxt| write!(fmt, ",{}", nxt)?
      }
    }
    write!(fmt, ")")
  }
}

impl<T: Copy> Sym2Smt<T> for VarIdx {
  fn sym_to_smt2<Writer>(
    & self, w: & mut Writer, _: T
  ) -> SmtRes<()> where Writer: Write {
    self.default_write(w) ? ;
    Ok(())
  }
}

impl<T: Copy> Expr2Smt<T> for VarIdx {
  fn expr_to_smt2<Writer>(
    & self, w: & mut Writer, _: T
  ) -> SmtRes<()> where Writer: Write {
    self.sym_to_smt2(w, & ())
  }
}


wrap_usize!{
  #[doc = "Arity."]
  Arity
  #[doc = "Range over arity."]
  range: ArityRange
  #[doc = "Total map from Arity to something."]
  map: ArityMap with iter: ArityMapIter
}


wrap_usize!{
  #[doc = "Clause indices."]
  ClsIdx
  #[doc = "Range over variables."]
  range: ClsRange
  #[doc = "Set of variables."]
  set: ClsSet
  #[doc = "Hash map from variables to something."]
  hash map: ClsHMap
  #[doc = "Total map from variables to something."]
  map: ClsMap with iter: ClsMapIter
}
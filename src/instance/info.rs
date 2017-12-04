//! Types to store information about variables and predicates.

use common::* ;
use super::Typ ;


/// Variable info.
#[derive(Clone)]
pub struct VarInfo {
  /// Variable's name.
  pub name: String,
  /// Variable's type.
  pub typ: Typ,
  /// Variable's index.
  pub idx: VarIdx,
  /// Is the variable active?
  pub active: bool,
}
impl VarInfo {
  /// Constructor.
  pub fn new(name: String, typ: Typ, idx: VarIdx) -> Self {
    VarInfo { name, typ, idx, active: true }
  }
  /// Name of the variable as bytes.
  pub fn as_bytes(& self) -> & [u8] {
    self.name.as_bytes()
  }
}
impl ::rsmt2::to_smt::Sym2Smt<()> for VarInfo {
  fn sym_to_smt2<Writer>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> where Writer: Write {
    write!(w, "v{}", self.idx) ? ;
    Ok(())
  }
}
impl_fmt!{
  VarInfo(self, fmt) {
    fmt.write_str(& self.name)
  }
}


/// Predicate info.
pub struct PrdInfo {
  /// Predicate's name.
  pub name: String,
  /// Predicate's index.
  pub idx: PrdIdx,
  /// Signature.
  pub sig: VarMap<Typ>,
  /// Maps arguments to an `active` flag. If it's true, it means the argument
  /// is relevant for the predicate in question. Used to restrict the
  /// qualifiers considered for each predicate.
  pub var_active: VarMap<bool>,
}
impl PrdInfo {
  /// Name of the variable as bytes.
  pub fn as_bytes(& self) -> & [u8] {
    self.name.as_bytes()
  }
}
impl_fmt!{
  PrdInfo(self, fmt) {
    fmt.write_str(& self.name)
  }
}
impl ::rsmt2::to_smt::Sym2Smt<()> for PrdInfo {
  fn sym_to_smt2<Writer: Write>(
    &self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "p_{}", self.idx) ? ;
    Ok(())
  }
}
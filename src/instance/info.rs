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
}
impl VarInfo {
  /// Name of the variable as bytes.
  pub fn as_bytes(& self) -> & [u8] {
    self.name.as_bytes()
  }
}
impl ::rsmt2::Sym2Smt<()> for VarInfo {
  fn sym_to_smt2<Writer>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> where Writer: Write {
    smt_cast_io!(
      "while writing variable as smt2" => write!(w, "v{}", self.idx)
    )
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
  pub sig: VarMap<Typ>
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
impl ::rsmt2::Sym2Smt<()> for PrdInfo {
  fn sym_to_smt2<Writer: Write>(
    &self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> {
    smt_cast_io!(
      "while writing predicate as symbol"
      => write!(w, "p_{}", self.idx)
    )
  }
}
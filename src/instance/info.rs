//! Types to store information about variables and predicates.

use rsmt2::print::Sym2Smt ;

use common::* ;

use super::Typ ;

/// Variable info.
#[derive(Clone, Debug)]
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
impl Sym2Smt<()> for VarInfo {
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
#[derive(Clone)]
pub struct PrdInfo {
  /// Predicate's name.
  pub name: String,
  /// Predicate's index.
  pub idx: PrdIdx,
  /// Signature.
  pub sig: VarMap<Typ>,
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
impl Sym2Smt<()> for PrdInfo {
  fn sym_to_smt2<Writer: Write>(
    &self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "p_{}", self.idx) ? ;
    Ok(())
  }
}
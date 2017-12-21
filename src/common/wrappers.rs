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

impl VarMap<::term::Val> {
  /// Evaluates some arguments and yields the resulting `VarMap`.
  pub fn apply_to(
    & self, args: & VarMap<::term::Term>
  ) -> ::errors::Res<Self> {
    let mut res = Self::with_capacity( args.len() ) ;
    for arg in args {
      res.push( arg.eval(self) ? )
    }
    Ok(res)
  }
}

impl VarMap< ::term::Term > {
  /// Removes the arguments of indices **not** in the set. Preserves the order.
  ///
  /// This is used when useless arguments are detected, to slice predicate
  /// applications.
  pub fn remove(& mut self, to_keep: & VarSet) {
    debug_assert! { self.len() >= to_keep.len() }
    debug_assert! {{
      let mut okay = true ;
      for var in to_keep {
        if * var >= self.len() {
          okay = false ; break
        }
      }
      okay
    }}
    let mut old_vars = VarMap::with_capacity( to_keep.len() ) ;
    ::std::mem::swap( & mut old_vars, self ) ;
    for (var, term) in old_vars.into_index_iter() {
      if to_keep.contains(& var) {
        self.push(term)
      }
    }
  }
}

impl<T: fmt::Display> fmt::Display for VarMap<T> {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    for_first!{
      self.iter() => {
        |fst| write!(fmt, "{}", fst) ?,
        then |nxt| write!(fmt, " {}", nxt) ?
      }
    }
    Ok(())
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
  #[doc = "Range over clauses."]
  range: ClsRange
  #[doc = "Set of clauses."]
  set: ClsSet
  #[doc = "Hash map from clauses to something."]
  hash map: ClsHMap
  #[doc = "Total map from clauses to something."]
  map: ClsMap with iter: ClsMapIter
}


wrap_usize! {
  #[doc = "Clause cluster indices."]
  CtrIdx
  #[doc = "Ranger over clusters."]
  range: CtrRange
  #[doc = "Set of clusters."]
  set: CtrSet
  #[doc = "Hash map from clusters to something."]
  hash map: CtrHMap
  #[doc = "Total map from clusters to something."]
  map: CtrMap with iter: CtrMapIter
}

wrap_usize!{
  #[doc = "Constraint index."]
  CstrIdx
  #[doc = "Constraint set."]
  set: CstrSet
  #[doc = "Constraint total map."]
  map: CstrMap with iter: CstrMapIter
}


wrap_usize!{
  #[doc = "Learner index."]
  LrnIdx
  #[doc = "Map of learners"]
  hash map: LrnHMap
  #[doc = "Total map from learners to something."]
  map: LrnMap with iter: LrnMapIter
}
unsafe impl Send for LrnIdx {}


wrap_usize!{
  #[doc = "Teacher Assistant index."]
  TAsIdx
  #[doc = "Map of TAs."]
  hash map: TAsHMap
  #[doc = "Total map from TAs to something."]
  map: TAsMap with iter: TAsMapIter
}
unsafe impl Send for TAsIdx {}
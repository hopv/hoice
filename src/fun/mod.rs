/*! Hash consed functions.

Note that [`Fun`][fun] is extended by [`FunExt`][fun ext] to allow

- retrieving the name of the function,
- defining the function in a solver.

[fun]: type.Fun.html (Fun type)
[fun ext]: trait.FunExt.html (FunExt trait)
*/

use hashconsing::{ HashConsign, HConser, HConsed } ;

use common::* ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<RFun> > ;

lazy_static! {
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa )
  ) ;
}

/// A hash consed function.
pub type Fun = HConsed<RFun> ;


/// Defines all functions.
pub fn define_all<P>(solver: & mut Solver<P>) -> Res<()> {
  if let Ok(f) = factory.read() {
    f.fold_res(
      (), |_, fun| fun.define(solver).map(|_| ())
    )
  } else {
    bail!("failed to lock factory")
  }
}


/// Extends [`Fun`][fun] with function declaration.
///
/// [fun]: type.Fun.html (Fun type)
pub trait FunExt {
  /// Defines itself as a function.
  ///
  /// Returns the name of the function.
  fn define<P>(& self, & mut Solver<P>) -> Res<String> ;
  /// Name of the function.
  fn name(& self) -> String ;
}
impl FunExt for Fun {
  fn define<P>(& self, solver: & mut Solver<P>) -> Res<String> {
    use smt::SmtTerm ;
    let name = self.name() ;
    let sig: Vec<_> = self.sig.index_iter().map(
      |(var, typ)| (var, typ.get())
    ).collect() ;
    solver.define_fun(
      & name, & sig, self.out.get(), & SmtTerm::new(& self.def)
    ) ? ;
    Ok(name)
  }
  fn name(& self) -> String {
    format!("hoice_reserved_fun_{}", self.uid())
  }
}



/// Creates a hash consed function.
pub fn mk<F: Into<RFun>>(val: F) -> Fun {
  factory.mk(val.into())
}

/// Functions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RFun {
  /// Input signature.
  sig: Sig,
  /// Output type.
  out: Typ,
  /// Definition.
  def: Term,
}
impl RFun {
  /// Constructor.
  pub fn new(sig: Sig, out: Typ, def: Term) -> Self {
    debug_assert_eq! { out, def.typ() }
    RFun { sig, out, def }
  }

  /// Signature accessor.
  pub fn sig(& self) -> (& Sig, & Typ) {
    (& self.sig, & self.out)
  }

  /// Definition accessor.
  pub fn def(& self) -> & Term {
    & self.def
  }

  /// Function evaluation.
  pub fn eval<E: Evaluator>(& self, model: & E) -> Res<Val> {
    debug_assert_eq! { self.sig.len(), model.len() }
    debug_assert! {{
      for (var, typ) in self.sig.index_iter() {
        debug_assert_eq! { * typ, model.get(var).typ() }
      }
      true
    }}
    self.def.eval(model)
  }
}



impl Into<RFun> for (Sig, Term) {
  fn into(self) -> RFun {
    let (sig, term) = self ;
    RFun::new(sig, term.typ(), term)
  }
}

impl Into<RFun> for (Sig, Typ, Term) {
  fn into(self) -> RFun {
    let (sig, out, term) = self ;
    RFun::new(sig, out, term)
  }
}
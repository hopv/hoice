//! Hash consed functions.
//!
//! # TODO
//!
//! Move this in the instance to avoid the unsafe code to borrow definitions.

use std::sync::{
  RwLockReadGuard, RwLockWriteGuard
} ;

use common::* ;

/// A function.
pub type Fun = Arc<RFun> ;

/// Type of the function factory.
///
/// The usize indicates whether an element of the factory is being borrowed
/// **unsafely** by [`get_as_ref`](fun/fn.get_as_ref.html). If it is true, then
/// borrowing the factory mutably is unsafe.
///
/// To avoid problems, **always** use the `factory` macro to access the
/// factory.
type Factory = RwLock< (BTreeMap<String, Fun>, usize) > ;
lazy_static! {
  /// Function factory.
  static ref factory: Factory = RwLock::new(
    ( BTreeMap::new(), 0 )
  ) ;
}

/// Read version of the factory.
fn read_factory<'a>() -> RwLockReadGuard<
  'a, (BTreeMap<String, Fun>, usize)
> {
  if let Ok(res) = factory.read() {
    res
  } else {
    panic!("failed to access function factory (read)")
  }
}
/// Write version of the factory.
fn write_factory<'a>() -> RwLockWriteGuard<
  'a, (BTreeMap<String, Fun>, usize)
> {
  loop {
    if let Ok(res) = factory.write() {
      if res.1 != 0 { continue }
      return res
    } else {
      panic!("failed to access function factory (write)")
    }
  }
}

macro_rules! factory {
  (read) => (& read_factory().0) ;
  (write) => (& mut write_factory().0) ;
}


/// Creates a function definition.
pub fn mk(fun: RFun) -> Res<Fun> {
  let fun = Arc::new( fun ) ;
  let f = factory!(write) ;
  let prev = f.insert( fun.name.clone(), fun.clone() ) ;

  if let Some(prev) = prev {
    bail!("attempting to redefine function `{}`", prev.name)
  }

  Ok(fun)
}



/// Defines all the functions.
pub fn write_all<W: Write>(w: & mut W) -> Res<()> {
  let f = factory!(read) ;

  if f.is_empty() { return Ok(()) }

  let mut set = BTreeSet::new() ;

  let mut all = vec![] ;

  for fun in f.values() {
    let do_it = set.insert(& fun.name) ;
    if ! do_it { continue }

    debug_assert! { all.is_empty() }

    all.reserve( fun.deps.len() + 1 ) ;
    all.push(fun) ;
    for dep in & fun.deps {
      set.insert(dep) ;
      if let Some(dep) = f.get(dep) {
        all.push(dep)
      } else {
        bail!(
          "function `{}` depends on unknown function `{}`",
          conf.emph(& fun.name), conf.bad(& dep)
        )
      }
    }

    writeln!(w, "(define-funs-rec (") ? ;

    // Write all signatures.
    for fun in & all {
      write!(w, "  (") ? ;
      write!(w, "{} (", fun.name) ? ;
      for info in & fun.sig {
        write!(w, " ({} {})", info.idx.default_str(), info.typ) ?
      }
      writeln!(w, " ) {})", fun.typ) ?
    }

    writeln!(w, ") (") ? ;

    // Write all definitions.
    for fun in all.drain( 0 .. ) {
      write!(w, "  ") ? ;
      fun.def.write(
        w, |w, var| var.default_write(w)
      ) ? ;
      writeln!(w) ?
    }

    writeln!(w, ") )") ?
  }

  writeln!(w) ? ;

  Ok(())
}



/// Retrieves the definition of a function as a reference.
///
/// This actually uses unsafe code, this kind of borrow should not be possible.
/// If something modifies the factory while the borrow is alive, then it might
/// end up pointing to arbitrary data.
///
/// It's made safe by keeping track of how many references have been created
/// and preventing modifying the factory as long as this count is not zero.
/// This function hence works in conjunction with [`decrease_ref_count`][link].
/// When using this function, you must keep track of how many references you
/// have created and when you are sure they're dead, call `decrease_ref_count`.
///
/// link: fun/fn.decrease_ref_count.html
/// (decrease_ref_count function)
pub fn get_as_ref<'a>(name: & 'a str) -> Option<& 'a Fun> {
  let mut pair = if let Ok(mut f) = factory.write() {
    f
  } else {
    panic!("failed to access function factory (write)")
  } ;
  pair.1 += 1 ;
  unsafe {
    ::std::mem::transmute::<Option<& Fun>, Option<& 'a Fun>>(
      pair.0.get(name)
    )
  }
}

pub fn decrease_ref_count(count: usize) {
  if count == 0 { return () }
  if let Ok(mut f) = factory.write() {
    if count <= f.1 {
      f.1 -= count
    } else {
      panic!("trying to decrease ref count for function factory by too much")
    }
  } else {
    panic!("failed to access function factory (write)")
  }
}



/// Retrieves the definition of a function.
pub fn get(name: & str) -> Option<Fun> {
  let f = factory!(read) ;
  f.get(name).cloned()
}


/// Types and creates a function application.
pub fn type_apply(
  name: String, var_info: & VarInfos, out: & Typ, args: Vec<Term>
) -> Result<Term, ::errors::TypError> {
  if args.len() != var_info.len() {
    return Err(
      TypError::Msg(
        format!(
          "function `{}` is applied to {} arguments, expected {}",
          conf.emph(name), args.len(), var_info.len()
        )
      )
    )
  }

  for (arg, info) in args.iter().zip( var_info.iter() ) {
    if ! arg.typ().is_compatible( & info.typ ) {
      return Err(
        TypError::Typ {
          expected: Some( info.typ.clone() ),
          obtained: arg.typ().clone(),
          index: * info.idx,
        }
      )
    }
  }

  Ok(
    term::fun( out.clone(), name, args )
  )
}


/// Creates a function application.
pub fn apply(
  name: String, args: Vec<Term>
) -> Result<Term, ::errors::TypError> {
  use ::errors::TypError ;

  let def = if let Some(def) = get(& name) { def } else {
    return Err(
      TypError::Msg( format!("unknown function `{}`", conf.bad(name)) )
    )
  } ;

  type_apply(name, & def.sig, & def.typ, args)
}






/// Real structure for functions.
#[derive(Debug, Clone)]
pub struct RFun {
  /// Name.
  pub name: String,
  /// Other functions this function depends on.
  pub deps: BTreeSet<String>,
  /// Signature.
  ///
  /// The string stored is the original name of the argument.
  pub sig: VarInfos,
  /// Type.
  pub typ: Typ,
  /// Definition.
  pub def: Term,
}

impl PartialEq for RFun {
  fn eq(& self, other: & Self) -> bool {
    self.name == other.name
  }
}
impl Eq for RFun {}

impl PartialOrd for RFun {
  fn partial_cmp(& self, other: & Self) -> Option< ::std::cmp::Ordering > {
    self.name.partial_cmp(& other.name)
  }
}
impl Ord for RFun {
  fn cmp(& self, other: & Self) -> ::std::cmp::Ordering {
    self.name.cmp(& other.name)
  }
}

impl ::std::hash::Hash for RFun {
  fn hash<H: ::std::hash::Hasher>(& self, state: & mut H) {
    self.name.hash(state)
  }
}

impl RFun {
  /// Constructor.
  ///
  /// The dependencies are initially empty, and the definition is set to
  /// `true`.
  pub fn new<S: Into<String>>(
    name: S, sig: VarInfos, typ: Typ
  ) -> Self {
    let name = name.into() ;
    RFun { name, deps: BTreeSet::new(), sig, typ, def: term::tru() }
  }

  /// Insert a dependency.
  ///
  /// Only inserts if `dep` is not `self.name`.
  pub fn insert_dep<S: Into<String>>(& mut self, dep: S) -> bool {
    let dep = dep.into() ;
    if self.name == dep {
      false
    } else {
      self.deps.insert(dep)
    }
  }

  /// Sets the definition of a function.
  ///
  /// # Panics
  ///
  /// - if `self.def` is not `term::tru()`
  pub fn set_def(& mut self, def: Term) {
    match * self.def {
      RTerm::Cst(ref cst) if cst.is_true() => (),
      _ => panic!("trying to set the definition of a function twice"),
    }
    self.def = def
  }

  /// Checks the function is legal.
  pub fn check(& self) -> Res<()> {
    for dep in & self.deps {
      if get(dep).is_none() {
        bail!(
          "function `{}` depends on unknown function `{}`",
          conf.emph(& self.name), conf.bad(dep)
        )
      }
    }
    Ok(())
  }
}





/// Stores functions from and to some type.
#[derive(Debug, Clone)]
pub struct Functions {
  /// Type these functions are for.
  pub typ: Typ,
  /// Functions from this type to another one.
  pub from_typ: Vec<Fun>,
  /// Function from another type to this one.
  pub to_typ: Vec<Fun>,
  /// Functions from this type to itself.
  pub from_to_typ: Vec<Fun>,
}
impl Functions {

  /// Constructor.
  pub fn new(typ: Typ) -> Self {
    let f = factory!(read) ;

    let mut from_typ = vec![] ;
    let mut to_typ = vec![] ;
    let mut from_to_typ = vec![] ;

    'find_funs: for fun in f.values() {
      let mut sig = fun.sig.iter() ;

      let ftyp = match sig.next() {
        Some(info) => info.typ == typ && sig.next().is_none(),
        _ => false,
      } ;

      let ttyp = fun.typ == typ ;

      match (ftyp, ttyp) {
        (true, true) => from_to_typ.push( fun.clone() ),
        (true, false) => from_typ.push( fun.clone() ),
        (false, true) => to_typ.push( fun.clone() ),
        (false, false) => continue 'find_funs,
      }
    }

    Functions { typ, from_typ, to_typ, from_to_typ }
  }

}
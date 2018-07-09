//! Hash consed functions.

use common::* ;

/// A function.
pub type Fun = Arc<RFun> ;

/// Type of the function factory.
type Factory = RwLock< BTreeMap<String, Fun> > ;
lazy_static! {
  /// Function factory.
  static ref factory: Factory = RwLock::new(
    BTreeMap::new()
  ) ;
}

/// Creates a function definition.
pub fn mk(fun: RFun) -> Res<Fun> {
  let fun = Arc::new( fun ) ;
  let prev = if let Ok(mut f) = factory.write() {
    f.insert( fun.name.clone(), fun.clone() )
  } else {
    bail!("failed to access function factory (write)")
  } ;

  if let Some(prev) = prev {
    bail!("attempting to redefine function `{}`", prev.name)
  }

  Ok(fun)
}



/// Defines all the functions.
pub fn write_all<W: Write>(w: & mut W) -> Res<()> {
  let f = if let Ok(f) = factory.read() {
    f
  } else {
    bail!("failed to access function factory (read)")
  } ;

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




/// Retrieves the definition of a function.
pub fn get(name: & str) -> Option<Fun> {
  if let Ok(f) = factory.read() {
    f.get(name).cloned()
  } else {
    panic!("failed to access function factory (read)")
  }
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
}
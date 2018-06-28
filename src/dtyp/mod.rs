//! Datatypes.

use common::* ;

wrap_usize!{
  #[doc = "Type parameter indices."]
  TPrmIdx
  #[doc = "Total map from type parameters to something."]
  map: TPrmMap with iter: TPrmMapIter
}

wrap_usize!{
  #[doc = "Constructor argument indices."]
  CArgIdx
  #[doc = "Total map from constructor arguments to something."]
  map: CArgMap with iter: CArgMapIter
}

/// A concrete type, a polymorphic type, a datatype or a type parameter.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PartialTyp {
  /// Array.
  Array(Box<PartialTyp>, Box<PartialTyp>),

  // /// List,
  // List(PartialTyp),

  /// Datatype.
  DTyp(String, ::parse::Pos, TPrmMap<PartialTyp>),
  /// Concrete type.
  Typ(Typ),
  /// Type parameter.
  Param(TPrmIdx),
}
impl From<Typ> for PartialTyp {
  fn from(typ: Typ) -> Self {
    PartialTyp::Typ(typ)
  }
}
impl PartialTyp {
  /// Resolves a partial type against a type.
  pub fn unify (
    & self, typ: & Typ, map: & mut TPrmMap<Typ>
  ) -> Res<()> {
    let mut stack = vec![ (self, typ) ] ;

    while let Some((ptyp, typ)) = stack.pop() {
      use typ::RTyp ;

      match ( ptyp, typ.get() ) {
        ( PartialTyp::Array(p_src, p_tgt), RTyp::Array { src, tgt } ) => {
          stack.push( (p_src, src) ) ;
          stack.push( (p_tgt, tgt) )
        },

        ( PartialTyp::Typ(p_typ), _ ) => if ! p_typ.is_compatible(typ) {
          bail!("cannot unify type {} and {}", ptyp, typ)
        },

        ( PartialTyp::Param(idx), _ ) => if let Some(merged) = typ.merge(
          & map[* idx]
        ) {
          map[* idx] = merged
        } else {
          bail!("cannot unify type {} and {}", ptyp, typ)
        },

        _ => unimplemented!(),
      }
    }

    Ok(())
  }




  fn write<W: Write>(
    & self, w: & mut W, prms: & TPrmMap<String>
  ) -> Res<()> {
    let mut stack = vec![ ("", self, "") ] ;

    while let Some((sep, typ, close)) = stack.pop() {
      write!(w, "{}", sep) ? ;
      match typ {
        PartialTyp::Array(src, tgt) => {
          stack.push( (" ", & ** tgt, ")") ) ;
          stack.push( (" ", & ** src, "") )
        },
        PartialTyp::DTyp(name, _, prms) => {
          write!(w, "({}", name) ? ;
          let mut first = true ;
          for sub in prms.iter().rev() {
            let close = if first {
              first = false ;
              ")"
            } else {
              ""
            } ;
            stack.push( (" ", sub, close) )
          }
        },
        PartialTyp::Typ(typ) => write!(w, "{}", typ) ?,
        PartialTyp::Param(idx) => write!(w, "{}", prms[* idx]) ?,
      }
      write!(w, "{}", close) ?
    }

    Ok(())
  }



  /// Checks a partial type is legal.
  pub fn check(& self) -> Result<(), (::parse::Pos, String)> {
    let mut stack = vec![self] ;

    while let Some(ptyp) = stack.pop() {
      if let PartialTyp::DTyp(name, pos, args) = ptyp {
        if get(name).is_err() {
          return Err((
            * pos, format!("unknown sort `{}`", name)
          ))
        }
        for arg in args {
          stack.push(arg)
        }
      }
    }

    Ok(())
  }
}

impl_fmt! {
  PartialTyp(self, fmt) {
    let mut stack = vec![ (self, "".to_string()) ] ;

    while let Some((typ, post)) = stack.pop() {

      match typ {
        PartialTyp::Array(src, tgt) => {
          write!(fmt, "(Array ") ? ;
          stack.push(
            ( tgt, format!("){}", post) )
          ) ;
          stack.push(
            ( src, " ".into() )
          )
        },

        PartialTyp::Typ(typ) => write!(fmt, "{}{}", typ, post) ?,

        PartialTyp::Param(idx) => write!(fmt, "'{}", idx) ?,

        PartialTyp::DTyp(dtyp, _, typs) => {
          write!(fmt, "({} ", dtyp) ? ;
          let mut first = true ;
          for typ in typs.iter().rev() {
            let post = if first {
              first = false ;
              ")"
            } else {
              " "
            } ;
            stack.push( (typ, post.into()) )
          }
        },
      }

    }

    Ok(())
  }
}


/// A datatype.
pub type DTyp = Arc<RDTyp> ;

/// Constructor arguments.
pub type CArgs = Vec<(String, PartialTyp)> ;




/// Type of the datatype factory.
type Factory = RwLock< BTreeMap<String, DTyp> > ;
lazy_static! {
  /// Datatype factory.
  static ref factory: Factory = RwLock::new(
    BTreeMap::new()
  ) ;
  /// Map from constructors to datatypes.
  static ref constructor_map: Factory = RwLock::new(
    BTreeMap::new()
  ) ;
}


/// Creates a datatype.
///
/// Will fail if either
///
/// - the datatype already exists
/// - one of the constructors of the datatype already exists
/// - can't access the datatype map
pub fn mk(dtyp: RDTyp) -> Res<DTyp> {
  let name = dtyp.name.clone() ;
  let to_insert = Arc::new(dtyp) ;
  let dtyp = to_insert.clone() ;

  // Update constructor map.
  if let Ok(mut map) = constructor_map.write() {
    for constructor in dtyp.news.keys() {
      let prev = map.insert( constructor.clone(), dtyp.clone() ) ;
      if let Some(prev) = prev {
        bail!(
          "constructor `{}` is already used by datatype `{}`",
          constructor, prev.name
        )
      }
    }
  }


  let prev = if let Ok(mut f) = factory.write() {
    f.insert(name, to_insert)
  } else {
    bail!("failed to access datatype factory")
  } ;

  if let Some(prev) = prev {
    bail!("attempting to redeclare datatype `{}`", prev.name)
  }

  Ok(dtyp)
}


/// Retrieves a datatype from its name.
///
/// Will fail if
///
/// - the datatype does not exist, or
/// - can't access the datatype map.
pub fn get(dtyp: & str) -> Res<DTyp> {
  let maybe_res = if let Ok(f) = factory.read() {
    f.get(dtyp).cloned()
  } else {
    bail!("failed to access datatype factory")
  } ;

  if let Some(res) = maybe_res {
    Ok(res)
  } else {
    bail!("unknown datatype `{}`", dtyp)
  }
}


/// All the datatypes.
pub fn get_all() -> impl ::std::ops::Deref< Target = BTreeMap<String, DTyp> > {
  factory.read().expect(
    "failed to access datatype factory"
  )
}


/// Writes all the datatypes.
pub fn write_all<W: Write>(w: & mut W, pref: & str) -> Res<()> {
  let decs = get_all() ;
  let mut known = HashSet::new() ;
  let dtyp_pref = & format!("{}  ", pref) ;

  for (name, dtyp) in decs.iter() {
    let is_new = known.insert(name) ;
    if ! is_new {
      continue
    }

    write!(w, "{}({} (", pref, keywords::cmd::dec_dtyp) ? ;
    for name in & dtyp.prms {
      write!(w, " {}", name) ?
    }
    writeln!(w, " ) (") ? ;

    dtyp.write(w, dtyp_pref) ? ;
    for dtyp in & dtyp.deps {
      let is_new = known.insert(dtyp) ;
      assert!(is_new) ;
      let dtyp = get(dtyp).expect("inconsistent datatype state") ;
      dtyp.write(w, dtyp_pref) ?
    }

    writeln!(w, "{}) )", pref) ?
  }

  Ok(())
}




/// Types a constructor application.
pub fn type_constructor(
  constructor: & str, args: & [ Term ]
) -> Res< Option<Typ> > {
  let dtyp = if let Ok(f) = factory.read() {
    if let Some(dtyp) = f.get(constructor) {
      dtyp.clone()
    } else {
      return Ok(None)
    }
  } else {
    bail!("failed to access datatype factory")
  } ;

  let params = {
    let dtyp_constructor = dtyp.news.get(constructor).expect(
      "inconsistent datatype constructor map"
    ) ;

    if args.len() != dtyp_constructor.len() {
      bail!(
        "constructor `{}` of type `{}` expects {} arguments, got {}",
        constructor, dtyp.name, dtyp_constructor.len(), args.len()
      )
    }

    let mut params = TPrmMap::with_capacity( dtyp.prms.len() ) ;
    for _ in 0 .. dtyp.prms.len() {
      params.push( typ::unk() )
    }

    for ( arg, (_, typ) ) in args.iter().zip(
      dtyp_constructor.iter()
    ) {
      typ.unify( & arg.typ(), & mut params ) ?
    }

    params
  } ;

  Ok( Some( typ::dtyp(dtyp.name.clone(), params) ) )
}






/// The actual datatype type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RDTyp {
  /// Name of the datatype.
  pub name: String,
  /// Other datatypes attached to this one.
  pub deps: Vec<String>,
  /// Type parameters.
  pub prms: TPrmMap<String>,
  /// Constructors.
  pub news: BTreeMap<String, CArgs>,
}
impl RDTyp {
  /// Constructor.
  pub fn new<S: Into<String>>(name: S, prms: TPrmMap<String>) -> Self {
    let name = name.into() ;
    RDTyp {
      name, deps: vec![], prms, news: BTreeMap::new(),
    }
  }

  /// Writes a single datatype.
  pub fn write<W: Write>(& self, w: & mut W, pref: & str) -> Res<()> {
    writeln!(w, "{}({}", pref, self.name) ? ;
    for (name, args) in & self.news {
      if args.is_empty() {
        write!(w, "{}  {}", pref, name) ?
      } else {
        write!(w, "{}  ({}", pref, name) ? ;
        for (name, typ) in args {
          write!(w, " ({} ", name) ? ;
          typ.write(w, & self.prms) ? ;
          write!(w, ")") ?
        }
        write!(w, ")") ?
      }
      writeln!(w) ?
    }
    writeln!(w, "{})", pref) ? ;
    Ok(())
  }

  /// Adds a datatype dependency.
  pub fn add_dep<S>(& mut self, dep: S)
  where S: Into<String> {
    self.deps.push( dep.into() )
  }

  /// Checks a datatype is legal.
  pub fn check(& self) -> Result<(), (::parse::Pos, String)> {
    for (constructor, cargs) in & self.news {
      for (selector, ptyp) in cargs {
        if let Err((pos, err)) = ptyp.check() {
          return Err((
            pos, format!(
              "{} on selector `{}` of constructor `{}`",
              err, selector, constructor
            )
          ))
        }
      }
    }
    Ok(())
  }

  /// Adds a constructor.
  pub fn add_constructor<S>(& mut self, name: S, args: CArgs) -> Res<()>
  where S: Into<String> {
    let name = name.into() ;
    for (other_name, other_args) in & self.news {
      if name == * other_name {
        bail!("attempting to redeclare constructor `{}`", name)
      }
      for (arg, _) in & args {
        for (other_arg, _) in other_args {
          if arg == other_arg {
            bail!("attempting to redeclare selector `{}`", arg)
          }
        }
      }
    }

    let _prev = self.news.insert(name, args) ;
    debug_assert_eq! { _prev, None }

    Ok(())
  }
}

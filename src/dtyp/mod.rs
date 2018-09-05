//! Datatypes.

use common::*;

wrap_usize! {
  #[doc = "Type parameter indices."]
  TPrmIdx
  #[doc = "Total map from type parameters to something."]
  map: TPrmMap with iter: TPrmMapIter
}

wrap_usize! {
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
    /// True if the type mentions the datatype provided.
    pub fn mentions_dtyp(&self, dtyp_name: &str) -> bool {
        let mut to_do = vec![self];
        let mut typ_to_do = vec![];

        loop {
            if to_do.is_empty() && typ_to_do.is_empty() {
                return false;
            }

            while let Some(current) = to_do.pop() {
                match current {
                    PartialTyp::Array(src, tgt) => {
                        to_do.push(&**src);
                        to_do.push(&**tgt)
                    }

                    PartialTyp::DTyp(name, _, _) if name == dtyp_name => return true,

                    PartialTyp::DTyp(_, _, prms) => for typ in prms {
                        to_do.push(typ)
                    },

                    PartialTyp::Typ(typ) => typ_to_do.push(typ),

                    PartialTyp::Param(_) => (),
                }
            }

            while let Some(current) = typ_to_do.pop() {
                use typ::RTyp;

                match current.get() {
                    RTyp::Unk | RTyp::Int | RTyp::Real | RTyp::Bool => (),
                    RTyp::Array { src, tgt } => {
                        typ_to_do.push(src);
                        typ_to_do.push(tgt)
                    }
                    RTyp::DTyp { dtyp, .. } if dtyp.name == dtyp_name => return true,
                    RTyp::DTyp { prms, .. } => for typ in prms {
                        typ_to_do.push(typ)
                    },
                }
            }
        }
    }

    /// Resolves a partial type against a type.
    pub fn unify(&self, typ: &Typ, map: &mut TPrmMap<Typ>) -> Res<()> {
        let mut stack = vec![(self, typ)];

        while let Some((ptyp, typ)) = stack.pop() {
            use typ::RTyp;

            match (ptyp, typ.get()) {
                (PartialTyp::Array(p_src, p_tgt), RTyp::Array { src, tgt }) => {
                    stack.push((p_src, src));
                    stack.push((p_tgt, tgt))
                }

                (PartialTyp::Typ(p_typ), _) => if !p_typ.is_compatible(typ) {
                    bail!("cannot unify type {} and {}", ptyp, typ)
                },

                (PartialTyp::Param(idx), _) => if let Some(merged) = typ.merge(&map[*idx]) {
                    map[*idx] = merged
                } else {
                    bail!("cannot unify type {} and {}", ptyp, typ)
                },

                (PartialTyp::DTyp(name, _, p_prms), RTyp::DTyp { dtyp, prms })
                    if name == &dtyp.name && p_prms.len() == prms.len() =>
                {
                    for (p_typ, typ) in p_prms.iter().zip(prms.iter()) {
                        stack.push((p_typ, typ))
                    }
                }

                _ => bail!("cannot unify {} with ({})", ptyp, typ),
            }
        }

        Ok(())
    }

    fn write<W: Write>(&self, w: &mut W, prms: &TPrmMap<String>) -> ::std::io::Result<()> {
        let mut stack = vec![("", self, "")];

        while let Some((sep, typ, close)) = stack.pop() {
            write!(w, "{}", sep)?;
            match typ {
                PartialTyp::Array(src, tgt) => {
                    stack.push((" ", &**tgt, ")"));
                    stack.push((" ", &**src, ""))
                }
                PartialTyp::DTyp(name, _, prms) => {
                    if !prms.is_empty() {
                        write!(w, "(")?
                    }
                    write!(w, "{}", name)?;
                    let mut first = true;
                    for sub in prms.iter().rev() {
                        let close = if first {
                            first = false;
                            ")"
                        } else {
                            ""
                        };
                        stack.push((" ", sub, close))
                    }
                }
                PartialTyp::Typ(typ) => write!(w, "{}", typ)?,
                PartialTyp::Param(idx) => write!(w, "{}", prms[*idx])?,
            }
            write!(w, "{}", close)?
        }

        Ok(())
    }

    /// Checks a partial type is legal.
    pub fn check(&self) -> Result<(), (::parse::Pos, String)> {
        let mut stack = vec![self];

        while let Some(ptyp) = stack.pop() {
            if let PartialTyp::DTyp(name, pos, args) = ptyp {
                if get(name).is_err() {
                    return Err((*pos, format!("unknown sort `{}`", name)));
                }
                for arg in args {
                    stack.push(arg)
                }
            }
        }

        Ok(())
    }

    /// Turns a partial type into a concrete type.
    pub fn to_type(&self, prms: &TPrmMap<Typ>) -> Result<Typ, (::parse::Pos, String)> {
        enum Frame<'a> {
            ArrayLft(&'a PartialTyp),
            ArrayRgt(Typ),
            DTyp(DTyp, TPrmMap<Typ>, ::std::slice::Iter<'a, PartialTyp>),
        }

        let mut curr = self;
        let mut stack = vec![];

        'go_down: loop {
            let mut typ = match curr {
                PartialTyp::Array(src, tgt) => {
                    curr = &**src;
                    stack.push(Frame::ArrayLft(&**tgt));

                    continue 'go_down;
                }

                PartialTyp::DTyp(name, pos, prms) => {
                    let mut nu_prms = TPrmMap::with_capacity(prms.len());
                    let mut prms = prms.iter();

                    let dtyp = if let Ok(dtyp) = get(name) {
                        dtyp
                    } else {
                        return Err((*pos, "unknown datatype".into()));
                    };

                    if let Some(partial) = prms.next() {
                        curr = partial;
                        stack.push(Frame::DTyp(dtyp, nu_prms, prms));

                        continue 'go_down;
                    } else {
                        typ::dtyp(dtyp, nu_prms)
                    }
                }

                PartialTyp::Typ(typ) => typ.clone(),

                PartialTyp::Param(idx) => prms[*idx].clone(),
            };

            'go_up: loop {
                match stack.pop() {
                    None => return Ok(typ),

                    Some(Frame::ArrayLft(tgt)) => {
                        curr = tgt;
                        stack.push(Frame::ArrayRgt(typ));
                        continue 'go_down;
                    }

                    Some(Frame::ArrayRgt(src)) => {
                        typ = typ::array(src, typ);
                        continue 'go_up;
                    }

                    Some(Frame::DTyp(dtyp, mut prms, mut to_do)) => {
                        prms.push(typ);
                        if let Some(typ_to_do) = to_do.next() {
                            stack.push(Frame::DTyp(dtyp, prms, to_do));
                            curr = typ_to_do;
                            continue 'go_down;
                        } else {
                            typ = typ::dtyp(dtyp, prms);
                            continue 'go_up;
                        }
                    }
                }
            }
        }
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

        PartialTyp::Param(idx) => write!(fmt, "'{}{}", idx, post) ?,

        PartialTyp::DTyp(dtyp, _, typs) => {
          if ! typs.is_empty() {
            write!(fmt, "(") ?
          }
          write!(fmt, "{} ", dtyp) ? ;
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
pub type DTyp = Arc<RDTyp>;

/// Constructor arguments.
pub type CArgs = Vec<(String, PartialTyp)>;

/// Type of the datatype factory.
type Factory = RwLock<BTreeMap<String, DTyp>>;
lazy_static! {
  /// Datatype factory.
  static ref factory: Factory = RwLock::new(
    BTreeMap::new()
  ) ;

  /// Set of reserved datatypes.
  static ref reserved_dtyps: BTreeSet<& 'static str> = {
    let mut set = BTreeSet::new() ;
    set.insert("List") ;
    set
  } ;

  /// Map from constructors to datatypes.
  static ref constructor_map: Factory = RwLock::new(
    BTreeMap::new()
  ) ;

  /// Set of selectors.
  static ref selector_set: RwLock<BTreeSet<String>> = RwLock::new(
    BTreeSet::new()
  ) ;
}

/// True if there is at least one datatype declared.
pub fn one_or_more() -> Res<bool> {
    if let Ok(f) = factory.read() {
        Ok(f.len() > 0)
    } else {
        bail!("could not access dtyp factory")
    }
}

/// Checks whether a datatype is reserved.
pub fn check_reserved(name: &str) -> Res<()> {
    if reserved_dtyps.contains(name) {
        bail!(
            "attempting to redefine built-in datatype {}",
            conf.bad(name)
        )
    }
    Ok(())
}

/// Creates a datatype.
///
/// Will fail if either
///
/// - the datatype already exists
/// - one of the constructors of the datatype already exists
/// - can't access the datatype map
/// - the datatype has no constructor
/// - the datatype has no constructor that don't mention itself
pub fn mk(mut dtyp: RDTyp) -> Res<DTyp> {
    let name = dtyp.name.clone();

    if dtyp.news.is_empty() {
        bail!("illegal datatype: no constructor")
    }

    // Number of constructor that mention `dtyp`.
    let mut rec_count = 0;
    let mut default = None;

    for (constructor, args) in &dtyp.news {
        let mut recursive = false;
        for (_, ty) in args {
            let rec = ty.mentions_dtyp(&dtyp.name);
            if rec {
                recursive = true;
                break;
            }
        }

        if recursive {
            rec_count += 1;
        } else {
            let default = default.get_or_insert_with(|| (constructor.clone(), args.len()));
            if default.1 > args.len() {
                default.0 = constructor.clone();
                default.1 = args.len()
            }
        }
    }

    if rec_count == dtyp.news.len() {
        bail!(
            "all constructors for datatype `{}` are recursive",
            dtyp.name
        )
    }

    if let Some((default, _)) = default {
        dtyp.default = default
    } else {
        bail!(
            "could not find a default constructor for datatype `{}`",
            dtyp.name
        )
    }

    let dtyp = Arc::new(dtyp);

    // Update constructor map.
    if let Ok(mut map) = constructor_map.write() {
        for constructor in dtyp.news.keys() {
            let prev = map.insert(constructor.clone(), dtyp.clone());
            if let Some(prev) = prev {
                bail!(
                    "constructor `{}` is already used by datatype `{}`",
                    constructor,
                    prev.name
                )
            }
        }
    } else {
        bail!("failed to retrieve datatype constructor map")
    }

    // Update selector set.
    if let Ok(mut set) = selector_set.write() {
        for selectors in dtyp.news.values() {
            for (selector, _) in selectors {
                set.insert(selector.clone());
            }
        }
    }

    let prev = if let Ok(mut f) = factory.write() {
        f.insert(name, dtyp.clone())
    } else {
        bail!("failed to access datatype factory")
    };

    if let Some(prev) = prev {
        bail!("attempting to redeclare datatype `{}`", prev.name)
    }

    Ok(dtyp)
}

/// Retrieves the datatype corresponding to a constructor.
pub fn of_constructor(constructor: &str) -> Option<DTyp> {
    constructor_map
        .read()
        .expect("failed to access constructor to datatype map")
        .get(constructor)
        .cloned()
}

/// True if the identifier is known to be a selector.
pub fn is_selector(selector: &str) -> bool {
    selector_set
        .read()
        .expect("failed to access selector set")
        .contains(selector)
}

/// Lists (some of) the constructors of a datatype as an error.
pub fn constructors_as_error(dtyp: &str) -> Error {
    let dtyp = match get(dtyp) {
        Ok(res) => res,
        Err(e) => return e,
    };
    let mut s = String::new();
    for (count, (constructor, args)) in dtyp.news.iter().enumerate() {
        if count >= 3 {
            s.push_str(&format!("and {} others...", dtyp.news.len() - 3))
        } else {
            if count > 0 {
                s.push_str("\n")
            }
            s.push_str(constructor);
            if !args.is_empty() {
                for (selector, typ) in args {
                    s.push_str(&format!(" ({} {})", selector, typ))
                }
            }
        }
    }
    s.into()
}

/// Retrieves a datatype from its name.
///
/// Will fail if
///
/// - the datatype does not exist, or
/// - can't access the datatype map.
pub fn get(dtyp: &str) -> Res<DTyp> {
    let maybe_res = if let Ok(f) = factory.read() {
        f.get(dtyp).cloned()
    } else {
        bail!("failed to access datatype factory")
    };

    if let Some(res) = maybe_res {
        Ok(res)
    } else if dtyp == "List" {
        mk(RDTyp::list())
    } else {
        bail!("unknown datatype `{}`", dtyp)
    }
}

/// All the datatypes.
pub fn get_all() -> impl ::std::ops::Deref<Target = BTreeMap<String, DTyp>> {
    factory.read().expect("failed to access datatype factory")
}

/// Writes the map from constructors to datatypes.
pub fn write_constructor_map<W: Write>(w: &mut W, pref: &str) -> ::std::io::Result<()> {
    for (constructor, dtyp) in constructor_map
        .read()
        .expect("unable to retrieve dtyp constructor map")
        .iter()
    {
        writeln!(w, "{}{:>10} -> {:>10}", pref, constructor, dtyp.name)?
    }
    Ok(())
}

/// Writes all the datatypes.
pub fn write_all<W: Write>(w: &mut W, pref: &str) -> ::std::io::Result<()> {
    let decs = get_all();

    if decs.is_empty() {
        return Ok(());
    }

    let mut known = HashSet::new();
    let dtyp_pref = &format!("{}  ", pref);

    for (name, dtyp) in decs.iter() {
        if reserved_dtyps.contains(name.as_str()) {
            continue;
        }
        let is_new = known.insert(name);
        if !is_new {
            continue;
        }

        let mut all = vec![dtyp.clone()];

        for dtyp in &dtyp.deps {
            let is_new = known.insert(dtyp);
            assert! { is_new }

            if let Ok(dtyp) = get(dtyp) {
                all.push(dtyp)
            } else {
                panic!("inconsistent datatype factory/maps state")
            }
        }

        writeln!(w, "{}({} (", pref, keywords::cmd::dec_dtyps)?;
        write!(w, "{} ", pref)?;

        for dtyp in all.clone() {
            write!(w, " ({} {})", dtyp.name, dtyp.prms.len())?
        }

        writeln!(w, "\n{}) (", pref)?;

        for dtyp in all {
            dtyp.write_dec(w, dtyp_pref)?
        }

        for dtyp in &dtyp.deps {
            let is_new = known.insert(dtyp);
            assert!(is_new)
        }

        writeln!(w, "{}) )", pref)?
    }

    writeln!(w)?;

    Ok(())
}

/// Types a constructor application.
pub fn type_constructor(constructor: &str, args: &[Term]) -> Res<Option<Typ>> {
    let dtyp = if let Some(dtyp) = of_constructor(constructor) {
        dtyp
    } else {
        return Ok(None);
    };

    let params = {
        let dtyp_constructor = dtyp
            .news
            .get(constructor)
            .expect("inconsistent datatype constructor map");

        if args.len() != dtyp_constructor.len() {
            bail!(
                "constructor `{}` of type `{}` expects {} arguments, got {}",
                constructor,
                dtyp.name,
                dtyp_constructor.len(),
                args.len()
            )
        }

        let mut params = TPrmMap::with_capacity(dtyp.prms.len());
        for _ in 0..dtyp.prms.len() {
            params.push(typ::unk())
        }

        for (arg, (_, typ)) in args.iter().zip(dtyp_constructor.iter()) {
            typ.unify(&arg.typ(), &mut params)?
        }

        params
    };

    Ok(Some(typ::dtyp(dtyp, params)))
}

/// Types a datatype selector application.
pub fn type_selector(
    selector: &str,
    slc_pos: ::parse::Pos,
    term: &Term,
) -> Result<Typ, (::parse::Pos, String)> {
    if let Some((dtyp, prms)) = term.typ().dtyp_inspect() {
        for args in dtyp.news.values() {
            for (slc, partial_typ) in args {
                if slc == selector {
                    return partial_typ.to_type(prms);
                }
            }
        }
    }

    Err((
        slc_pos,
        format!(
            "cannot apply selector `{}` to term of type {}",
            conf.bad(selector),
            term.typ()
        ),
    ))
}

/// Types a datatype tester application.
pub fn type_tester(
    tester: &str,
    tst_pos: ::parse::Pos,
    term: &Term,
) -> Result<(), (::parse::Pos, String)> {
    if let Some((dtyp, _)) = term.typ().dtyp_inspect() {
        if dtyp.news.contains_key(tester) {
            return Ok(());
        }
    }

    Err((
        tst_pos,
        format!(
            "cannot apply tester `{}` to term of type {}, no such constructor",
            conf.bad(tester),
            term.typ()
        ),
    ))
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
    /// Default type constructor.
    pub default: String,
}
impl RDTyp {
    /// Constructor.
    pub fn new<S: Into<String>>(name: S) -> Self {
        let name = name.into();
        RDTyp {
            name,
            deps: vec![],
            prms: TPrmMap::new(),
            news: BTreeMap::new(),
            default: "".into(),
        }
    }

    /// Generates the definition for the `List` datatype.
    fn list() -> Self {
        use parse::Pos;

        let mut news = BTreeMap::new();

        let mut prms = TPrmMap::new();
        let param = prms.next_index();
        prms.push("T".into());

        let prev = news.insert("nil".to_string(), vec![]);
        debug_assert! { prev.is_none() }

        let head = ("head".to_string(), PartialTyp::Param(param));
        let tail = (
            "tail".to_string(),
            PartialTyp::DTyp(
                "List".into(),
                Pos::default(),
                vec![PartialTyp::Param(param)].into(),
            ),
        );

        let prev = news.insert("insert".to_string(), vec![head, tail]);
        debug_assert! { prev.is_none() }

        let default = "nil".to_string();

        RDTyp {
            name: "List".into(),
            deps: vec![],
            prms,
            news,
            default,
        }
    }

    /// Pushes a type parameter.
    pub fn push_typ_param<S: Into<String>>(&mut self, name: S) -> TPrmIdx {
        let idx = self.prms.next_index();
        self.prms.push(name.into());
        idx
    }

    /// Writes the declaration for a datatype.
    pub fn write_dec<W: Write>(&self, w: &mut W, pref: &str) -> ::std::io::Result<()> {
        let close_par = if self.prms.is_empty() {
            writeln!(w, "{}( ; {}", pref, self.name)?;
            false
        } else {
            write!(w, "{}(par (", pref)?;
            for prm in &self.prms {
                write!(w, " {}", prm)?
            }
            writeln!(w, " ) (")?;
            true
        };

        for (name, args) in &self.news {
            write!(w, "{}  ({}", pref, name)?;
            for (name, typ) in args {
                write!(w, " ({} ", name)?;
                typ.write(w, &self.prms)?;
                write!(w, ")")?
            }
            writeln!(w, ")")?
        }

        writeln!(w, "{}){}", pref, if close_par { " )" } else { "" })
    }

    /// Writes a single datatype.
    pub fn write<W: Write>(&self, w: &mut W, pref: &str) -> ::std::io::Result<()> {
        writeln!(w, "{}({}", pref, self.name)?;
        for (name, args) in &self.news {
            if args.is_empty() {
                write!(w, "{}  {}", pref, name)?
            } else {
                write!(w, "{}  ({}", pref, name)?;
                for (name, typ) in args {
                    write!(w, " ({} ", name)?;
                    typ.write(w, &self.prms)?;
                    write!(w, ")")?
                }
                write!(w, ")")?
            }
            writeln!(w)?
        }
        writeln!(w, "{})", pref)?;
        Ok(())
    }

    /// Adds a datatype dependency.
    pub fn add_dep<S>(&mut self, dep: S)
    where
        S: Into<String>,
    {
        self.deps.push(dep.into())
    }

    /// Checks a datatype is legal.
    pub fn check(&self) -> Result<(), (::parse::Pos, String)> {
        for (constructor, cargs) in &self.news {
            for (selector, ptyp) in cargs {
                if let Err((pos, err)) = ptyp.check() {
                    return Err((
                        pos,
                        format!(
                            "{} on selector `{}` of constructor `{}`",
                            err, selector, constructor
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    /// Adds a constructor.
    pub fn add_constructor<S>(&mut self, name: S, args: CArgs) -> Res<()>
    where
        S: Into<String>,
    {
        let name = name.into();
        for (other_name, other_args) in &self.news {
            if name == *other_name {
                bail!("attempting to redeclare constructor `{}`", name)
            }
            for (arg, _) in &args {
                for (other_arg, _) in other_args {
                    if arg == other_arg {
                        bail!("attempting to redeclare selector `{}`", arg)
                    }
                }
            }
        }

        let _prev = self.news.insert(name, args);
        debug_assert_eq! { _prev, None }

        Ok(())
    }

    /// Returns a recursive constructor.
    ///
    /// Only returns something if
    ///
    /// - there are only two constructors
    /// - one of them is recursive
    pub fn rec_constructor(&self) -> Option<&str> {
        if self.news.len() == 2 {
            for (new, args) in &self.news {
                for (_, ptyp) in args {
                    if ptyp.mentions_dtyp(&self.name) {
                        return Some(new);
                    }
                }
            }
        }
        None
    }

    /// Returns the selectors of a constructor.
    pub fn selectors_of(&self, constructor: &str) -> Res<&CArgs> {
        if let Some(selectors) = self.news.get(constructor) {
            Ok(selectors)
        } else {
            bail!(
                "unknown constructor {} for dtyp {}, no selectors",
                conf.bad(constructor),
                conf.emph(&self.name)
            )
        }
    }
}
impl_fmt! {
  RDTyp(self, fmt) { write!(fmt, "{}", self.name) }
}

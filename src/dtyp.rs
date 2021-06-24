//! Datatypes.
//!
//! In test mode, the `List` datatype is automatically added, as well as a few functions (see the
//! [`fun`] module). This is so that dtyp-related doc/lib tests have something to work with.
//!
//! # Creating Mutually Recursive Datatypes
//!
//! Consider the following mutually recursive datatypes (stolen and fixed from the [z3 tutorial])
//!
//! ```scheme
//! (declare-datatypes ( (Tree 1) (TreeList 1) )
//!     ((par (T)
//!         (leaf)
//!         (node (value T) (children (TreeList T)))
//!     )(par (T)
//!         (nil)
//!         (cons (car (Tree T)) (cdr (TreeList T)))
//!     ))
//! )
//! ```
//!
//! The main steps are
//!
//! - create [`RDTyp`] structures encoding each datatype, which itself consists in
//!     - creating the list of type parameters if any
//!     - creating the list of constructors
//! - register them as depending on each other (important for SMT-level printing)
//! - finalize by hashconsing the definitions, thus obtaining [`DTyp`]s
//!
//! If you skip the non-mandatory-but-strongly-recommended last step, problems will arise during
//! term creation.
//!
//! ```rust
//! use hoice::{ dtyp, dtyp::{ RDTyp, PartialTyp }, parse::Pos };
//! let dummy_pos = Pos::default();
//! let (tree_name, tree_list_name) = ("DTypTestTree", "DTypTestTreeList");
//! let (mut tree, mut tree_list) = (RDTyp::new(tree_name), RDTyp::new(tree_list_name));
//!
//! // Working on `Tree`.
//! let t_param = tree.push_typ_param("T");
//! // `leaf` constructor takes no arguments
//! tree.add_constructor("leaf", vec![]).expect("while adding `leaf` constructor");
//! let node_params = vec![
//!     // `value` field of `node` has type `T`, registered as `t_param`
//!     ("value".to_string(), PartialTyp::Param(t_param)),
//!     // `children` field of `node` has type `(TreeList T)`
//!     (
//!         "children".to_string(),
//!         PartialTyp::DTyp(
//!             tree_list_name.into(),
//!             dummy_pos, // Used for error reporting when actually parsing user's input.
//!             // `TreeList` has a single argument, our type parameter `T`
//!             vec![ PartialTyp::Param(t_param) ].into(),
//!         )
//!     ),
//! ];
//! tree.add_constructor("node", node_params).expect("while adding node constructor");
//! // Finally, register dependency to `TreeList`.
//! tree.add_dep(tree_list_name);
//!
//! // Working on `TreeList`.
//! let t_param = tree_list.push_typ_param("T");
//! tree_list.add_constructor("nil", vec![]).expect("while adding `nil` constructor");
//! let cons_params = vec![
//!     (
//!         "car".to_string(),
//!         PartialTyp::DTyp(
//!             tree_name.into(),
//!             dummy_pos,
//!             vec![ PartialTyp::Param(t_param) ].into(),
//!         )
//!     ),
//!     (
//!         "cdr".to_string(),
//!         PartialTyp::DTyp(
//!             tree_list_name.into(),
//!             dummy_pos,
//!             vec![ PartialTyp::Param(t_param) ].into(),
//!         )
//!     ),
//! ];
//! tree_list.add_constructor("cons", cons_params).expect("while adding `cons` constructor");
//! tree_list.add_dep(tree_name);
//!
//! // Actually register.
//! let dtyps = dtyp::new_recs(
//!     vec![tree, tree_list], |_, err| err
//! ).expect("while registering `tree`");
//!
//! // Everything okay?
//! for dtyp in dtyps {
//!     dtyp.check().expect("while checking datatype")
//! }
//! ```
//!
//! [`fun`]: ../fun/index.html (fun module)
//! [z3 tutorial]: https://rise4fun.com/z3/tutorial
//! (z3 tutorial at Rise4Fun)
//! [`RDTyp`]: struct.RDTyp.html (RDTyp struct)
//! [`DTyp`]: type.DTyp.html (DTyp type)

use crate::{common::*, parse::Pos};

mylib::wrap_usize! {
    #[doc = "Type parameter indices."]
    TPrmIdx
    #[doc = "Total map from type parameters to something."]
    map: TPrmMap with iter: TPrmMapIter
}

mylib::wrap_usize! {
    #[doc = "Constructor argument indices."]
    CArgIdx
    #[doc = "Total map from constructor arguments to something."]
    map: CArgMap with iter: CArgMapIter
}

/// A concrete type, a polymorphic type, a datatype or a type parameter.
///
/// This is used by [`RDTyp`] to represent datatype (potentially) with type parameters.
///
/// [`RDTyp`]: struct.RDTyp.html (RDTyp struct)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PartialTyp {
    /// Array.
    Array(Box<PartialTyp>, Box<PartialTyp>),
    /// Datatype.
    DTyp(String, Pos, TPrmMap<PartialTyp>),
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::{dtyp::*, common::*, parse::Pos};
    /// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    /// let dummy_pos = Pos::default();
    /// let ptyp = PartialTyp::DTyp(
    ///     "MyADT".into(), dummy_pos, vec![
    ///         list.into(), PartialTyp::DTyp( "SubADT".into(), dummy_pos, vec![].into() )
    ///     ].into()
    /// );
    /// assert! { ptyp.mentions_dtyp("MyADT") }
    /// assert! { ptyp.mentions_dtyp("SubADT") }
    /// assert! { ptyp.mentions_dtyp("List") }
    /// assert! { !ptyp.mentions_dtyp("NotThere") }
    /// ```
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

                    PartialTyp::DTyp(_, _, prms) => {
                        for typ in prms {
                            to_do.push(typ)
                        }
                    }

                    PartialTyp::Typ(typ) => typ_to_do.push(typ),

                    PartialTyp::Param(_) => (),
                }
            }

            while let Some(current) = typ_to_do.pop() {
                use crate::typ::RTyp;

                match current.get() {
                    RTyp::Unk | RTyp::Int | RTyp::Real | RTyp::Bool => (),
                    RTyp::Array { src, tgt } => {
                        typ_to_do.push(src);
                        typ_to_do.push(tgt)
                    }
                    RTyp::DTyp { dtyp, .. } if dtyp.name == dtyp_name => return true,
                    RTyp::DTyp { prms, .. } => {
                        for typ in prms {
                            typ_to_do.push(typ)
                        }
                    }
                }
            }
        }
    }

    /// Resolves a partial type against a type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::{dtyp::*, common::*, parse::Pos};
    /// ::hoice::fun::test::create_length_fun();
    /// let dummy_pos = Pos::default();
    /// let param_0: TPrmIdx = 0.into();
    /// let ptyp = PartialTyp::DTyp(
    ///     "List".into(), dummy_pos, vec![ PartialTyp::Param(param_0) ].into()
    /// );
    /// let int_list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    ///
    /// let mut params: TPrmMap<Typ> = vec![ typ::unk() ].into();
    /// assert_eq! { &params[param_0], &typ::unk() }
    /// ptyp.unify(&int_list, &mut params).unwrap();
    /// assert_eq! { &params[param_0], &typ::int() }
    /// ```
    ///
    /// ```rust
    /// # use hoice::{dtyp::*, common::*, parse::Pos};
    /// ::hoice::fun::test::create_length_fun();
    /// let dummy_pos = Pos::default();
    /// let param_0: TPrmIdx = 0.into();
    /// let ptyp = PartialTyp::DTyp(
    ///     "List".into(), dummy_pos, vec![ PartialTyp::Param(param_0) ].into()
    /// );
    /// let int = typ::int();
    ///
    /// let mut params: TPrmMap<Typ> = vec![ typ::unk() ].into();
    /// assert_eq! { &params[param_0], &typ::unk() }
    /// let res = ptyp.unify(&int, &mut params);
    /// let err = res.unwrap_err();
    /// assert_eq! { &format!("{}", err), "cannot unify (List '0) with (Int)" }
    /// ```
    pub fn unify(&self, typ: &Typ, map: &mut TPrmMap<Typ>) -> Res<()> {
        let mut stack = vec![(self, typ)];

        while let Some((ptyp, typ)) = stack.pop() {
            use crate::typ::RTyp;

            match (ptyp, typ.get()) {
                (PartialTyp::Array(p_src, p_tgt), RTyp::Array { src, tgt }) => {
                    stack.push((p_src, src));
                    stack.push((p_tgt, tgt))
                }

                (PartialTyp::Typ(p_typ), _) => {
                    if !p_typ.is_compatible(typ) {
                        bail!("cannot unify type {} and {}", ptyp, typ)
                    }
                }

                (PartialTyp::Param(idx), _) => {
                    if let Some(merged) = typ.merge(&map[*idx]) {
                        map[*idx] = merged
                    } else {
                        bail!("cannot unify type {} and {}", ptyp, typ)
                    }
                }

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
    ///
    /// This checks that all datatypes mentioned in the partial type exist.
    ///
    /// ```rust
    /// # use hoice::{common::*, dtyp::*, parse::Pos};
    /// let _ = dtyp::get("List");
    /// let dummy_pos = Pos::default();
    /// let unknown = PartialTyp::DTyp("Unknown".into(), dummy_pos, vec![].into());
    /// let ptyp = PartialTyp::DTyp(
    ///     "List".into(), dummy_pos, vec![ unknown ].into()
    /// );
    /// let err = ptyp.check().unwrap_err().1;
    /// assert_eq! { &err, "unknown sort `Unknown`" }
    /// ```
    pub fn check(&self) -> Result<(), (Pos, String)> {
        let mut stack = vec![self];

        while let Some(ptyp) = stack.pop() {
            if let PartialTyp::DTyp(name, pos, args) = ptyp {
                if get(name).is_err() {
                    return Err((*pos, format!("unknown sort `{}`", conf.bad(name))));
                }
                for arg in args {
                    stack.push(arg)
                }
            }
        }

        Ok(())
    }

    /// Turns a partial type into a concrete type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::{dtyp::*, common::*, parse::Pos};
    /// let dummy_pos = Pos::default();
    /// let param_0: TPrmIdx = 0.into();
    /// let ptyp = PartialTyp::DTyp(
    ///     "List".into(), dummy_pos, vec![ PartialTyp::Param(param_0) ].into()
    /// );
    /// let int_list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    ///
    /// let mut params: TPrmMap<Typ> = vec![ typ::unk() ].into();
    /// assert_eq! { &params[param_0], &typ::unk() }
    /// ptyp.unify(&int_list, &mut params).unwrap();
    /// assert_eq! { &params[param_0], &typ::int() }
    /// let typ = ptyp.to_type(Some(&params)).unwrap();
    /// assert_eq! { int_list, typ }
    /// ```
    pub fn to_type(&self, prms: Option<&TPrmMap<Typ>>) -> Result<Typ, (Option<Pos>, String)> {
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
                    let nu_prms = TPrmMap::with_capacity(prms.len());
                    let mut prms = prms.iter();

                    let dtyp = if let Ok(dtyp) = get(name) {
                        dtyp
                    } else {
                        return Err((Some(*pos), "unknown datatype".into()));
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

                PartialTyp::Param(idx) => {
                    if let Some(prms) = prms {
                        prms[*idx].clone()
                    } else {
                        return Err(
                        (None, "trying to convert a partial sort in a total one without type parameters".into()));
                    }
                }
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

mylib::impl_fmt! {
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

/// A hashconsed datatype.
pub type DTyp = Arc<RDTyp>;

/// Constructor arguments.
///
/// Each string is the name of the selector, *i.e.* the "name" of the field. It is associated to a
/// partial type because, in general, it will mention type parameters of the datatype it belongs
/// to.
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

/// Creates the list datatype.
///
/// Only available in test mode.
pub fn create_list_dtyp() {
    let _ = new(RDTyp::list(), |_, blah| {
        format!("failed to create List datatype: {}", blah)
    });
    ()
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
pub fn check_reserved(_name: &str) -> Res<()> {
    // if reserved_dtyps.contains(name) {
    //     bail!(
    //         "attempting to redefine built-in datatype {}",
    //         conf.bad(name)
    //     )
    // }
    Ok(())
}

/// Creates a datatype.
///
/// Will fail if either
///
/// - the datatype already exists
/// - it mentions a datatype that doesn't exist
/// - one of the constructors of the datatype already exists
/// - can't access the datatype map
/// - the datatype has no constructor
/// - the datatype has no constructor that don't mention itself
///
/// Do *not* use this to construct mutually-recursive datatypes as it will fail. Use [`new_recs`]
/// instead.
///
/// For more see the [module-level documentation].
///
/// [module-level documentation]: index.html (dtyp module documentation)
/// [`new_recs`]: fn.new_recs.html (datatypes construction function)
pub fn new<E, F>(dtyp: RDTyp, err: F) -> Res<DTyp>
where
    E: Into<Error>,
    F: Fn(Pos, String) -> E,
{
    check_reserved(&dtyp.name)?;
    new_raw(dtyp).and_then(|dtyp| {
        if let Err((pos, blah)) = dtyp.check() {
            bail!(err(pos, blah))
        } else {
            Ok(dtyp)
        }
    })
}

/// Creates mutually recursive datatypes.
///
/// Will fail if either
///
/// - one of the datatypes already exists
/// - one of them mentions a datatype that doesn't exist
/// - one of the constructors already exists
/// - can't access the datatype map
/// - one of the datatypes has no constructor
/// - one of the datatypes has no constructor that don't mention itself
///
/// If an error occured, returns the index of the datatype for which it occured and the error
/// itself.
///
/// For more see the [module-level documentation].
///
/// [module-level documentation]: index.html (dtyp module documentation)
pub fn new_recs<E, F, RDTyps>(dtyp: RDTyps, err: F) -> Result<Vec<DTyp>, (usize, Error)>
where
    E: Into<Error>,
    F: Fn(Pos, String) -> E,
    RDTyps: IntoIterator<Item = RDTyp>,
{
    let mut res = vec![];
    for (index, dtyp) in dtyp.into_iter().enumerate() {
        check_reserved(&dtyp.name).map_err(|e| (index, e))?;
        res.push(new_raw(dtyp).map_err(|e| (index, e))?)
    }
    for (index, dtyp) in res.iter().enumerate() {
        if let Err((pos, blah)) = dtyp.check() {
            return Err((index, err(pos, blah).into()));
        }
    }
    Ok(res)
}

/// Creates a datatype.
///
/// Will fail if either
///
/// - the datatype already exists
/// - name is reserved
/// - one of the constructors of the datatype already exists
/// - can't access the datatype map
/// - the datatype has no constructor
/// - the datatype has no constructor that don't mention itself
fn new_raw(mut dtyp: RDTyp) -> Res<DTyp> {
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
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let list = dtyp::get("List").unwrap();
/// let dtyp = dtyp::of_constructor("nil");
/// assert_eq! { list, dtyp.unwrap() }
/// let dtyp = dtyp::of_constructor("insert");
/// assert_eq! { list, dtyp.unwrap() }
/// assert! { dtyp::of_constructor("unknown").is_none() }
/// ```
pub fn of_constructor(constructor: &str) -> Option<DTyp> {
    constructor_map
        .read()
        .expect("failed to access constructor to datatype map")
        .get(constructor)
        .cloned()
}

/// True if the identifier is known to be a selector.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let _ = dtyp::get("List");
/// assert! { dtyp::is_selector("tail") }
/// assert! { dtyp::is_selector("head") }
/// assert! { !dtyp::is_selector("unknown") }
/// ```
pub fn is_selector(selector: &str) -> bool {
    selector_set
        .read()
        .expect("failed to access selector set")
        .contains(selector)
}

/// Lists the constructors of a datatype as an error.
///
/// One line per constructor. If there are more than three constructor, lists only the first three
/// followed by "and `<n>` others" where `<n>` is the number of constructors left.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let _ = dtyp::get("List");
/// let err = dtyp::constructors_as_error("List");
/// assert_eq! {
///     &format!("{}", err),
///     "insert (head '0) (tail (List '0))\n\
///      nil"
/// }
/// ```
///
/// ```rust
/// # use hoice::common::*;
/// hoice::parse::fun_dtyp(
///     "(declare-datatypes ( (Enum 0) ) \
///         ( ( A B C D E F G H ) )
///     )"
/// );
/// let err = dtyp::constructors_as_error("Enum");
/// assert_eq! {
///     &format!("{}", err),
///     "A\nB\nC\nand 5 others"
/// }
/// ```
pub fn constructors_as_error(dtyp: &str) -> Error {
    let dtyp = match get(dtyp) {
        Ok(res) => res,
        Err(e) => return e,
    };
    let mut s = String::new();
    for (count, (constructor, args)) in dtyp.news.iter().enumerate() {
        if count > 0 {
            s.push_str("\n")
        }
        if count >= 3 {
            s.push_str(&format!("and {} others", dtyp.news.len() - 3));
            break;
        } else {
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
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// assert! { dtyp::get("Unknown").is_err() }
/// let lst = dtyp::get("List").unwrap();
/// assert_eq! { lst.name, "List" }
/// ```
pub fn get(dtyp: &str) -> Res<DTyp> {
    let maybe_res = if let Ok(f) = factory.read() {
        f.get(dtyp).cloned()
    } else {
        bail!("failed to access datatype factory")
    };

    if let Some(res) = maybe_res {
        Ok(res)
    } else if dtyp == "List" {
        new(RDTyp::list(), |_, blah| {
            format!("failed to create List datatype: {}", blah)
        })
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

/// Writes all the datatypes, SMT-LIB style.
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
///
/// Returns `None` if the constructor is unknown.
///
/// # Examples
///
/// ```rust
/// # use hoice::common::*;
/// let int_list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
/// let maybe_typ = dtyp::type_constructor(
///     "insert", & [ term::int(7), term::dtyp_new(int_list.clone(), "nil", vec![]) ]
/// ).unwrap();
/// assert_eq! { maybe_typ, Some(int_list) }
/// ```
///
/// ```rust
/// # use hoice::common::*;
/// let _ = dtyp::get("List");
/// let maybe_typ = dtyp::type_constructor("nil", &[]).unwrap();
/// assert_eq! { &format!("{}", maybe_typ.unwrap()), "(List _)" }
/// ```
///
/// ```rust
/// # use hoice::common::*;
/// let maybe_typ = dtyp::type_constructor("unknown", &[]).unwrap();
/// assert! { maybe_typ.is_none() }
/// ```
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
///
/// # Examples
///
/// ```rust
/// # use hoice::{common::*, parse::Pos};
/// let int_list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
/// let dummy_pos = Pos::default();
/// let typ = dtyp::type_selector(
///     "head", dummy_pos, & term::dtyp_new(int_list.clone(), "nil", vec![])
/// ).unwrap();
/// assert_eq! { typ, typ::int() }
/// let typ = dtyp::type_selector(
///     "tail", dummy_pos, & term::dtyp_new(int_list.clone(), "nil", vec![])
/// ).unwrap();
/// assert_eq! { typ, int_list }
/// ```
///
/// ```rust
/// # use hoice::{common::*, parse::Pos};
/// let dummy_pos = Pos::default();
/// let (_, blah) = dtyp::type_selector("unknown", dummy_pos, &term::int(7)).unwrap_err();
/// assert_eq! {
///     &blah, "`unknown` is not a legal selector for sort Int"
/// }
/// ```
pub fn type_selector(
    selector: &str,
    slc_pos: Pos,
    term: &Term,
) -> Result<Typ, (Option<Pos>, String)> {
    if let Some((dtyp, prms)) = term.typ().dtyp_inspect() {
        for args in dtyp.news.values() {
            for (slc, partial_typ) in args {
                if slc == selector {
                    return partial_typ.to_type(Some(prms));
                }
            }
        }
    }

    Err((
        Some(slc_pos),
        format!(
            "`{}` is not a legal selector for sort {}",
            conf.bad(selector),
            term.typ()
        ),
    ))
}

/// Types a datatype tester application.
///
/// Just like in term creation, the `tester` name is simply the name of the constructor (`"insert"`
/// for instance) as opposed to the name of the tester function (`"is-insert"` in this case).
///
/// Does not return a type, since a tester always has sort `Bool`.
///
/// # Examples
///
/// ```rust
/// # use hoice::{common::*, parse::Pos};
/// let int_list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
/// let dummy_pos = Pos::default();
/// dtyp::type_tester(
///     "nil", dummy_pos, & term::dtyp_new(int_list.clone(), "nil", vec![])
/// ).unwrap();
/// dtyp::type_tester(
///     "insert", dummy_pos, & term::dtyp_new(int_list.clone(), "nil", vec![])
/// ).unwrap();
/// ```
///
/// ```rust
/// # use hoice::{common::*, parse::Pos};
/// let dummy_pos = Pos::default();
/// let (_, blah) = dtyp::type_tester("unknown", dummy_pos, &term::int(7)).unwrap_err();
/// assert_eq! {
///     &blah, "`unknown` is not a legal tester for sort Int"
/// }
/// ```
pub fn type_tester(tester: &str, tst_pos: Pos, term: &Term) -> Result<(), (Pos, String)> {
    if let Some((dtyp, _)) = term.typ().dtyp_inspect() {
        if dtyp.news.contains_key(tester) {
            return Ok(());
        }
    }

    Err((
        tst_pos,
        format!(
            "`{}` is not a legal tester for sort {}",
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

    /// Writes the *body* of the declaration for a datatype.
    fn write_dec<W: Write>(&self, w: &mut W, pref: &str) -> ::std::io::Result<()> {
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

    /// String representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let list = dtyp::get("List").unwrap();
    /// assert_eq! {
    ///     (* list).to_string(), "\
    /// (List
    ///   (insert (head T) (tail (List T)))
    ///   nil
    /// )\n\
    ///     "
    /// }
    /// ```
    pub fn to_string(&self) -> String {
        let mut buff: Vec<u8> = vec![];
        self.write(&mut buff, "").unwrap();
        String::from_utf8_lossy(&buff).into()
    }

    /// Writes a single datatype.
    fn write<W: Write>(&self, w: &mut W, pref: &str) -> ::std::io::Result<()> {
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
    ///
    /// Dependencies indicates that some datatypes depend on each other. This useful mostly for
    /// printing at SMT-level.
    pub fn add_dep<S>(&mut self, dep: S)
    where
        S: Into<String>,
    {
        self.deps.push(dep.into())
    }

    /// Checks a datatype is legal.
    ///
    /// This checks that all partial types are legal, meaning that all datatypes referenced *must
    /// be registered*. So, checking a datatype before it is hashconsed and before its dependencies
    /// are hashconsed will usually fail.
    ///
    /// This check runs automatically when hashconsing datatype(s) with [`new`] and [`new_recs`].
    ///
    /// For more see the [module-level documentation].
    ///
    /// [module-level documentation]: index.html (dtyp module documentation)
    /// [`new`]: fn.new.html (datatype construction function)
    /// [`new_recs`]: fn.new_recs.html (datatypes construction function)
    pub fn check(&self) -> Result<(), (Pos, String)> {
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let list = dtyp::get("List").unwrap();
    /// assert_eq! { list.rec_constructor(), Some("insert") }
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let list = dtyp::get("List").unwrap();
    /// let slcs = list.selectors_of("nil").unwrap();
    /// assert! { slcs.is_empty() }
    /// let slcs = list.selectors_of("insert").unwrap();
    /// let mut slcs = slcs.iter();
    /// assert_eq! { &slcs.next().unwrap().0, "head" }
    /// assert_eq! { &slcs.next().unwrap().0, "tail" }
    /// assert! { slcs.next().is_none() }
    ///
    /// let err = list.selectors_of("node").unwrap_err();
    /// assert_eq! { &format!("{}", err), "unknown constructor `node` for dtyp List" }
    /// ```
    pub fn selectors_of(&self, constructor: &str) -> Res<&CArgs> {
        if let Some(selectors) = self.news.get(constructor) {
            Ok(selectors)
        } else {
            bail!(
                "unknown constructor `{}` for dtyp {}",
                conf.bad(constructor),
                conf.emph(&self.name)
            )
        }
    }
}
mylib::impl_fmt! {
    RDTyp(self, fmt) { write!(fmt, "{}", self.name) }
}

#[test]
fn dtyp_write_dec() {
    let list = get("List").unwrap();
    let mut buff: Vec<u8> = vec![];
    list.write_dec(&mut buff, "").unwrap();
    assert_eq!(
        &String::from_utf8_lossy(&buff),
        "\
(par ( T ) (
  (insert (head T) (tail (List T)))
  (nil)
) )\n\
        "
    )
}

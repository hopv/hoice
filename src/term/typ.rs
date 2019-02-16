//! Everything type-related.

use hashconsing::{HConsed, HashConsign};

use crate::{common::*, dtyp::TPrmMap};

hashconsing::consign! {
  /// Type factory.
  let factory = consign(conf.instance.term_capa) for RTyp ;
}

/// Generates the `Int` type.
pub fn int() -> Typ {
    factory.mk(RTyp::Int)
}
/// Generates the `Real` type.
pub fn real() -> Typ {
    factory.mk(RTyp::Real)
}
/// Generates the `Bool` type.
pub fn bool() -> Typ {
    factory.mk(RTyp::Bool)
}
/// Generates an Array type.
pub fn array(src: Typ, tgt: Typ) -> Typ {
    factory.mk(RTyp::Array { src, tgt })
}
/// Generates an unknown type.
pub fn unk() -> Typ {
    factory.mk(RTyp::Unk)
}
/// Generates a datatype.
pub fn dtyp(dtyp: dtyp::DTyp, prms: TPrmMap<Typ>) -> Typ {
    factory.mk(RTyp::DTyp { dtyp, prms })
}

/// A hash-consed type.
pub type Typ = HConsed<RTyp>;

/// Types.
///
/// # Examples
///
/// ```rust
/// use hoice::term::typ::* ;
/// assert_eq! {
///   format!("{}", array(int(), array(int(), int()))),
///   "(Array Int (Array Int Int))"
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RTyp {
    /// Unknown.
    Unk,
    /// Integers.
    Int,
    /// Reals.
    Real,
    /// Booleans.
    Bool,

    /// Arrays.
    Array {
        /// Type of indices.
        src: Typ,
        /// Type of values.
        tgt: Typ,
    },

    /// Datatype.
    DTyp {
        /// Original datatype.
        dtyp: DTyp,
        /// Type parameters.
        prms: TPrmMap<Typ>,
    },
}
impl RTyp {
    /// True if the type is bool.
    pub fn is_bool(&self) -> bool {
        *self == RTyp::Bool
    }
    /// True if the type is integer.
    pub fn is_int(&self) -> bool {
        *self == RTyp::Int
    }
    /// True if the type is real.
    pub fn is_real(&self) -> bool {
        *self == RTyp::Real
    }

    /// True if the type is arithmetic.
    pub fn is_arith(&self) -> bool {
        match *self {
            RTyp::Int | RTyp::Real => true,
            _ => false,
        }
    }

    /// True if the type is an array.
    pub fn is_array(&self) -> bool {
        match *self {
            RTyp::Array { .. } => true,
            _ => false,
        }
    }

    /// True if the type is a datatype.
    pub fn is_dtyp(&self) -> bool {
        match *self {
            RTyp::DTyp { .. } => true,
            _ => false,
        }
    }

    /// Inspects an array type.
    pub fn array_inspect(&self) -> Option<(&Typ, &Typ)> {
        if let RTyp::Array { src, tgt } = self {
            Some((src, tgt))
        } else {
            None
        }
    }

    /// True if the type is unknown.
    pub fn is_unk(&self) -> bool {
        RTyp::Unk == *self
    }

    /// True if the type mentions an unknown type.
    pub fn has_unk(&self) -> bool {
        let mut stack = vec![self];
        while let Some(curr) = stack.pop() {
            match curr {
                RTyp::Unk => return true,
                RTyp::Array { src, tgt } => {
                    stack.push(src.get());
                    stack.push(tgt.get())
                }
                RTyp::DTyp { prms, .. } => {
                    for typ in prms {
                        stack.push(typ.get())
                    }
                }
                RTyp::Int | RTyp::Real | RTyp::Bool => (),
            }
        }
        false
    }

    /// Returns the selectors of a constructor.
    ///
    /// Only legal on a datatype.
    pub fn selectors_of(&self, constructor: &str) -> Res<&dtyp::CArgs> {
        if let Some((dtyp, _)) = self.dtyp_inspect() {
            dtyp.selectors_of(constructor)
        } else {
            bail!("cannot retrieve dtyp selectors on non-dtyp sort {}", self)
        }
    }

    /// Inspects a datatype type.
    pub fn dtyp_inspect(&self) -> Option<(&DTyp, &TPrmMap<Typ>)> {
        if let RTyp::DTyp { dtyp, prms } = self {
            Some((dtyp, prms))
        } else {
            None
        }
    }

    /// Checks a type is legal.
    pub fn check(&self) -> Res<()> {
        match self {
            RTyp::DTyp { dtyp, prms } => {
                if dtyp.prms.len() != prms.len() {
                    bail!(
                        "datatype {} expects {} parameters, found {}",
                        conf.emph(&dtyp.name),
                        dtyp.prms.len(),
                        prms.len()
                    )
                }
            }
            RTyp::Unk | RTyp::Array { .. } | RTyp::Int | RTyp::Real | RTyp::Bool => (),
        }
        Ok(())
    }

    /// True if the types are compatible.
    ///
    /// Two types are compatible if they're the same except for unknown subtypes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::common::* ;
    ///
    /// let t_1 = typ::array( typ::int(), typ::unk() ) ;
    /// let t_2 = typ::array( typ::unk(), typ::real() ) ;
    /// assert! { t_1.is_compatible(& t_2) }
    /// ```
    pub fn is_compatible(&self, other: &Typ) -> bool {
        if self == other.get() {
            return true;
        }

        let mut stack = vec![(self, other.get())];
        while let Some((t_1, t_2)) = stack.pop() {
            match (t_1, t_2) {
                (RTyp::Int, RTyp::Int) => (),
                (RTyp::Real, RTyp::Real) => (),
                (RTyp::Bool, RTyp::Bool) => (),

                (RTyp::Unk, _) | (_, RTyp::Unk) => (),

                (
                    RTyp::Array {
                        src: src_1,
                        tgt: tgt_1,
                    },
                    RTyp::Array {
                        src: src_2,
                        tgt: tgt_2,
                    },
                ) => {
                    stack.push((src_1.get(), src_2.get()));
                    stack.push((tgt_1.get(), tgt_2.get()));
                }

                (
                    RTyp::DTyp {
                        dtyp: dtyp_1,
                        prms: prms_1,
                    },
                    RTyp::DTyp {
                        dtyp: dtyp_2,
                        prms: prms_2,
                    },
                ) => {
                    if dtyp_1.name == dtyp_2.name {
                        for (t_1, t_2) in prms_1.iter().zip(prms_2.iter()) {
                            stack.push((t_1, t_2))
                        }
                    } else {
                        return false;
                    }
                }

                (RTyp::Int, _)
                | (RTyp::Real, _)
                | (RTyp::Bool, _)
                | (RTyp::Array { .. }, _)
                | (RTyp::DTyp { .. }, _) => return false,
            }
        }

        true
    }

    /// Merges two types.
    ///
    /// Basically removes unknown types when possible. Returns `None` if the
    /// types are not compatible.
    pub fn merge(&self, typ: &Typ) -> Option<Typ> {
        use std::iter::Zip;
        use std::slice::Iter;

        enum Frame<'a, 'b> {
            ArrayLft(&'a Typ, &'a Typ),
            ArrayRgt(Typ),
            DTyp(
                dtyp::DTyp,
                dtyp::TPrmMap<Typ>,
                Zip<Iter<'b, Typ>, Iter<'b, Typ>>,
            ),
        }
        let slf = factory.mk(self.clone());

        let (mut lft, mut rgt) = (&slf, typ);
        let mut stack = vec![];

        'go_down: loop {
            let mut typ = match (lft.get(), rgt.get()) {
                (RTyp::Unk, _) => rgt.clone(),
                (_, RTyp::Unk) => lft.clone(),

                (
                    RTyp::Array {
                        src: src_1,
                        tgt: tgt_1,
                    },
                    RTyp::Array {
                        src: src_2,
                        tgt: tgt_2,
                    },
                ) => {
                    lft = src_1;
                    rgt = src_2;
                    stack.push(Frame::ArrayLft(tgt_1, tgt_2));

                    continue 'go_down;
                }

                (
                    RTyp::DTyp {
                        dtyp: dtyp_1,
                        prms: prms_1,
                    },
                    RTyp::DTyp {
                        dtyp: dtyp_2,
                        prms: prms_2,
                    },
                ) => {
                    if dtyp_1.name == dtyp_2.name && prms_1.len() == prms_2.len() {
                        debug_assert_eq! { prms_1.len(), prms_2.len() }

                        let mut prms = prms_1.iter().zip(prms_2.iter());

                        if let Some((l, r)) = prms.next() {
                            lft = l;
                            rgt = r;

                            stack.push(Frame::DTyp(
                                dtyp_1.clone(),
                                Vec::with_capacity(prms_1.len()).into(),
                                prms,
                            ));

                            continue 'go_down;
                        } else {
                            lft.clone()
                        }
                    } else {
                        return None;
                    }
                }

                (RTyp::Int, _)
                | (RTyp::Real, _)
                | (RTyp::Bool, _)
                | (RTyp::Array { .. }, _)
                | (RTyp::DTyp { .. }, _) => {
                    if lft == rgt {
                        lft.clone()
                    } else {
                        return None;
                    }
                }
            };

            'go_up: loop {
                match stack.pop() {
                    None => return Some(typ),

                    Some(Frame::ArrayLft(l, r)) => {
                        stack.push(Frame::ArrayRgt(typ));
                        lft = l;
                        rgt = r;
                        continue 'go_down;
                    }

                    Some(Frame::ArrayRgt(src)) => {
                        typ = array(src, typ);
                        continue 'go_up;
                    }

                    Some(Frame::DTyp(dt, mut params, mut zip)) => {
                        params.push(typ);
                        if let Some((l, r)) = zip.next() {
                            stack.push(Frame::DTyp(dt, params, zip));
                            lft = l;
                            rgt = r;
                            continue 'go_down;
                        } else {
                            typ = dtyp(dt, params);
                            continue 'go_up;
                        }
                    }
                }
            }
        }
    }

    /// Default value of a type.
    ///
    /// Fails if the type is unknown.
    pub fn default_val(&self) -> Val {
        let typ = factory.mk(self.clone());
        let mut current = typ;
        let mut stack = vec![];

        'go_down: loop {
            let mut val = match current.clone().get() {
                RTyp::Real => val::real(Rat::zero()),
                RTyp::Int => val::int(Int::zero()),
                RTyp::Bool => val::bool(true),
                RTyp::Array { ref src, ref tgt } => val::array(src.clone(), tgt.default_val()),
                RTyp::DTyp { dtyp, prms } => {
                    let mut args = vec![];

                    for (_, arg_typ) in dtyp
                        .news
                        .get(&dtyp.default)
                        .expect("inconsistent datatype factory/map state")
                    {
                        let arg_typ = arg_typ
                            .to_type(Some(prms))
                            .unwrap_or_else(|_| panic!("illegal type {}", current));
                        args.push(arg_typ)
                    }

                    let mut args = args.into_iter();

                    if let Some(next) = args.next() {
                        stack.push((current.clone(), dtyp.default.clone(), vec![], args));
                        current = next;
                        continue 'go_down;
                    } else {
                        val::dtyp_new(current.clone(), dtyp.default.clone(), vec![])
                    }
                }
                RTyp::Unk => panic!("unknown type has no default value"),
            };

            'go_up: loop {
                match stack.pop() {
                    None => return val,

                    Some((typ, default, mut args, mut prms)) => {
                        args.push(val);
                        if let Some(prm) = prms.next() {
                            stack.push((typ, default, args, prms));
                            current = prm;
                            continue 'go_down;
                        } else {
                            val = val::dtyp_new(typ.clone(), default, args);
                            continue 'go_up;
                        }
                    }
                }
            }
        }
    }

    /// Default term of a type.
    ///
    /// Fails if the type is unknown.
    pub fn default_term(&self) -> Term {
        match *self {
            RTyp::Real => term::real(Rat::zero()),
            RTyp::Int => term::int(Int::zero()),
            RTyp::Bool => term::bool(true),
            RTyp::Array { ref src, ref tgt } => term::cst_array(src.clone(), tgt.default_term()),
            RTyp::DTyp { .. } => unimplemented!(),
            RTyp::Unk => panic!("unknown type has no default term"),
        }
    }
}
impl ::rsmt2::print::Sort2Smt for RTyp {
    fn sort_to_smt2<Writer>(&self, w: &mut Writer) -> SmtRes<()>
    where
        Writer: Write,
    {
        write!(w, "{}", self)?;
        Ok(())
    }
}

mylib::impl_fmt! {
  RTyp(self, fmt) {
    let mut stack = vec![ (vec![self].into_iter(), "", "") ] ;

    'stack: while let Some( (mut typs, sep, end) ) = stack.pop() {
      while let Some(typ) = typs.next() {
        fmt.write_str(sep) ? ;
        match * typ {
          RTyp::Int => fmt.write_str("Int") ?,
          RTyp::Real => fmt.write_str("Real") ?,
          RTyp::Bool => fmt.write_str("Bool") ?,
          RTyp::Unk => fmt.write_str("_") ?,

          RTyp::DTyp { ref dtyp, ref prms } => {
            stack.push((typs, sep, end)) ;
            if prms.is_empty() {
              write!(fmt, "{}", dtyp.name) ? ;
            } else {
              write!(fmt, "({}", dtyp.name) ? ;
              let typs: Vec<_> = prms.iter().map(|typ| typ.get()).collect() ;
              stack.push( (typs.into_iter(), " ", ")") ) ;
            }
            continue 'stack
          },

          RTyp::Array { ref src, ref tgt } => {
            stack.push((typs, sep, end)) ;
            fmt.write_str("(Array") ? ;
            stack.push(
              (vec![& * src as & RTyp, & * tgt].into_iter(), " ", ")")
            ) ;
            continue 'stack
          },
        }
      }
      fmt.write_str(end) ?
    }

    Ok(())
  }
}

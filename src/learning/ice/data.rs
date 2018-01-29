//! Contains stuff related to ICE's projected data representation.

use common::* ;
use common::data::{ DataCore, Sample, HSample, HSamples } ;

use super::quals::{ Qual } ;


/// Projected data to classify.
#[derive(Clone)]
pub struct CData {
  /// Positive samples.
  pub pos: HSamples,
  /// Negative samples.
  pub neg: HSamples,
  /// Unclassified samples.
  pub unc: HSamples,
}
impl CData {

  /// Shannon entropy given the number of positive and negative samples.
  fn shannon_entropy(pos: f64, neg: f64) -> f64 {
    if pos == 0. && neg == 0. { return 1. }
    let den = pos + neg ;
    let (pos, neg) = (pos / den, neg / den) ;
    let (pos, neg) = (
      if pos <= 0. { 0. } else { - ( pos * pos.log2() ) },
      if neg <= 0. { 0. } else { - ( neg * neg.log2() ) }
    ) ;
    pos + neg
  }

  /// Shannon-entropy-based information gain of a qualifier (simple, ignores
  /// unclassified data).
  pub fn simple_gain(& self, qual: & mut Qual) -> Res< Option<f64> > {
    let my_entropy = Self::shannon_entropy(
      self.pos.len() as f64, self.neg.len() as f64
    ) ;
    let card = (self.pos.len() as f64) + (self.neg.len() as f64) ;
    let (
      mut q_pos, mut q_neg, mut q_unc, mut nq_pos, mut nq_neg, mut nq_unc
    ) = (0., 0., 0., 0., 0., 0.) ;
    for pos in & self.pos {
      match qual.bool_eval( pos.get() ) ? {
        Some(true) => q_pos += 1.,
        Some(false) => nq_pos += 1.,
        None => return Ok(None),
      }
    }
    for neg in & self.neg {
      match qual.bool_eval( neg.get() ) ? {
        Some(true) => q_neg += 1.,
        Some(false) => nq_neg += 1.,
        None => return Ok(None),
      }
    }
    for unc in & self.unc {
      match qual.bool_eval( unc.get() ) ? {
        Some(true) => q_unc += 1.,
        Some(false) => nq_unc += 1.,
        None => return Ok(None),
      }
    }
    if q_pos + q_neg + q_unc == 0. || nq_pos + nq_neg + nq_unc == 0. {
      Ok( None )
    } else {
      let (q_entropy, nq_entropy) = (
        Self::shannon_entropy( q_pos,  q_neg),
        Self::shannon_entropy(nq_pos, nq_neg)
      ) ;

      Ok(
        Some((
          my_entropy - (
            ( (q_pos + q_neg) *  q_entropy / card ) +
            ( (nq_pos + nq_neg) * nq_entropy / card )
          )
        ))
      )
    }
  }


  /// Modified entropy, uses [`EntropyBuilder`](struct.EntropyBuilder.html).
  ///
  /// Only takes into account unclassified data when `conf.ice.simple_gain`
  /// is false.
  pub fn entropy(& self, pred: PrdIdx, data: & DataCore) -> Res<f64> {
    let mut proba = EntropyBuilder::new() ;
    proba.set_pos_count( self.pos.len() ) ;
    proba.set_neg_count( self.neg.len() ) ;
    for unc in & self.unc {
      proba.add_unc(data, pred, unc) ?
    }
    proba.entropy()
  }

  /// Modified gain, uses `entropy`.
  ///
  /// Only takes into account unclassified data when `conf.ice.simple_gain`
  /// is false.
  pub fn gain<Trm: CanBEvaled>(
    & self, pred: PrdIdx, data: & DataCore, qual: & Trm
  ) -> Res< Option<f64> > {
    let my_entropy = self.entropy(pred, data) ? ;
    let my_card = (
      self.pos.len() + self.neg.len() + self.unc.len()
    ) as f64 ;
    let (mut q_ent, mut nq_ent) = (
      EntropyBuilder::new(), EntropyBuilder::new()
    ) ;
    let (
      mut q_pos, mut q_neg, mut q_unc, mut nq_pos, mut nq_neg, mut nq_unc
    ) = (0, 0, 0., 0, 0, 0.) ;
    for pos in & self.pos {
      match qual.evaluate( pos.get() ) ? {
        Some(true) => q_pos += 1,
        Some(false) => nq_pos += 1,
        None => return Ok(None),
      }
    }
    q_ent.set_pos_count(q_pos) ;
    nq_ent.set_pos_count(nq_pos) ;

    for neg in & self.neg {
      match qual.evaluate( neg.get() ) ? {
        Some(true) => q_neg += 1,
        Some(false) => nq_neg += 1,
        None => return Ok(None),
      }
    }
    q_ent.set_neg_count(q_neg) ;
    nq_ent.set_neg_count(nq_neg) ;

    for unc in & self.unc {
      match qual.evaluate( unc.get() ) ? {
        Some(true) => {
          q_unc += 1. ;
          q_ent.add_unc(data, pred, unc) ?
        },
        Some(false) => {
          nq_unc += 1. ;
          nq_ent.add_unc(data, pred, unc) ?
        },
        None => return Ok(None),
      }
    }
    
    let (q_pos, q_neg, nq_pos, nq_neg) = (
      q_pos as f64, q_neg as f64, nq_pos as f64, nq_neg as f64
    ) ;

    // Is this qualifier separating anything?
    if q_pos + q_neg + q_unc == 0.
    || nq_pos + nq_neg + nq_unc == 0. {
      return Ok(None)
    }

    let (q_entropy, nq_entropy) = (
      q_ent.entropy() ?, nq_ent.entropy() ?
    ) ;

    let gain = my_entropy - (
      (q_pos + q_neg + q_unc) * q_entropy / my_card +
      (nq_pos + nq_neg + nq_unc) * nq_entropy / my_card
    ) ;

    if gain.is_nan() {
      bail!(
        format!(
          "gain is NaN :(
  my_entropy: {}
  my_card: {}
  q  numerator: {} * {} = {}
  nq numerator: {} * {} = {}", my_entropy, my_card,
          (q_pos + q_neg + q_unc),
          q_entropy,
          (q_pos + q_neg + q_unc) * q_entropy,
          (nq_pos + nq_neg + nq_unc),
          nq_entropy,
          (nq_pos + nq_neg + nq_unc) * nq_entropy,
        )
      )
    }

    Ok( Some(gain) )
  }

  /// Splits the data given some qualifier. First is the data for which the
  /// qualifier is true.
  pub fn split(self, qual: & Term) -> (Self, Self) {
    let (mut q, mut nq) = (
      CData {
        pos: Vec::with_capacity( self.pos.len() ),
        neg: Vec::with_capacity( self.neg.len() ),
        unc: Vec::with_capacity( self.unc.len() ),
      },
      CData {
        pos: Vec::with_capacity( self.pos.len() ),
        neg: Vec::with_capacity( self.neg.len() ),
        unc: Vec::with_capacity( self.unc.len() ),
      }
    ) ;

    for pos in self.pos {
      if qual.bool_eval( pos.get() ).and_then(
        |res| res.ok_or_else(
          || ErrorKind::Msg( "model is not complete enough".into() ).into()
        )
      ).expect("error evaluating qualifier") {
        q.pos.push( pos )
      } else {
        nq.pos.push( pos )
      }
    }
    for neg in self.neg {
      if qual.bool_eval( neg.get() ).and_then(
        |res| res.ok_or_else(
          || ErrorKind::Msg( "model is not complete enough".into() ).into()
        )
      ).expect("error evaluating qualifier") {
        q.neg.push( neg )
      } else {
        nq.neg.push( neg )
      }
    }
    for unc in self.unc {
      if qual.bool_eval( unc.get() ).and_then(
        |res| res.ok_or_else(
          || ErrorKind::Msg( "model is not complete enough".into() ).into()
        )
      ).expect("error evaluating qualifier") {
        q.unc.push( unc )
      } else {
        nq.unc.push( unc )
      }
    }

    q.pos.shrink_to_fit() ;
    q.neg.shrink_to_fit() ;
    q.unc.shrink_to_fit() ;
    nq.pos.shrink_to_fit() ;
    nq.neg.shrink_to_fit() ;
    nq.unc.shrink_to_fit() ;

    (q, nq)
  }

  /// Iterator over some data.
  pub fn iter<'a>(& 'a self) -> CDataIter<'a> {
    CDataIter {
      pos: self.pos.iter(),
      neg: self.neg.iter(),
      unc: self.unc.iter(),
    }
  }
}

/// Iterator over CData.
pub struct CDataIter<'a> {
  pos: ::std::slice::Iter<'a, HSample>,
  neg: ::std::slice::Iter<'a, HSample>,
  unc: ::std::slice::Iter<'a, HSample>,
}
impl<'a> ::std::iter::Iterator for CDataIter<'a> {
  type Item = & 'a HSample ;
  fn next(& mut self) -> Option<Self::Item> {
    let next = self.pos.next() ;
    if next.is_some() { return next }
    let next = self.neg.next() ;
    if next.is_some() { return next }
    self.unc.next()
  }
}



/// Wrapper around an `f64` used to compute an approximation of the ratio
/// between legal positive classifications and negative ones, without actually
/// splitting the data.
///
/// See the paper for more details.
pub struct EntropyBuilder { num: f64, den: usize }
impl EntropyBuilder {
  /// Constructor.
  pub fn new() -> Self {
    EntropyBuilder { num: 0., den: 0 }
  }

  /// Sets the number of positive samples.
  pub fn set_pos_count(& mut self, pos: usize) {
    self.num += pos as f64 ;
    self.den += pos
  }
  /// Sets the number of negative samples.
  pub fn set_neg_count(& mut self, neg: usize) {
    self.den += neg
  }

  /// Adds the degree of an unclassified example.
  pub fn add_unc(
    & mut self, data: & DataCore, prd: PrdIdx, sample: & HSample
  ) -> Res<()> {
    let degree = Self::degree(data, prd, sample) ? ;
    self.den += 1 ;
    self.num += (1. / 2.) + (
      degree
    ).atan() / ::std::f64::consts::PI ;
    Ok(())
  }

  /// Probability stored in the builder.
  pub fn proba(& self) -> f64 {
    self.num / (self.den as f64)
  }

  /// Destroys the builder and returns the entropy.
  pub fn entropy(self) -> Res<f64> {
    let proba = self.proba() ;
    let (pos, neg) = (
      if proba == 0. { 0. } else {
        proba * proba.log2()
      },
      if proba == 1. { 0. } else {
        (1. - proba) * (1. - proba).log2()
      }
    ) ;
    let res = - pos - neg ;
    if res.is_nan() {
      bail!(
        format!(
          "entropy is NaN :(
  num  : {}
  den  : {}
  proba: {}
  pos  : {}
  neg  : {}", self.num, self.den, proba, pos, neg
        )
      )
    }
    Ok(res)
  }

  /// Degree of a sample, refer to the paper for details.
  pub fn degree(
    data: & DataCore, prd: PrdIdx, sample: & HSample
  ) -> Res<f64> {
    let (
      mut sum_imp_rhs,
      mut sum_imp_lhs,
      mut sum_neg,
    ) = (0., 0., 0.) ;

    if let Some(constraints) = data.map[prd].get(& sample) {
      for constraint in constraints {
        let constraint = & data.constraints[* constraint] ;
        match constraint.rhs {
          None => sum_neg = sum_neg + 1. / (constraint.lhs.len() as f64),
          Some( Sample { pred, ref args } )
          if pred == prd
          && args == sample => sum_imp_rhs = sum_imp_rhs + 1. / (
            1. + (constraint.lhs.len() as f64)
          ),
          _ => {
            debug_assert!(
              constraint.lhs.iter().fold(
                false,
                |b, & Sample { pred, ref args }|
                  b || ( pred == prd && args == sample )
              )
            ) ;
            sum_imp_lhs = sum_imp_lhs + 1. / (
              1. + (constraint.lhs.len() as f64)
            )
          },
        }
      }
    }

    let res = sum_imp_rhs - sum_imp_lhs - sum_neg ;

    Ok(res)
  }
}
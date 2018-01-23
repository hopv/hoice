//! Qualifier synthesis in the theory of integers.

use common::* ;
use common::data::HSample ;

use super::{ TermVals, TheoSynth } ;


/// Integer qualifier synthesizer.
pub struct IntSynth {
  /// Expressivity level.
  expressivity: usize,
}
impl IntSynth {
  /// Creates a new integer synthesizer.
  pub fn new() -> Self {
    IntSynth { expressivity: 0 }
  }
}
impl TheoSynth for IntSynth {
  fn is_done(& self) -> bool {
    self.expressivity > 0
  }
  fn restart(& mut self) {
    * self = Self::new()
  }
  fn synth<F>(
    & mut self, f: F, sample: & HSample, others: & mut TermVals
  ) -> Res<bool>
  where F: FnMut(Term) -> Res<bool> {
    match self.expressivity {
      0 => {
        self.expressivity += 1 ;
        simple_int_synth(sample, others, f)
      },
      _ => Ok(false),
    }
  }

  /// Only generates reals for now (using `to_real`).
  fn project(
    & self, sample: & HSample, typ: Typ, map: & mut TermVals
  ) -> Res<()> {
    match typ {
      Typ::Real => for (var, val) in sample.index_iter() {
        let val = Op::ToReal.eval( vec![ val.clone() ] ) ? ;
        if val.is_known() {
          let prev = map.insert(
            term::to_real( term::var(var) ), val
          ) ;
          debug_assert_eq!( prev, None )
        }
      },
      _ => (),
    }
    Ok(())
  }
}

macro_rules! apply {
  ($f:ident to $term:expr) => (
    if $f($term)? { return Ok(true) }
  ) ;
}


/// Lowest level of int synthesis.
///
/// All `v*` are variables. Synthesizes qualifiers of the form
///
/// - `v = n`, `v <= n`, `v >= n`,
/// - `v_1 = v_2`, `v_1 = - v_2`,
/// - `v_1 + v_2 >= n`, `v_1 + v_2 <= n`,
/// - `v_1 - v_2 >= n`, `v_1 - v_2 <= n`,
fn simple_int_synth<F>(
  sample: & HSample, others: & mut TermVals, mut f: F
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous_int: Vec<(Term, Int)> = Vec::with_capacity(
    sample.len()
  ) ;

  macro_rules! simple {
    ($term:tt = $val:expr) => ({

      let val_term = term::int( $val.clone() ) ;
      let term = term::app(
        Op::Ge, vec![ $term.clone(), val_term.clone() ]
      ) ;
      apply! { f to term }
      let term = term::app(
        Op::Le, vec![ $term.clone(), val_term.clone() ]
      ) ;
      apply! { f to term }
      let term = term::app(
        Op::Eql, vec![ $term.clone(), val_term ]
      ) ;
      apply! { f to term }

      for & (ref other_term, ref other_val) in & previous_int {
        if & $val == other_val {
          let term = term::eq(
            $term.clone(), other_term.clone()
          ) ;
          apply! { f to term }
        }
        if - (& $val) == * other_val {
          let term = term::eq(
            $term.clone(), term::sub( vec![ other_term.clone() ] )
          ) ;
          apply! { f to term }
        }

        let add = term::app(
          Op::Add, vec![ $term.clone(), other_term.clone() ]
        ) ;
        let add_val = term::int( & $val + other_val ) ;
        let term = term::app(
          Op::Ge, vec![ add.clone(), add_val.clone() ]
        ) ;
        apply! { f to term }
        let term = term::app(
          Op::Le, vec![ add, add_val ]
        ) ;
        apply! { f to term }

        let sub = term::app(
          Op::Sub, vec![ $term.clone(), other_term.clone() ]
        ) ;
        let sub_val = term::int( & $val - other_val ) ;
        let term = term::app(
          Op::Ge, vec![ sub.clone(), sub_val.clone() ]
        ) ;
        apply! { f to term }
        let term = term::app(
          Op::Le, vec![ sub, sub_val ]
        ) ;
        apply! { f to term }
      }

      previous_int.push( ($term, $val.clone()) )
    }) ;
  }

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    match * val {
      Val::I(ref val) => {
        let var = term::var(var_idx) ;
        simple! { var = ( val.clone() ) }
      },
      _ => (),
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    match val {
      Val::I(val) => {
        simple! { term = val }
      }
      val => bail!(
        "int synthesis expects projected integers, got {}", val
      )
    }
  }

  Ok(false)
}
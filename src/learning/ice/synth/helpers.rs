//! Macros factoring code for the synthesis process.


use common::* ;
use super::TermVals ;


/// Applies `$f` to `$term`.
///
/// Early returns if the application is an error. Early returns `Ok(true)` if
/// the application yields true.
macro_rules! apply {
  ($f:ident to $term:expr) => (
    if $f($term) ? { return Ok(true) }
  ) ;
}

/// Non-linear arithmetic synthesis for integer terms.
macro_rules! arith_synth_non_lin {
  ($previous:tt, $f:tt, $constructor:tt | $term:tt = $val:expr) => ({
    let zero: Int = 0.into() ;
    for & (ref other_term, ref other_val) in & $previous {
      let (lft, rgt, div, rem) = {
        if ! other_val.is_zero() && $val / other_val != zero {
          (
            $term.clone(), other_term.clone(),
            $val / other_val, $val % other_val
          )
        } else if ! $val.is_zero() {
          (
            other_term.clone(), $term.clone(),
            other_val / $val, other_val % $val
          )
        } else {
          continue
        }
      } ;
      let lhs = term::sub(
        vec![
          lft,
          term::mul( vec![ term::int(div), rgt ] ),
          term::int(rem)
        ]
      ) ;

      let term = term::ge( lhs.clone(), term::int(0) ) ;
      apply! { $f to term }

      let term = term::le( lhs.clone(), term::int(0) ) ;
      apply! { $f to term }

      let term = term::eq( lhs, term::int(0) ) ;
      apply! { $f to term }
    }
    $previous.push(($term, $val))
  }) ;
}


/// Bitvecs.
pub struct Bitvec {
  value: u64,
}
impl Bitvec {
  /// Constructor.
  pub fn zero() -> Self {
    Bitvec { value: 0 }
  }

  /// Increases the value.
  pub fn inc(& mut self) {
    self.value += 1
  }

  /// Retrieves the (inverted) boolean at some index.
  pub fn index(& self, index: usize) -> bool {
    if index < 64 {
      self.value & (1 << index) == 0
    } else {
      panic!("requesting synthesis over more than 64 variables")
    }
  }
}




/// N-term arithmetic synthesis.
pub fn n_term_arith_synth<F>(
  sample: & VarVals, others: & mut TermVals,
  typ: & Typ, len: usize, mut f: F,
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut previous: Vec<(Term, Val)> = Vec::with_capacity(
    sample.len()
  ) ;

  // Iterate over the sample.
  for (var_idx, val) in sample.index_iter() {
    if val.typ() == * typ && val.is_known() {
      let var = term::var(var_idx, typ::int()) ;

      let done = ::learning::ice::synth::helpers::sum_diff_synth(
        & ( var.clone(), val.clone() ), & previous,
        len, |term| f(term)
      ) ? ;

      if done {
        return Ok(true)
      }

      previous.push((var, val.clone()))
    }
  }

  // Iterate over the cross-theory terms.
  for (term, val) in others.drain() {
    let done = sum_diff_synth(
      & ( term.clone(), val.clone() ), & previous,
      len, |term| f(term)
    ) ? ;

    if done {
      return Ok(true)
    }

    previous.push( (term.clone(), val.clone()) )
  }

  Ok(false)
}




/// Arith sum/diff synth.
pub fn sum_diff_synth<F>(
  term: & (Term, Val), others: & Vec<(Term, Val)>,
  len: usize, mut f: F,
) -> Res<bool>
where F: FnMut(Term) -> Res<bool> {
  let mut stack = vec![ ( term, others.iter() ) ] ;

  loop {

    while stack.len() < len {
      if let Some((pair, others)) = stack.last_mut().and_then(
        |(_, others)| others.next().map(
          |pair| ( pair, others.clone() )
        )
      ) {
        stack.push( (pair, others) )
      } else if let Some(_) = stack.pop() {
        ()
      } else {
        return Ok(false)
      }
    }

    let done = iter_sum_diff_synth(& stack, & mut f) ? ;

    if done {
      return Ok(true)
    }

    let _ = stack.pop() ;
    ()

  }
}


/// Arith sum/diff synth.
fn iter_sum_diff_synth<F, T>(
  terms: & Vec<(& (Term, Val), T)>, mut f: F
) -> Res<bool>
where F : FnMut(Term) -> Res<bool> {
  if terms.is_empty() {
    return Ok(false)
  }

  let mut bitvec = Bitvec::zero() ;
  let max = 2u64.pow( ( terms.len() - 1 ) as u32 ) ;

  for _ in 0 .. max {
    let (
      mut sum, mut val, mut cnt
    ): (Vec<Term>, Option<Val>, usize) = (
      Vec::with_capacity( terms.len() ), None, 0
    ) ;

    for ( (term, term_val), _ ) in terms {
      let pos = bitvec.index(cnt) ;

      val = if let Some(val) = val {
        if pos {
          Some( val.add(term_val) ? )
        } else {
          Some( val.sub(term_val) ? )
        }
      } else if pos {
        Some( term_val.clone() )
      } else {
        Some( term_val.minus() ? )
      } ;

      if pos {
        sum.push( term.clone() )
      } else {
        sum.push( term::u_minus(term.clone()) )
      }

      cnt += 1
    }

    let val = if let Some(val) = val.and_then(
      |val| val.to_term()
    ) {
      val
    } else {
      bail!("unexpected non-value in synthesis")
    } ;

    let sum = term::add(sum) ;

    let done = f(
      term::ge( sum.clone(), val.clone() )
    ) ? ;
    if done {
      return Ok(true)
    }

    let done = f(
      term::le( sum.clone(), val.clone() )
    ) ? ;
    if done {
      return Ok(true)
    }

    let done = f(
      term::eq(sum, val)
    ) ? ;
    if done {
      return Ok(true)
    }

    bitvec.inc()
  }
  Ok(false)
}


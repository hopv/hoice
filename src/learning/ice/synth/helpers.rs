//! Macros factoring code for the synthesis process.

use super::TermVals;
use crate::common::*;

/// Applies `$f` to `$term`.
///
/// Early returns if the application is an error. Early returns `Ok(true)` if
/// the application yields true.
macro_rules! apply {
    ($f:ident to $term:expr) => {
        if $f($term)? {
            return Ok(true);
        }
    };
}

/// Simple arithmetic synthesis.
///
/// All `t*` are terms. Synthesizes qualifiers of the form
///
/// - `t = n`, `t <= n`, `t >= n`,
/// - `t_1 = t_2`, `t_1 = - t_2`,
/// - `t_1 + t_2 >= n`, `t_1 + t_2 <= n`,
/// - `t_1 - t_2 >= n`, `t_1 - t_2 <= n`,
#[macro_export]
macro_rules! simple_arith_synth {
    ($previous:tt, $f:tt, $constructor:tt | $term:tt = $val:expr) => {{
        let val_term = term::$constructor($val.clone());
        let term = term::app(Op::Ge, vec![$term.clone(), val_term.clone()]);
        apply! { $f to term }
        let term = term::app(Op::Le, vec![$term.clone(), val_term.clone()]);
        apply! { $f to term }
        let term = term::app(Op::Eql, vec![$term.clone(), val_term]);
        apply! { $f to term }

        for &(ref other_term, ref other_val) in &$previous {
            if &$val == other_val {
                let term = term::eq($term.clone(), other_term.clone());
                apply! { $f to term }
            }
            if -(&$val) == *other_val {
                let term = term::eq($term.clone(), term::sub(vec![other_term.clone()]));
                apply! { $f to term }
            }

            let add = term::app(Op::Add, vec![$term.clone(), other_term.clone()]);
            let add_val = term::$constructor(&$val + other_val);
            let term = term::app(Op::Ge, vec![add.clone(), add_val.clone()]);
            apply! { $f to term }
            let term = term::app(Op::Le, vec![add, add_val]);
            apply! { $f to term }

            let sub = term::app(Op::Sub, vec![$term.clone(), other_term.clone()]);
            let sub_val = term::$constructor(&$val - other_val);
            let term = term::app(Op::Ge, vec![sub.clone(), sub_val.clone()]);
            apply! { $f to term }
            let term = term::app(Op::Le, vec![sub, sub_val]);
            apply! { $f to term }
        }

        $previous.insert(($term, $val.clone()));
    }};
}

/// Non-linear arithmetic synthesis for integer terms.
#[macro_export]
macro_rules! arith_synth_non_lin {
    ($previous:tt, $f:tt, $constructor:tt | $term:tt = $val:expr) => {{
        use num::Zero;
        if !$val.is_zero() {
            for &(ref other_term, ref other_val) in &$previous {
                if other_val.is_zero() {
                    continue;
                }
                let (lhs, rhs) = arith_synth_non_lin!(
                                              @lhs $constructor $term, $val, other_term, other_val
                                            );

                let term = term::ge(lhs.clone(), rhs.clone());
                apply! { $f to term }

                let term = term::le(lhs.clone(), rhs.clone());
                apply! { $f to term }

                let term = term::eq(lhs, rhs);
                apply! { $f to term }
            }
            $previous.insert(($term, $val));
        }
    }};

    // Assumes $other_val is not 0.
    (@lhs int $term:expr, $val:expr, $other_term:expr, $other_val:expr) => {{
        let (lft, rgt, div, rem) = (
            $term.clone(),
            $other_term.clone(),
            &$val / $other_val,
            &$val % $other_val,
        );

        (
            term::sub(vec![lft, term::cmul(div, rgt), term::int(rem)]),
            term::int(0),
        )
    }};

    // Assumes $other_val is not 0.
    (@lhs real $term:expr, $val:expr, $other_term:expr, $other_val:expr) => {
        (
            term::sub(vec![
                $term.clone(),
                term::cmul($val / $other_val, $other_term.clone()),
            ]),
            term::real(Rat::new(0.into(), 1.into())),
        )
    };
}

/// Arithmetic synthesis over three terms.
///
/// All `t*` are terms, `<op>` is `=`, `ge` or `le. Synthesizes qualifiers
/// of the form
///
/// - `+ t_1 + t_2 + t_3 <op> n`
/// - `+ t_1 + t_2 - t_3 <op> n`
/// - `+ t_1 - t_2 + t_3 <op> n`
/// - `+ t_1 - t_2 - t_3 <op> n`
/// - `- t_1 + t_2 + t_3 <op> n`
/// - `- t_1 + t_2 - t_3 <op> n`
/// - `- t_1 - t_2 + t_3 <op> n`
/// - `- t_1 - t_2 - t_3 <op> n`
#[macro_export]
macro_rules! arith_synth_three_terms {
    ($previous:tt, $f:tt, $constructor:tt | $term:tt = $val:expr) => {{
        {
            let mut previous = $previous.iter();

            while let Some(&(ref other_term, ref other_val)) = previous.next() {
                for &(ref another_term, ref another_val) in previous.clone() {
                    arith_synth_three_terms! { @internal
                      $f(
                        term::add(
                          vec![ $term.clone(), other_term.clone(), another_term.clone() ]
                        ),
                        term::$constructor( & $val + other_val + another_val )
                      )
                    }

                    arith_synth_three_terms! { @internal
                      $f(
                        term::add(
                          vec![
                            $term.clone(),
                            other_term.clone(),
                            term::sub( vec![ another_term.clone() ] ),
                          ]
                        ),
                        term::$constructor( & $val + other_val - another_val )
                      )
                    }

                    arith_synth_three_terms! { @internal
                      $f(
                        term::add(
                          vec![
                            $term.clone(),
                            term::sub( vec![ other_term.clone() ] ),
                            another_term.clone(),
                          ]
                        ),
                        term::$constructor( & $val - other_val + another_val )
                      )
                    }

                    arith_synth_three_terms! { @internal
                      $f(
                        term::sub(
                          vec![
                            $term.clone(), other_term.clone(), another_term.clone()
                          ]
                        ),
                        term::$constructor( & $val - other_val - another_val )
                      )
                    }

                    arith_synth_three_terms! { @internal
                      $f(
                        term::add(
                          vec![
                            term::sub( vec![ $term.clone() ] ),
                            other_term.clone(),
                            another_term.clone()
                          ]
                        ),
                        term::$constructor( (- & $val) + other_val + another_val )
                      )
                    }

                    arith_synth_three_terms! { @internal
                      $f(
                        term::sub(
                          vec![
                            other_term.clone(),
                            $term.clone(),
                            another_term.clone()
                          ]
                        ),
                        term::$constructor( (- & $val) + other_val - another_val )
                      )
                    }

                    arith_synth_three_terms! { @internal
                      $f(
                        term::sub(
                          vec![
                            another_term.clone(),
                            $term.clone(),
                            other_term.clone(),
                          ]
                        ),
                        term::$constructor( (- & $val) - other_val + another_val )
                      )
                    }

                    arith_synth_three_terms! { @internal
                      $f(
                        term::sub(
                          vec![
                            term::add(
                              vec![
                                $term.clone(),
                                other_term.clone(),
                                another_term.clone()
                              ]
                            )
                          ]
                        ),
                        term::$constructor( (- & $val) - other_val - another_val )
                      )
                    }
                }
            }
        }
        $previous.insert(($term, $val.clone()));
    }};

    (@internal $f:tt($lhs:expr, $rhs:expr)) => {{
        let term = term::app(Op::Ge, vec![$lhs.clone(), $rhs.clone()]);
        // println!() ;
        // println!("> {}", term) ;
        apply! { $f to term }
        let term = term::app(Op::Le, vec![$lhs.clone(), $rhs.clone()]);
        // println!() ;
        // println!("> {}", term) ;
        apply! { $f to term }
        let term = term::app(Op::Eql, vec![$lhs.clone(), $rhs.clone()]);
        // println!() ;
        // println!("> {}", term) ;
        apply! { $f to term }
    }};
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
    pub fn inc(&mut self) {
        self.value += 1
    }

    /// Retrieves the (inverted) boolean at some index.
    pub fn index(&self, index: usize) -> bool {
        if index < 64 {
            self.value & (1 << index) == 0
        } else {
            panic!("requesting synthesis over more than 64 variables")
        }
    }
}

/// N-term arithmetic synthesis.
pub fn n_term_arith_synth<F>(
    sample: &VarVals,
    others: &mut TermVals,
    typ: &Typ,
    len: usize,
    mut f: F,
) -> Res<bool>
where
    F: FnMut(Term) -> Res<bool>,
{
    let mut previous: Vec<(Term, Val)> = Vec::with_capacity(sample.len());

    // Iterate over the sample.
    for (var_idx, val) in sample.index_iter() {
        if val.typ() == *typ && val.is_known() {
            let var = term::var(var_idx, typ.clone());

            let done = sum_diff_synth(&(var.clone(), val.clone()), &previous, len, &mut f)?;

            if done {
                return Ok(true);
            }

            previous.push((var, val.clone()))
        }
    }

    // Iterate over the cross-theory terms.
    for (term, val) in others.drain() {
        let done = sum_diff_synth(&(term.clone(), val.clone()), &previous, len, &mut f)?;

        if done {
            return Ok(true);
        }

        previous.push((term.clone(), val.clone()))
    }

    Ok(false)
}

/// Arith sum/diff synth.
pub fn sum_diff_synth<F>(
    term: &(Term, Val),
    others: &[(Term, Val)],
    len: usize,
    mut f: F,
) -> Res<bool>
where
    F: FnMut(Term) -> Res<bool>,
{
    let mut stack = vec![(term, others.iter())];

    loop {
        while stack.len() < len {
            if let Some((pair, others)) = stack
                .last_mut()
                .and_then(|(_, others)| others.next().map(|pair| (pair, others.clone())))
            {
                stack.push((pair, others))
            } else if stack.pop().is_some() {
                ()
            } else {
                return Ok(false);
            }
        }

        let done = iter_sum_diff_synth(&stack, &mut f)?;

        if done {
            return Ok(true);
        }

        let _ = stack.pop();
        ()
    }
}

// #[test]
fn _sum_diff() {
    let term = &(term::var(40, typ::int()), val::int(0));
    // println!("{}", term.0.uid());

    let v_41 = (term::var(41, typ::int()), val::int(1));
    // println!("{}", v_41.0.uid());
    let v_42 = (term::var(42, typ::int()), val::int(2));
    // println!("{}", v_42.0.uid());
    let v_43 = (term::var(43, typ::int()), val::int(3));
    // println!("{}", v_43.0.uid());

    let others = &[v_41, v_42, v_43];

    let expected = vec![
        "(= (+ (- 3) v_40 v_41 v_42) 0)",
        "(>= (+ v_40 v_41 v_42) 3)",
        "(>= (+ (* (- 1) v_40) (* (- 1) v_41) (* (- 1) v_42)) (- 3))",
        "(= (+ (- 3) v_41 v_42 (* (- 1) v_40)) 0)",
        "(>= (+ v_41 v_42 (* (- 1) v_40)) 3)",
        "(>= (+ v_40 (* (- 1) v_41) (* (- 1) v_42)) (- 3))",
        "(= (+ (- 1) v_40 v_42 (* (- 1) v_41)) 0)",
        "(>= (+ v_40 v_42 (* (- 1) v_41)) 1)",
        "(>= (+ v_41 (* (- 1) v_40) (* (- 1) v_42)) (- 1))",
        "(= (+ (- 1) v_42 (* (- 1) v_40) (* (- 1) v_41)) 0)",
        "(>= (+ v_42 (* (- 1) v_40) (* (- 1) v_41)) 1)",
        "(>= (+ v_40 v_41 (* (- 1) v_42)) (- 1))",
        "(= (+ v_40 v_41 v_43 (- 4)) 0)",
        "(>= (+ v_40 v_41 v_43) 4)",
        "(>= (+ (* (- 1) v_40) (* (- 1) v_41) (* (- 1) v_43)) (- 4))",
        "(= (+ v_41 v_43 (* (- 1) v_40) (- 4)) 0)",
        "(>= (+ v_41 v_43 (* (- 1) v_40)) 4)",
        "(>= (+ v_40 (* (- 1) v_41) (* (- 1) v_43)) (- 4))",
        "(= (+ v_40 v_43 (* (- 1) v_41) (- 2)) 0)",
        "(>= (+ v_40 v_43 (* (- 1) v_41)) 2)",
        "(>= (+ v_41 (* (- 1) v_40) (* (- 1) v_43)) (- 2))",
        "(= (+ v_43 (* (- 1) v_40) (* (- 1) v_41) (- 2)) 0)",
        "(>= (+ v_43 (* (- 1) v_40) (* (- 1) v_41)) 2)",
        "(>= (+ v_40 v_41 (* (- 1) v_43)) (- 2))",
        "(= (+ v_40 v_42 v_43 (- 5)) 0)",
        "(>= (+ v_40 v_42 v_43) 5)",
        "(>= (+ (* (- 1) v_40) (* (- 1) v_42) (* (- 1) v_43)) (- 5))",
        "(= (+ v_42 v_43 (* (- 1) v_40) (- 5)) 0)",
        "(>= (+ v_42 v_43 (* (- 1) v_40)) 5)",
        "(>= (+ v_40 (* (- 1) v_42) (* (- 1) v_43)) (- 5))",
        "(= (+ v_40 v_43 (- 1) (* (- 1) v_42)) 0)",
        "(>= (+ v_40 v_43 (* (- 1) v_42)) 1)",
        "(>= (+ v_42 (* (- 1) v_40) (* (- 1) v_43)) (- 1))",
        "(= (+ v_43 (- 1) (* (- 1) v_40) (* (- 1) v_42)) 0)",
        "(>= (+ v_43 (* (- 1) v_40) (* (- 1) v_42)) 1)",
        "(>= (+ v_40 v_42 (* (- 1) v_43)) (- 1))",
    ];
    let mut cnt = 0;

    sum_diff_synth(term, others, 3, |term| {
        println!("{}", term);
        assert_eq! { & format!("{}", term), & expected[cnt] };
        cnt += 1;
        Ok(false)
    })
    .unwrap();

    assert!(false)
}

/// Arith sum/diff synth.
fn iter_sum_diff_synth<F, T>(terms: &[(&(Term, Val), T)], mut f: F) -> Res<bool>
where
    F: FnMut(Term) -> Res<bool>,
{
    if terms.is_empty() {
        return Ok(false);
    }

    let mut bitvec = Bitvec::zero();
    let max = 2u64.pow((terms.len() - 1) as u32);

    for _ in 0..max {
        let (mut sum, mut val, mut cnt): (Vec<Term>, Option<Val>, usize) =
            (Vec::with_capacity(terms.len()), None, 0);

        for ((term, term_val), _) in terms {
            let pos = bitvec.index(cnt);

            val = if let Some(val) = val {
                if pos {
                    Some(val.add(term_val)?)
                } else {
                    Some(val.sub(term_val)?)
                }
            } else if pos {
                Some(term_val.clone())
            } else {
                Some(term_val.minus()?)
            };

            if pos {
                sum.push(term.clone())
            } else {
                sum.push(term::u_minus(term.clone()))
            }

            cnt += 1
        }

        let val = if let Some(val) = val.and_then(|val| val.to_term()) {
            val
        } else {
            bail!("unexpected non-value in synthesis")
        };

        let sum = term::add(sum);

        let done = f(term::eq(sum.clone(), val.clone()))?;
        if done {
            return Ok(true);
        }

        let done = f(term::ge(sum.clone(), val.clone()))?;
        if done {
            return Ok(true);
        }

        let done = f(term::le(sum, val))?;
        if done {
            return Ok(true);
        }

        bitvec.inc()
    }
    Ok(false)
}

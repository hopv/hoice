//! Tests for the term structure.

use common::* ;
use term::Op ;

#[test]
fn cst_add() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let sum = term::app( Op::Add, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    int model => sum, 10
  )
}

#[test]
fn cst_sub_1() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let sub = term::app( Op::Sub, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    int model => sub, 4
  )
}

#[test]
fn cst_sub_2() {
  let c_1 = term::int(7) ;
  let sub = term::app( Op::Sub, vec![ c_1 ] ) ;
  let model = model!() ;
  assert_eval!(
    int model => sub, (-7)
  )
}

#[test]
fn cst_mul() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let mul = term::app( Op::Mul, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    int model => mul, 21
  )
}

#[test]
fn cst_div() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let div = term::app( Op::Div, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    int model => div, 2
  )
}

#[test]
fn cst_mod() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let m0d = term::app( Op::Mod, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    int model => m0d, 1
  )
}

#[test]
fn cst_gt_1() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let gt = term::app( Op::Gt, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => gt
  )
}

#[test]
fn cst_gt_2() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(7) ;
  let gt = term::app( Op::Gt, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => gt
  )
}

#[test]
fn cst_ge_1() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let ge = term::app( Op::Ge, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => ge
  )
}

#[test]
fn cst_ge_2() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(7) ;
  let ge = term::app( Op::Ge, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => ge
  )
}

#[test]
fn cst_le_1() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let le = term::app( Op::Le, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => le
  )
}

#[test]
fn cst_le_2() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(7) ;
  let le = term::app( Op::Le, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => le
  )
}

#[test]
fn cst_lt_1() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let lt = term::app( Op::Lt, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => lt
  )
}

#[test]
fn cst_lt_2() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(7) ;
  let lt = term::app( Op::Lt, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => lt
  )
}

#[test]
fn cst_eq_1() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(7) ;
  let eq = term::app( Op::Eql, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => eq
  )
}

#[test]
fn cst_eq_2() {
  let c_1 = term::int(7) ;
  let c_2 = term::int(3) ;
  let eq = term::app( Op::Eql, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => eq
  )
}

#[test]
fn cst_eq_3() {
  let c_1 = term::tru() ;
  let c_2 = term::tru() ;
  let eq = term::app( Op::Eql, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => eq
  )
}

#[test]
fn cst_eq_4() {
  let c_1 = term::fls() ;
  let c_2 = term::tru() ;
  let eq = term::app( Op::Eql, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => eq
  )
}

#[test]
fn cst_impl_1() {
  let c_1 = term::fls() ;
  let c_2 = term::fls() ;
  let imp = term::app( Op::Impl, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => imp
  )
}

#[test]
fn cst_impl_2() {
  let c_1 = term::tru() ;
  let c_2 = term::fls() ;
  let imp = term::app( Op::Impl, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => imp
  )
}

#[test]
fn cst_impl_3() {
  let c_1 = term::fls() ;
  let c_2 = term::tru() ;
  let imp = term::app( Op::Impl, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => imp
  )
}

#[test]
fn cst_impl_4() {
  let c_1 = term::tru() ;
  let c_2 = term::tru() ;
  let imp = term::app( Op::Impl, vec![ c_1, c_2 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => imp
  )
}

#[test]
fn cst_not_1() {
  let c_1 = term::fls() ;
  let not = term::app( Op::Not, vec![ c_1 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => not
  )
}

#[test]
fn cst_not_2() {
  let c_1 = term::tru() ;
  let not = term::app( Op::Not, vec![ c_1 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => not
  )
}

#[test]
fn cst_and_1() {
  let c_1 = term::tru() ;
  let c_2 = term::tru() ;
  let c_3 = term::tru() ;
  let c_4 = term::tru() ;
  let and = term::app( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => and
  )
}

#[test]
fn cst_and_2() {
  let c_1 = term::tru() ;
  let c_2 = term::tru() ;
  let c_3 = term::fls() ;
  let c_4 = term::tru() ;
  let and = term::app( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => and
  )
}

#[test]
fn cst_and_3() {
  let c_1 = term::fls() ;
  let c_2 = term::tru() ;
  let c_3 = term::tru() ;
  let c_4 = term::tru() ;
  let and = term::app( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => and
  )
}

#[test]
fn cst_and_4() {
  let c_1 = term::tru() ;
  let c_2 = term::fls() ;
  let c_3 = term::fls() ;
  let c_4 = term::tru() ;
  let and = term::app( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => and
  )
}

#[test]
fn cst_or_1() {
  let c_1 = term::tru() ;
  let c_2 = term::tru() ;
  let c_3 = term::tru() ;
  let c_4 = term::tru() ;
  let or = term::app( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => or
  )
}

#[test]
fn cst_or_2() {
  let c_1 = term::tru() ;
  let c_2 = term::tru() ;
  let c_3 = term::fls() ;
  let c_4 = term::tru() ;
  let or = term::app( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => or
  )
}

#[test]
fn cst_or_3() {
  let c_1 = term::fls() ;
  let c_2 = term::tru() ;
  let c_3 = term::tru() ;
  let c_4 = term::tru() ;
  let or = term::app( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => or
  )
}

#[test]
fn cst_or_4() {
  let c_1 = term::tru() ;
  let c_2 = term::fls() ;
  let c_3 = term::fls() ;
  let c_4 = term::tru() ;
  let or = term::app( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool model => or
  )
}

#[test]
fn cst_or_5() {
  let c_1 = term::fls() ;
  let c_2 = term::fls() ;
  let c_3 = term::fls() ;
  let c_4 = term::fls() ;
  let or = term::app( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
  let model = model!() ;
  assert_eval!(
    bool not model => or
  )
}

#[test]
fn models() {
  let v_1 = term::var(0) ;
  let v_2 = term::var(1) ;
  let v_3 = term::var(2) ;


  let model_1 = model!( true, 2, 3 ) ;
  let model_2 = model!( true, 7, 0 ) ;

  // (7 - v_2) + (v_2 * 2) + (- v_3)
  let lhs = term::app(
    Op::Add, vec![
      term::app( Op::Sub, vec![ term::int(7), v_2.clone() ] ),
      term::app( Op::Mul, vec![ v_2.clone(), term::int(2) ] ),
      term::app( Op::Sub, vec![ v_3.clone() ] ),
    ]
  ) ;
  assert_eval!(int model_1 => lhs, 6) ;
  assert_eval!(int model_2 => lhs, 14) ;

  // v_3 * 3
  let rhs = term::app(
    Op::Mul, vec![ v_3.clone(), term::int(3) ]
  ) ;
  assert_eval!(int model_1 => rhs, 9) ;
  assert_eval!(int model_2 => rhs, 0) ;

  // 7 + v_2 + (- v_3) > v_3 * 3
  let gt = term::app(
    Op::Gt, vec![ lhs.clone(), rhs.clone() ]
  ) ;
  assert_eval!(bool not model_1 => gt) ;
  assert_eval!(bool     model_2 => gt) ;

  // v_1 && (7 + v_2 + (- v_3) > v_3 * 3)
  let and = term::app(
    Op::And, vec![ v_1.clone(), gt.clone() ]
  ) ;
  assert_eval!(bool not model_1 => and) ;
  assert_eval!(bool     model_2 => and) ;

  ()
}

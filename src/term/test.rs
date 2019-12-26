//! Tests for the term structure.

use crate::{common::*, term::int, term::Op};

fn init() {
    let terms = [
        term::int(0),
        term::int(1),
        term::int(2),
        term::int(3),
        term::u_minus(term::int(0)),
        term::u_minus(term::int(1)),
        term::u_minus(term::int(2)),
        term::u_minus(term::int(3)),
        term::var(40, typ::int()),
        term::var(41, typ::int()),
        term::var(42, typ::int()),
        term::var(43, typ::int()),
        term::u_minus(term::var(40, typ::int())),
        term::u_minus(term::var(41, typ::int())),
        term::u_minus(term::var(42, typ::int())),
        term::u_minus(term::var(43, typ::int())),
    ];

    for _ in terms.into_iter() {
        assert!(true)
    }
}

#[test]
fn cst_add() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let sum = term::app(Op::Add, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        int model => sum, 10
    )
}

#[test]
fn cst_sub_1() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let sub = term::app(Op::Sub, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        int model => sub, 4
    )
}

#[test]
fn cst_sub_2() {
    init();
    let c_1 = int(7);
    let sub = term::app(Op::Sub, vec![c_1]);
    let model = model!();
    assert_eval!(
        int model => sub, (-7)
    )
}

#[test]
fn cst_mul() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let mul = term::app(Op::Mul, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        int model => mul, 21
    )
}

#[test]
fn cst_div() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let div = term::app(Op::IDiv, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        int model => div, 2
    )
}

#[test]
fn cst_mod() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let m0d = term::app(Op::Mod, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        int model => m0d, 1
    )
}

#[test]
fn cst_gt_1() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let gt = term::app(Op::Gt, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => gt
    )
}

#[test]
fn cst_gt_2() {
    init();
    let c_1 = int(7);
    let c_2 = int(7);
    let gt = term::app(Op::Gt, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool not model => gt
    )
}

#[test]
fn cst_ge_1() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let ge = term::app(Op::Ge, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => ge
    )
}

#[test]
fn cst_ge_2() {
    init();
    let c_1 = int(7);
    let c_2 = int(7);
    let ge = term::app(Op::Ge, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => ge
    )
}

#[test]
fn cst_le_1() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let le = term::app(Op::Le, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool not model => le
    )
}

#[test]
fn cst_le_2() {
    init();
    let c_1 = int(7);
    let c_2 = int(7);
    let le = term::app(Op::Le, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => le
    )
}

#[test]
fn cst_lt_1() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let lt = term::app(Op::Lt, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool not model => lt
    )
}

#[test]
fn cst_lt_2() {
    init();
    let c_1 = int(7);
    let c_2 = int(7);
    let lt = term::app(Op::Lt, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool not model => lt
    )
}

#[test]
fn cst_eq_1() {
    init();
    let c_1 = int(7);
    let c_2 = int(7);
    let eq = term::app(Op::Eql, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => eq
    )
}

#[test]
fn cst_eq_2() {
    init();
    let c_1 = int(7);
    let c_2 = int(3);
    let eq = term::app(Op::Eql, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool not model => eq
    )
}

#[test]
fn cst_eq_3() {
    init();
    let c_1 = term::tru();
    let c_2 = term::tru();
    let eq = term::app(Op::Eql, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => eq
    )
}

#[test]
fn cst_eq_4() {
    init();
    let c_1 = term::fls();
    let c_2 = term::tru();
    let eq = term::app(Op::Eql, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool not model => eq
    )
}

#[test]
fn cst_impl_1() {
    init();
    let c_1 = term::fls();
    let c_2 = term::fls();
    let imp = term::app(Op::Impl, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => imp
    )
}

#[test]
fn cst_impl_2() {
    init();
    let c_1 = term::tru();
    let c_2 = term::fls();
    let imp = term::app(Op::Impl, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool not model => imp
    )
}

#[test]
fn cst_impl_3() {
    init();
    let c_1 = term::fls();
    let c_2 = term::tru();
    let imp = term::app(Op::Impl, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => imp
    )
}

#[test]
fn cst_impl_4() {
    init();
    let c_1 = term::tru();
    let c_2 = term::tru();
    let imp = term::app(Op::Impl, vec![c_1, c_2]);
    let model = model!();
    assert_eval!(
        bool model => imp
    )
}

#[test]
fn cst_not_1() {
    init();
    let c_1 = term::fls();
    let not = term::app(Op::Not, vec![c_1]);
    let model = model!();
    assert_eval!(
        bool model => not
    )
}

#[test]
fn cst_not_2() {
    init();
    let c_1 = term::tru();
    let not = term::app(Op::Not, vec![c_1]);
    let model = model!();
    assert_eval!(
        bool not model => not
    )
}

#[test]
fn cst_and_1() {
    init();
    let c_1 = term::tru();
    let c_2 = term::tru();
    let c_3 = term::tru();
    let c_4 = term::tru();
    let and = term::app(Op::And, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool model => and
    )
}

#[test]
fn cst_and_2() {
    init();
    let c_1 = term::tru();
    let c_2 = term::tru();
    let c_3 = term::fls();
    let c_4 = term::tru();
    let and = term::app(Op::And, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool not model => and
    )
}

#[test]
fn cst_and_3() {
    init();
    let c_1 = term::fls();
    let c_2 = term::tru();
    let c_3 = term::tru();
    let c_4 = term::tru();
    let and = term::app(Op::And, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool not model => and
    )
}

#[test]
fn cst_and_4() {
    init();
    let c_1 = term::tru();
    let c_2 = term::fls();
    let c_3 = term::fls();
    let c_4 = term::tru();
    let and = term::app(Op::And, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool not model => and
    )
}

#[test]
fn cst_or_1() {
    init();
    let c_1 = term::tru();
    let c_2 = term::tru();
    let c_3 = term::tru();
    let c_4 = term::tru();
    let or = term::app(Op::Or, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool model => or
    )
}

#[test]
fn cst_or_2() {
    init();
    let c_1 = term::tru();
    let c_2 = term::tru();
    let c_3 = term::fls();
    let c_4 = term::tru();
    let or = term::app(Op::Or, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool model => or
    )
}

#[test]
fn cst_or_3() {
    init();
    let c_1 = term::fls();
    let c_2 = term::tru();
    let c_3 = term::tru();
    let c_4 = term::tru();
    let or = term::app(Op::Or, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool model => or
    )
}

#[test]
fn cst_or_4() {
    init();
    let c_1 = term::tru();
    let c_2 = term::fls();
    let c_3 = term::fls();
    let c_4 = term::tru();
    let or = term::app(Op::Or, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool model => or
    )
}

#[test]
fn cst_or_5() {
    init();
    let c_1 = term::fls();
    let c_2 = term::fls();
    let c_3 = term::fls();
    let c_4 = term::fls();
    let or = term::app(Op::Or, vec![c_1, c_2, c_3, c_4]);
    let model = model!();
    assert_eval!(
        bool not model => or
    )
}

#[test]
fn add_real_1() {
    init();
    let v_1 = term::var(0, typ::real());
    let add = term::add(vec![term::real_of(-2.0), v_1.clone()]);
    let model = model!(val::real(rat_of_float(1.0)));
    assert_eval!( real model => add, - 1.0 );
}

#[test]
fn ite_1() {
    init();
    let v_1 = term::var(0, typ::real());
    let ite = term::ite(
        term::eq(
            term::add(vec![term::real_of(-2.0), v_1.clone()]),
            term::real_of(0.0),
        ),
        term::real_of(1.0),
        term::add(vec![term::real_of(1.0), v_1.clone()]),
    );
    let model = model!(val::real(rat_of_float(1.0)));
    println!("ite_1");
    println!("model:");
    model.print();
    assert_eval!( real model => ite, 2.0 );
}

// The lazy evaluation tests rely on the order in which the terms are created.
// This is not the case outside of these tests obviously. But here the goal is
// to have the last term being illegal, usually a variable that's not defined
// in the model. That way, if lazy evaluation does not do the right thing the
// test crashes.
//
// Unfortunately, test run in parallel and this can end up screwing up the
// order of the terms. To avoid this, the illegal variable should use a
// different index each time, ideally a high one to avoid clashes with other
// tests.

#[test]
fn lazy_1() {
    init();
    let v_0 = term::real_var(0);
    let t_1 = term::ge(v_0, term::real(rat_of_float(7.0)));
    let v_1 = term::real_var(1000);
    let t_2 = term::ge(v_1, term::real(rat_of_float(0.0)));

    let conj = term::and(vec![t_1, t_2]);

    let model = model!(val::real(rat_of_float(1.0)));

    // This evaluation should not work: `v_1` is not defined in the model, but
    // because evaluation is lazy and `t_1` is false with this model, it goes
    // through and the conjunction evaluates to false.

    assert_eval!( bool not model => conj )
}

#[test]
fn lazy_2() {
    init();
    let v_0 = term::real_var(0);
    let t_1 = term::ge(v_0, term::real(rat_of_float(0.0)));
    let v_1 = term::real_var(1001);
    let t_2 = term::ge(v_1, term::real(rat_of_float(0.0)));

    let disj = term::or(vec![t_1, t_2]);

    let model = model!(val::real(rat_of_float(1.0)));

    // This evaluation should not work: `v_1` is not defined in the model, but
    // because evaluation is lazy and `t_1` is false with this model, it goes
    // through and the conjunction evaluates to false.

    assert_eval!( bool model => disj )
}

#[test]
fn lazy_3() {
    init();
    let v_0 = term::real_var(0);
    let t_1 = term::ge(v_0.clone(), term::real(rat_of_float(7.0)));
    let v_1 = term::real_var(1002);
    let ite = term::ite(t_1, v_1, v_0);

    let model = model!(val::real(rat_of_float(1.0)));

    assert_eval!( real model => ite, 1.0 )
}

#[test]
fn lazy_4() {
    init();
    let v_0 = term::real_var(0);
    let t_1 = term::u_minus(v_0.clone());
    let v_1 = term::real_var(1003);
    let distinct = term::distinct(vec![t_1, v_0, v_1]);

    let model = model!(val::real(rat_of_float(0.0)));

    assert_eval!( bool not model => distinct )
}

// #[test]
// fn models() {
//   let v_1 = term::bool_var(0) ;
//   let v_2 = term::int_var(1) ;
//   let v_3 = term::int_var(2) ;

//   let model_1 = model!( true, 2, 3 ) ;
//   let model_2 = model!( true, 7, 0 ) ;

//   // (7 - v_2) + (v_2 * 2) + (- v_3)
//   let lhs = term::add(
//     vec![
//       term::sub( vec![ int(7), v_2.clone() ] ),
//       term::mul( vec![ v_2.clone(), int(2) ] ),
//       term::sub( vec![ v_3.clone() ] ),
//     ]
//   ) ;
//   assert_eval!(int model_1 => lhs, 6) ;
//   assert_eval!(int model_2 => lhs, 14) ;

//   // v_3 * 3
//   let rhs = term::mul( vec![ v_3.clone(), int(3) ] ) ;
//   assert_eval!(int model_1 => rhs, 9) ;
//   assert_eval!(int model_2 => rhs, 0) ;

//   // 7 + v_2 + (- v_3) > v_3 * 3
//   let gt = term::gt(lhs.clone(), rhs.clone()) ;
//   assert_eval!(bool not model_1 => gt) ;
//   assert_eval!(bool     model_2 => gt) ;

//   // v_1 && (7 + v_2 + (- v_3) > v_3 * 3)
//   let and = term::and( vec![ v_1.clone(), gt.clone() ] ) ;
//   assert_eval!(bool not model_1 => and) ;
//   assert_eval!(bool     model_2 => and) ;

//   ()
// }

// #[test]
// fn partial_eval() {
//   let v_1 = term::bool_var(0) ;
//   let v_2 = term::bool_var(1) ;
//   let v_3 = term::bool_var(2) ;

//   println!("and") ;
//   let term = term::and(
//     vec![ v_1.clone(), v_2.clone(), v_3.clone() ]
//   ) ;
//   let model = model!( (), true, false ) ;
//   assert_eval!{ bool not model => term }
//   let term = term::and(
//     vec![ term::fls(), v_1.clone() ]
//   ) ;
//   assert_eval!{ bool not model => term }
//   let term = term::and(
//     vec![
//       term::eq( term::int(2), term::add(vec![v_1.clone(), term::int(7)]) ),
//       term::tru(),
//       v_3.clone()
//     ]
//   ) ;
//   assert_eval!{ bool not model => term }

//   println!("or") ;
//   let term = term::or(
//     vec![ v_1.clone(), v_2.clone(), v_3.clone() ]
//   ) ;
//   let model = model!( (), true, false ) ;
//   assert_eval!{ bool model => term }
//   let term = term::or(
//     vec![ term::tru(), v_1.clone() ]
//   ) ;
//   assert_eval!{ bool model => term }
//   let term = term::or(
//     vec![
//       term::eq( term::int(2), term::add(vec![v_1.clone(), term::int(7)]) ),
//       term::tru(),
//       v_3.clone()
//     ]
//   ) ;
//   assert_eval!{ bool model => term }

//   println!("ite") ;
//   let term = term::ite(
//     v_1.clone(), v_2.clone(), v_3.clone()
//   ) ;
//   let model = model!( true, 7, () ) ;
//   assert_eval!{ int model => term, 7 }
//   let model = model!( false, (), 3 ) ;
//   assert_eval!{ int model => term, 3 }

//   println!("=>") ;
//   let term = term::implies(
//     v_1.clone(), v_2.clone()
//   ) ;
//   let model = model!( false, ()) ;
//   assert_eval!{ bool model => term }
//   let model = model!( (), true) ;
//   assert_eval!{ bool model => term }

//   println!("mul") ;
//   let term = term::mul(
//     vec![ v_1.clone(), v_2.clone(), v_3.clone() ]
//   ) ;
//   let model = model!( 3, (), 0 ) ;
//   assert_eval!{ int model => term, 0 }

//   println!("mod") ;
//   let term = term::modulo( v_1.clone(), v_2.clone() ) ;
//   let model = model!( (), 1 ) ;
//   assert_eval!{ int model => term, 0 }
// }

// use term::{ tru, fls } ;

// macro_rules! eq {
//   ($(> $lhs:expr, $rhs:expr);* $(;)*) => ({
//     $({
//       let (lhs, rhs) = ($lhs, $rhs) ;
//       println!("") ;
//       println!("     got: {}", lhs) ;
//       println!("expected: {}", rhs) ;
//       assert_eq!(lhs, rhs) ;
//     })*
//   }) ;
// }

// fn bool_var() -> Term { term::bool_var(0) }
// fn int_var() -> Term { term::int_var(0) }

// #[test]
// fn and_simplify() {
//   eq!{
//     > term::and( vec![ bool_var() ] ),
//       bool_var() ;
//     > term::and( vec![ tru(), bool_var(), tru() ] ),
//       bool_var() ;
//     > term::and( vec![ tru(), fls(), bool_var() ] ),
//       fls() ;
//     > term::and( vec![] ),
//       tru() ;
//     > term::and( vec![
//         tru(),
//         term::eq( int_var(), int_var() ),
//       ] ),
//       tru() ;
//   }
// }

// #[test]
// fn or_simplify() {
//   eq!{
//     > term::or( vec![ bool_var() ] ),
//       bool_var() ;
//     > term::or( vec![ fls(), bool_var(), fls() ] ),
//       bool_var() ;
//     > term::or( vec![ fls(), tru(), bool_var() ] ),
//       tru() ;
//     > term::or( vec![] ),
//       fls() ;
//     > term::or( vec![
//         fls(),
//         term::eq( int_var(), int_var() ),
//       ] ),
//       tru() ;
//   }
// }

// #[test]
// fn ge_simplify() {
//   eq!{
//     > term::ge( int_var(), int_var() ),
//       tru() ;
//     > term::ge( int(7), int(-3) ),
//       tru() ;
//     > term::ge( int(-42), int(0) ),
//       fls() ;
//   }
// }

// #[test]
// fn le_simplify() {
//   eq!{
//     > term::le( int_var(), int_var() ),
//       tru() ;
//     > term::le( int(7), int(-3) ),
//       fls() ;
//     > term::le( int(-42), int(0) ),
//       tru() ;
//   }
// }

// #[test]
// fn gt_simplify() {
//   eq!{
//     > term::gt( int_var(), int_var() ),
//       fls() ;
//     > term::gt( int(7), int(-3) ),
//       tru() ;
//     > term::gt( int(-42), int(0) ),
//       fls() ;
//   }
// }

// #[test]
// fn lt_simplify() {
//   eq!{
//     > term::lt( int_var(), int_var() ),
//       fls() ;
//     > term::lt( int(7), int(-3) ),
//       fls() ;
//     > term::lt( int(-42), int(0) ),
//       tru() ;
//   }
// }

// #[test]
// fn eq_simplify() {
//   eq!{
//     > term::eq( int_var(), int_var() ),
//       tru() ;
//     > term::eq( fls(), bool_var() ),
//       term::not(bool_var()) ;
//     > term::eq( tru(), bool_var() ),
//       bool_var() ;
//     > term::eq( bool_var(), fls() ),
//       term::not(bool_var()) ;
//     > term::eq( bool_var(), tru() ),
//       bool_var() ;
//     > term::eq( int(7), int(3) ),
//       fls() ;
//     > term::eq( int(3), int(3) ),
//       tru() ;
//   }
// }

// #[test]
// fn not_simplify() {
//   eq!{
//     > term::not( tru() ),
//       fls() ;
//     > term::not( fls() ),
//       tru() ;
//     > term::not( term::not( bool_var() ) ),
//       bool_var() ;
//     > term::not( term::and( vec![ bool_var(), term::bool_var(7) ] ) ),
//       term::or(
//         vec![ term::not(bool_var()), term::not( term::bool_var(7) ) ]
//       ) ;
//     > term::not( term::or( vec![ bool_var(), term::bool_var(7) ] ) ),
//       term::and(
//         vec![ term::not(bool_var()), term::not( term::bool_var(7) ) ]
//       ) ;
//   }
// }

// #[test]
// fn add_simplify() {
//   eq!{
//     > term::add( vec![ int(7), int(3) ] ),
//       int(10) ;
//     > term::add( vec![ int(7), int_var(), int(-3) ] ),
//       term::add( vec![ int_var(), int(4) ] ) ;
//     > term::add( vec![ int(-42), int_var() ] ),
//       term::add( vec![ int_var(), int(-42) ] ) ;
//   }
// }

// #[test]
// fn mul_simplify() {
//   eq!{
//     > term::mul( vec![ int(7), int(3) ] ),
//       int(21) ;
//     > term::mul( vec![ int(7), int_var(), int(-3) ] ),
//       term::mul( vec![ int_var(), int(-21) ] ) ;
//     > term::mul( vec![ int(-42), int_var() ] ),
//       term::mul( vec![ int_var(), int(-42 ) ] ) ;
//   }
// }

// #[test]
// fn invert() {
//   let term = term::u_minus( int_var() ) ;
//   let invert = term.invert( term::int_var(1) ).unwrap() ;
//   eq!{
//    > invert.1,
//      term::u_minus( term::int_var(1) ) ;
//    > invert.0,
//      0 ;
//   }
//   let term = term::sub( vec![ term::int(7), int_var() ] ) ;
//   let invert = term.invert( term::int_var(1) ).unwrap() ;
//   eq!{
//    > invert.1,
//      term::sub( vec![ term::int(7), term::int_var(1) ] ) ;
//    > invert.0,
//      0 ;
//   }
//   let term = term::sub( vec![ term::int_var(0), term::int(7) ] ) ;
//   let invert = term.invert( term::int_var(1) ).unwrap() ;
//   eq!{
//    > invert.1,
//      term::add( vec![ term::int_var(1), term::int(7) ] ) ;
//    > invert.0,
//      0 ;
//   }

//   let term = term::add( vec![ term::int(7), term::int_var(0) ] ) ;
//   let invert = term.invert( term::int_var(1) ).unwrap() ;
//   eq!{
//    > invert.1,
//      term::sub( vec![ term::int_var(1), term::int(7) ] ) ;
//    > invert.0,
//      0 ;
//   }
//   let term = term::add( vec![ term::int_var(0), term::int(7) ] ) ;
//   let invert = term.invert( term::int_var(1) ).unwrap() ;
//   eq!{
//    > invert.1,
//      term::sub( vec![ term::int_var(1), term::int(7) ] ) ;
//    > invert.0,
//      0 ;
//   }

//   // let term = term::mul( vec![ term::int(7), term::var(0) ] ) ;
//   // let invert = term.invert( term::var(1) ).unwrap() ;
//   // eq!{
//   //  > invert.1,
//   //    term::div( vec![ term::var(1), term::int(7) ] ) ;
//   //  > invert.0,
//   //    0 ;
//   // }
//   // let term = term::mul( vec![ term::var(0), term::int(7) ] ) ;
//   // let invert = term.invert( term::var(1) ).unwrap() ;
//   // eq!{
//   //  > invert.1,
//   //    term::div( vec![ term::var(1), term::int(7) ] ) ;
//   //  > invert.0,
//   //    0 ;
//   // }
// }

// macro_rules! parser {
//   (
//     vars {
//       $($ident:expr => $typ:expr),* $(,)*
//     }
//     $(
//       if let parse($term:ident) = $str:tt $b:tt
//     )*
//   ) => ({
//     let instance = ::instance::Instance::new() ;
//     let mut parser = ::instance::parse::ParserCxt::new() ;
//     let (mut map, mut var_map) = (
//       HashMap::new(), VarMap::new()
//     ) ;
//     $(
//       let idx = var_map.next_index() ;
//       let ident = $ident ;
//       var_map.push(
//         ::instance::info::VarInfo::new(
//           ident.into(), $typ, idx
//         )
//       ) ;
//       map.insert(ident, idx) ;
//     )*
//     $({
//       let text = $str ;
//       let mut parser = parser.parser(text, 0) ;
//       let $term = parser.term_opt(
//         & var_map, & map, & instance
//       ).expect(
//         "while parsing term"
//       ).expect(
//         "failed to parse term"
//       ) ;
//       println!("term: {}", $term) ;
//       parser! { @ $b }
//     })*
//   }) ;

//   (@ { $term:ident by $model:ident == $val:expr } ) => ({
//     let val = $term.eval(& $model).expect("evaluation failed") ;
//     println!("{} =? {}", val, $val) ;
//     debug_assert_eq! { val, $val.into() }
//   }) ;

//   // ($($tt:tt)*) => ($($tt)*) ;
// }

// #[test]
// fn bug_find() {
//   use term::Typ ;
//   let mut model = VarMap::new() ;
//   model.push( Val::I( 2.into() ) ) ;
//   model.push( Val::I( 2.into() ) ) ;
//   model.push( Val::I( 0.into() ) ) ;
//   model.push( Val::I( 2.into() ) ) ;
//   model.push( Val::I( 2.into() ) ) ;

//   parser! {
//     vars {
//       "v_0" => Typ::Int,
//       "v_1" => Typ::Int,
//       "v_2" => Typ::Int,
//       "v_3" => Typ::Int,
//       "v_4" => Typ::Int,
//     }

//     if let parse(term) = "(and
//       (> (/ (+ v_1 (- 1)) 2) (div v_0 2))
//       (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_2))
//     )" {
//       term by model == false
//     }

//     if let parse(term) = "(and
//       (>= (div v_0 2) (/ (+ v_1 (- 1)) 2))
//       (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_2))
//       (= v_3 (+ 1 (* 2 (/ (+ v_3 (- 1)) 2))))
//       (or
//         (> 0 v_0) (> (/ v_1 2) (div v_0 2)) (> 0 (/ v_1 2)) (> (/ v_1 2) v_0)
//       )
//     )" {
//       term by model == false
//     }

//     if let parse(term) = "(and
//       (>= v_1 0)
//       (>= v_0 0)
//       (>= v_0 v_1)
//       (>= (div v_0 2) (/ (+ v_1 (- 1)) 2))
//       (>= v_0 (/ (+ v_1 (- 1)) 2))
//       (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_2))
//       (> v_3 v_0)
//       (= v_2 (+ 1 (* 2 (/ (+ v_2 (- 1)) 2))))
//       (not (= v_3 (+ 1 (* 2 (/ (+ v_3 (- 1)) 2)))))
//     )" {
//       term by model == false
//     }

//     if let parse(term) = "(and
//       (>= v_0 0)
//       (= v_1 (+ 1 (* 2 (/ (+ v_1 (- 1)) 2))))
//       (>= (div v_0 2) (/ (+ v_1 (- 1)) 2))
//       (>= (div v_0 2) (/ v_1 2))
//       (>= v_0 (/ (+ v_1 (- 1)) 2))
//       (>= (/ v_1 2) 0)
//       (>= v_0 (/ v_1 2))
//       (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_2))
//       (= v_2 (+ 1 (* 2 (/ (+ v_2 (- 1)) 2))))
//       (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_3))
//       (not (= v_3 (+ 1 (* 2 (/ (+ v_3 (- 1)) 2)))))
//     )" {
//       term by model == false
//     }

//     if let parse(term) = "(and
//       (= v_1 (+ 1 (* 2 (/ (+ v_1 (- 1)) 2))))
//       (>= (div v_0 2) (/ (+ v_1 (- 1)) 2))
//       (>= v_0 (/ (+ v_1 (- 1)) 2))
//       (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_2))
//       (or
//         (> 0 v_3) (> (/ v_4 2) (div v_3 2)) (> 0 (/ v_4 2)) (> (/ v_4 2) v_3)
//       )
//       (= v_2 (+ 1 (* 2 (/ (+ v_2 (- 1)) 2))))
//       (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_3))
//       (not (= v_3 (+ 1 (* 2 (/ (+ v_3 (- 1)) 2)))))
//       (or
//         (> 0 v_0) (> (/ v_1 2) (div v_0 2)) (> 0 (/ v_1 2)) (> (/ v_1 2) v_0)
//       )
//     )" {
//       term by model == false
//     }

//     if let parse(term) = "(+ 1 (* 2 (/ (+ v_1 (- 1)) 2)))" {
//       term by model == 2
//     }

//     if let parse(term) = "(or
//       (and
//         (= 0 v_0)
//         (or (> 0 v_1) (> 0 v_0) (> v_1 v_0) (>= v_0 v_2))
//         (not (= 0 v_1))
//         (>= (+ v_3 (* v_0 (- 1))) 0)
//         (>= v_0 v_3)
//         (> 2 v_1)
//       )
//     )" {
//       term by model == false
//     }
//   }
// }

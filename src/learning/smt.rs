//! Pure SMT learner.

use rsmt2::{ ParseSmt2 } ; // , SolverConf, Kid } ;

use nom::IResult ;

use common::* ;
use common::data::* ;
use common::msg::* ;
use instance::{ Instance, Op } ;

/// Launches an smt learner.
pub struct Launcher ;
unsafe impl Sync for Launcher {}
unsafe impl Send for Launcher {}
impl Launcher {
  /// Launches an smt learner.
  pub fn launch(
    core: & LearnerCore, instance: Arc<Instance>
  ) -> Res<()> {
    use rsmt2::{ solver, Kid } ;
    let mut kid = Kid::new( conf.solver.conf() ).chain_err(
      || "while spawning the teacher's solver"
    ) ? ;
    let solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("smt_learner") ? {
      (
        SmtLearner::new(& core, instance, solver.tee(log)) ?
      ).run()
    } else {
      (
        SmtLearner::new(& core, instance, solver) ?
      ).run()
    }
  }
}
impl Learner for Launcher {
  fn run(
    & self, core: LearnerCore, instance: Arc<Instance>, _: Arc<Data>
  ) {
    if let Err(e) = Self::launch(& core, instance) {
      let _ = core.err(e) ;
    }
  }
  fn description(& self) -> String {
    "smt".into()
  }
}

/// Stores the counterexamples so far and the instance.
pub struct SmtLearner<'core, Solv> {
  /// Learner core.
  core: & 'core LearnerCore,
  /// The instance.
  pub instance: Arc<Instance>,
  /// Solver.
  pub solver: Solv,
  /// Positive data.
  pub pos: HashSet<Sample>,
  /// Negative data.
  pub neg: HashSet<Sample>,
  /// Constraints.
  pub cstr: HashSet<Constraint>,
}
impl<'core, Solv> HasLearnerCore for SmtLearner<'core, Solv> {
  fn core(& self) -> & LearnerCore { self.core }
}
impl<'core, 'kid, Solv: Solver<'kid, Parser>> SmtLearner<'core, Solv> {
  /// Constructor.
  pub fn new(
    core: & 'core LearnerCore, instance: Arc<Instance>, mut solver: Solv,
  ) -> Res<Self> {

    for info in instance.preds() {
      use instance::Typ ;
      // Declare coefficients.
      for (idx, _) in info.sig.index_iter() {
        let coeff = format!("c_{}_{}", info.idx, idx) ;
        solver.declare_const( & coeff, & Typ::Int, & () ) ?
      }
      let coeff = format!("c_{}", info.idx) ;
      solver.declare_const( & coeff, & Typ::Int, & () ) ? ;

      // Define predicate.
      let args: Vec<_> = info.sig.index_iter().map(
        |(idx, _)| (idx, "Int")
      ).collect() ;
      let wrapped = & PWrap(info) ;
      solver.define_fun(
        info, & args, & "Bool", wrapped, & ()
      ) ?
    }

    Ok(
      SmtLearner {
        core, instance, solver,
        pos:  HashSet::with_capacity(1000),
        neg:  HashSet::with_capacity(1000),
        cstr: HashSet::with_capacity(1000),
      }
    )
  }

  /// Runs the learner.
  pub fn run(mut self) -> Res<()> {
    let mut teacher_alive = true ;
    'learn: loop {
      if ! teacher_alive {
        bail!("teacher is dead T__T")
      }
      match self.recv() {
        Some(data) => if let Some(candidates) = self.learn(data) ? {
          teacher_alive = self.send_candidates(
            candidates
          )
        } else {
          self.err(
            "unsat on linear synthesis\n\
            can't synthesize candidates for this, sorry".into()
          ) ;
          bail!("can't solve this T__T")
        },
        None => teacher_alive = false,
      }
    }
  }

  /// Integrates new learning data and returns consistent candidates.
  pub fn learn(& mut self, data: LearningData) -> Res< Option<Candidates> > {

    let LearningData { pos, neg, cstr } = data ;

    // Assert stuff.
    for pos in & pos {
      self.solver.assert( & SplWrap(pos, true), & () ) ?
    }
    for neg in & neg {
      self.solver.assert( & SplWrap(neg, false), & () ) ?
    }
    for cstr in & cstr {
      self.solver.assert( & CstrWrap(cstr), & () ) ?
    }

    // Issue check-sat.
    self.solver.print_check_sat() ? ;

    // Store stuff in the mean time.
    for pos in pos {
      let _ = self.pos.insert( pos.clone() ) ;
    }
    for neg in neg {
      let _ = self.neg.insert( neg.clone() ) ;
    }
    for cstr in cstr {
      let _ = self.cstr.insert( cstr.clone() ) ;
    }

    // Get check-sat result.
    if self.solver.parse_check_sat() ? {
      
      let model = self.solver.get_model() ? ;
      // Setting all coefficients to `None` for now.
      let mut coefs: PrdMap<
        (VarMap<_>, _)
      > = self.instance.preds().iter().map(
        |pred_info| (
          pred_info.sig.iter().map(|_| None).collect(), None
        )
      ).collect() ;
      // Populate coef map.
      for ((pred, var_opt), val) in model {
        let pred = & mut coefs[pred] ;
        if let Some(var) = var_opt {
          pred.0[var] = Some(val)
        } else {
          pred.1 = Some(val)
        }
      }

      // println!("coefs:") ;
      // for (pred, & (ref map, ref rhs)) in coefs.index_iter() {
      //   print!("  c_{}: ", pred) ;
      //   if let Some(ref rhs) = * rhs {
      //     println!("{}", rhs)
      //   } else {
      //     println!("_")
      //   }
      //   for (var, coef) in map.index_iter() {
      //     print!("  c_{}_{}: ", pred, var) ;
      //     if let Some(ref coef) = * coef {
      //       println!("{}", coef)
      //     } else {
      //       println!("_")
      //     }
      //   }
      //   println!("") ;

      // }

      let map: PrdMap<_> = coefs.into_iter().map(
        |(coefs, constant)| self.instance.op(
          Op::Ge, vec![
            self.instance.op(
              Op::Add,
              coefs.into_index_iter().map(
                |(idx, coef)| self.instance.op(
                  Op::Mul, vec![
                    if let Some(coef) = coef {
                      self.instance.int(coef)
                    } else {
                      self.instance.zero()
                    },
                    self.instance.var(idx)
                  ]
                )
              ).collect()
            ),
            if let Some(rhs) = constant {
              self.instance.int(rhs)
            } else {
              self.instance.zero()
            }
          ]
        )
      ).collect() ;

      // println!("terms:") ;
      // for term in map.iter() {
      //   println!("  {}", term)
      // }
      // println!("") ;

      Ok(Some(map))
    } else {
      Ok(None)
    }
  }
}



/// Wrapper around predicates info for smt definition.
pub struct PWrap<'a>(& 'a ::instance::info::PrdInfo) ;
impl<'a> ::rsmt2::Expr2Smt<()> for PWrap<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> {
    let PWrap(info) = * self ;
    smt_cast_io!(
      "writing predicate as expression" =>
      write!(w, "(<= c_{} (+ ", info.idx) ; {
        for (var, _) in info.sig.index_iter() {
          smtry_io!(
            "writing predicate as expression" =>
            write!(w, "(* c_{}_{} v_{})", info.idx, var, var)
          )
        }
        Ok(()) as IoRes<()>
      } ;
      write!(w, "))")
    )
  }
}

/// Wrapper around samples for smt.
pub struct SplWrap<'a>(& 'a Sample, bool) ;
impl<'a> ::rsmt2::Expr2Smt<()> for SplWrap<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> {
    let SplWrap(sample, pos) = * self ;
    smt_cast_io!(
      "writing sample as expression" =>
      if pos { Ok(()) } else {
        write!(w, " (not ")
      } ;
      write!(w, "(p_{}", sample.pred) ;
      {
        for arg in sample.args.iter() {
          smtry_io!(
            "writing sample as expression" =>
            write!(w, " {}", arg).into()
          )
        }
        Ok(()) as IoRes<()>
      } ;
      write!(w, ")") ;
      if pos { Ok(()) } else {
        write!(w, ")")
      } ;
    )
  }
}

/// Wrapper around constraints for smt.
pub struct CstrWrap<'a>(& 'a Constraint) ;
impl<'a> ::rsmt2::Expr2Smt<()> for CstrWrap<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> {
    let CstrWrap(constraint) = * self ;
    smt_cast_io!(
      "writing constraint as expression" =>
      write!(w, "(=> (and") ;
      {
        for lhs in & constraint.lhs {
          smtry_io!{
            "writing constraint as expression" =>
            write!(w, " ") ;
          }
          SplWrap(lhs, true).expr_to_smt2(w, & ()) ?
        }
        Ok(()) as IoRes<()>
      } ;
      write!(w, ") ") ;
      {
        match constraint.rhs {
          None => smtry_io!(
            "writing constraint as expression" =>
            write!(w, "false")
          ),
          Some(ref rhs) => SplWrap(rhs, true).expr_to_smt2(w, & ()) ?,
        }
        Ok(()) as IoRes<()>
      } ;
      write!(w, ")") ;
    )
  }
}



#[doc = r#"Unit type parsing the output of the SMT solver.

Parses coefficients of the form `c_<int>_<int>` or `c_<int>`. The first integer
is the index of the predicate this coefficient is for, and the second integer
(optional) is the index of the predicate's variable it's a coefficient for.

The convention must match the predicate definition strategy:

```lisp
(define-fun p_<pred> ( (v_<var> Int) ... ) Int
  (>=
    (+ (* c_<pred>_<var> v_<var>) ...)
    c_<pred>
  )
)
```
"#]
pub struct Parser ;
impl ParseSmt2 for Parser {
  type Ident = (PrdIdx, Option<VarIdx>) ;
  type Value = Int ;
  type Expr = () ;
  type Proof = () ;
  type I = () ;

  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], (PrdIdx, Option<VarIdx>)> {
    use std::str::FromStr ;
    do_parse!(
      bytes,
      tag!("c_") >>
      pred: map_res!(
        map_res!(
          re_bytes_find!("^[0-9][0-9]*"),
          ::std::str::from_utf8
        ),
        usize::from_str
      ) >>
      var: opt!(
        preceded!(
          char!('_'),
          map_res!(
            map_res!(
              re_bytes_find!("^[0-9][0-9]*"),
              ::std::str::from_utf8
            ),
            usize::from_str
          )
        )
      ) >> (
        ( pred.into(), var.map( |i| i.into() ) )
      )
    )
  }

  fn parse_value<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], Int> {
    use instance::build::{ int, spc_cmt } ;
    dbg_dmp!(bytes, alt_complete!(
      // bytes,
      int | do_parse!(
        char!('(') >>
        spc_cmt >> char!('-') >>
        spc_cmt >> value: int >>
        spc_cmt >> char!(')') >>
        (- value)
      )
    ))
  }

  fn parse_expr<'a>(
    & self, _: & 'a [u8], _: & ()
  ) -> IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_expr` should never be called")
  }

  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_proof` should never be called")
  }
}

#![doc = r#"Checks the result of a `hoice` run.

This code is completely separated from the rest of the code, on purpose. It
basically takes the original `smt2` file, a file containing the output of the
`hoice` run, and checks that the result makes sense.

It does so using an SMT solver, and performing string substitution (roughly)
to rewrite the problem as a pure SMT query. In particular, there is no real
notion of term here."#]

use errors::* ;
use common::{ conf, ColorExt, Solver, HashMap, Read } ;

pub mod parse ;

use self::parse::InParser ;
use self::smt::* ;

/// A predicate is just a string.
pub type Pred = String ;
/// A type is just a string.
pub type Typ = String ;
/// A signature.
pub type Sig = Vec<Typ> ;

/// A predicate declaration.
pub struct PredDec {
  /// Predicate.
  pub pred: Pred,
  /// Signature.
  pub sig: Sig,
}

/// An ident is just a string.
pub type Ident = String ;
/// A value is a string.
pub type Value = String ;
/// A list of arguments.
pub type Args = Vec<(Ident, Typ)> ;
/// A term is just a string.
pub type Term = String ;

/// A predicate definition.
pub struct PredDef {
  /// Predicate.
  pub pred: Pred,
  /// Arguments.
  pub args: Args,
  /// Body.
  pub body: Option<Term>,
}

/// A clause.
pub struct Clause {
  /// Arguments.
  pub args: Args,
  /// Body.
  pub body: Term,
  // /// Let bindings.
  // pub lets: Vec< Vec<(Ident, String)> >,
  // /// LHS.
  // pub lhs: Vec<Term>,
  // /// RHS.
  // pub rhs: Term,
}

/// Data from the input file.
pub struct Input {
  /// Predicate declarations.
  pub pred_decs: Vec<PredDec>,
  /// Clauses.
  pub clauses: Vec<Clause>,
}
impl Input {
  /// Loads some input data from a file.
  pub fn of_file<P: AsRef<::std::path::Path>>(file: P) -> Res<Self> {
    use std::fs::OpenOptions ;
    let file = file.as_ref() ;
    info!{
      "loading horn clause file {}...", conf.emph(file.to_string_lossy())
    }
    let mut buff = String::new() ;
    OpenOptions::new().read(true).open(file).chain_err(
      || format!(
        "while opening file {}", conf.emph(file.to_string_lossy())
      )
    )?.read_to_string(& mut buff).chain_err(
      || format!(
        "while reading file {}", conf.emph(file.to_string_lossy())
      )
    )? ;
    Self::of_str(& buff)
  }
  /// Loads some input data from a string.
  pub fn of_str(data: & str) -> Res<Self> {
    InParser::new(data).parse_input()
  }
}

/// Output of a `hoice` run.
pub struct Output {
  /// Predicate definitions.
  pub pred_defs: Vec<PredDef>,
}
impl Output {
  /// Loads some input data from a file.
  pub fn of_file(file: & str) -> Res<Self> {
    use std::fs::OpenOptions ;
    info!{ "loading hoice output file {}...", conf.emph(file) }
    let mut buff = String::new() ;
    OpenOptions::new().read(true).open(file).chain_err(
      || format!( "while opening file {}", conf.emph(file) )
    )?.read_to_string(& mut buff).chain_err(
      || format!( "while reading file {}", conf.emph(file) )
    )? ;
    Self::of_str(& buff)
  }
  /// Loads some input data from a string.
  pub fn of_str(data: & str) -> Res<Self> {
    InParser::new(data).parse_output()
  }

  /// Checks the signature of the predicates match the declarations of an input
  /// `hc` file. Also checks that all predicates are defined *once*.
  pub fn check_consistency(& mut self, input: & Input) -> Res<()> {
    info!{ "checking predicate signature consistency..." }
    let mut map = HashMap::with_capacity( self.pred_defs.len() ) ;
    for & PredDef { ref pred, ref args, .. } in & self.pred_defs {
      let prev = map.insert(pred.clone(), args.clone()) ;
      if prev.is_some() {
        bail!(
          "predicate {} is defined twice in hoice's output", conf.emph(pred)
        )
      }
    }
    for & PredDec { ref pred, ref sig } in & input.pred_decs {
      if let Some(args) = map.get(pred) {
        if sig.len() != args.len() {
          bail!(
            "arguments of predicate {}'s definition \
            does not match its signature", conf.emph(pred)
          )
        }
        let mut count = 0 ;
        for (ty_1, & (ref arg, ref ty_2)) in sig.iter().zip( args.iter() ) {
          if ty_1 != ty_2 {
            bail!(
              "type of argument {} ({}) in predicate {}'s definition ({}) \
              match that of the input file ({})",
              count, arg, conf.emph(pred), ty_2, ty_1
            )
          }
          count += 1
        }
      } else {
        warn!(
          "predicate {} is not defined in hoice's output", conf.emph(pred)
        ) ;
        let mut args = vec![] ;
        let mut cnt = 0 ;
        for ty in sig {
          args.push( (format!("v_{}", cnt), ty.clone()) ) ;
          cnt += 1
        }
        self.pred_defs.push(
          PredDef { pred: pred.clone(), args, body: None }
        )
      }
    }
    Ok(())
  }
}


/// Aggregates the input and output data.
pub struct Data {
  /// Input data.
  pub input: Input,
  /// Output data.
  pub output: Output,
}
impl Data {
  /// Direct contructor.
  pub fn new(input: Input, mut output: Output) -> Res<Self> {
    output.check_consistency(& input) ? ;
    Ok( Data { input, output } )
  }
  /// Reads two files for input and output data.
  pub fn of_files(input_file: & str, output_file: & str) -> Res<Self> {
    let input = Input::of_file(input_file) ? ;
    let output = Output::of_file(output_file) ? ;
    Self::new(input, output)
  }

  /// Checks the output data works with the input data using an SMT solver.
  pub fn check< 'kid, S: Solver<'kid, Parser> >(
    & self, mut solver: S
  ) -> Res<()> {

    let mut okay = true ;
    let mut count = 0 ;

    // Check all clauses one by one.
    for & Clause {
      ref args, ref body // ref lets, ref lhs, ref rhs
    } in & self.input.clauses {
      count += 1 ;
      solver.reset() ? ;
      // Define all predicates.
      for & PredDef {
        ref pred, ref args, ref body
      } in & self.output.pred_defs {
        if let Some(body) = body.as_ref() {
          solver.define_fun(
            pred, args, & "Bool".to_string(), body
          ) ?
        } else {
          solver.declare_fun(
            pred,
            & args.iter().map(
              |& (_, ref typ)| typ.clone()
            ).collect::<Vec<_>>(),
            & "Bool".to_string()
          ) ?
        }
      }

      // Declare arguments.
      for & (ref ident, ref typ) in args {
        solver.declare_const(ident, typ) ?
      }

      solver.assert( & format!("(not {})", body) ) ? ;

      let res = solver.check_sat_or_unknown() ? ;

      if let & Some(true) = & res {
        okay = false ;
        let exprs: Vec<_> = args.iter().map(
          |& (ref id, _)| id.clone()
        ).collect() ;
        let model = solver.get_values(& exprs) ? ;
        println!("") ;
        println!("({} \"", conf.bad("error")) ;
        println!("  clause {} is falsifiable with {{", count) ;
        // print!(  "   ") ;
        // for & (ref id, ref ty) in args {
        //   print!(" ({} {})", id, ty)
        // }
        // println!("") ;
        // println!("    (=>") ;
        // println!("      (and") ;
        // for lhs in lhs {
        //   println!("        {}", lhs)
        // }
        // println!("      ) {}", rhs) ;
        // println!("    )") ;
        // println!("  is falsifiable with {{") ;
        for (ident, value) in model {
          println!("    {}: {},", ident, value)
        }
        println!("  }}") ;
        println!("\")") ;
        println!("")
      } else if let & Some(false) = & res {
        info!("clause {} is fine", count)
      } else {
        warn!(
          "clause {}'s check resulted in unknown, assuming it's fine", count
        )
      }
    }

    if ! okay {
      bail!(
        "predicates do not verify all the clauses of the input file"
      )
    }

    Ok(())
  }
}



/// Checks a `hoice` run from two files.
pub fn do_it(input_file: & str, output_file: & str) -> Res<()> {
  use rsmt2::{ solver, Kid } ;
  let data = Data::of_files(input_file, output_file) ? ;

  let mut kid = Kid::new( conf.solver.conf() ).chain_err(
    || ErrorKind::Z3SpawnError
  ) ? ;
  {
    let solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the checkers solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("check") ? {
      data.check(solver.tee(log)) ?
    } else {
      data.check(solver) ?
    }
  }
  println!("(safe)") ;
  kid.kill().chain_err(
    || "while killing solver kid"
  ) ? ;
  Ok(())
}




/// Checks a `hoice` run, script from a file, model from a string.
///
/// This is currently only used for testing purposes.
#[cfg(test)]
pub fn do_it_from_str<P: AsRef<::std::path::Path>>(
  input_file: P, model: & str
) -> Res<()> {
  use rsmt2::{ solver, Kid } ;
  let data = Data::new(
    Input::of_file(input_file).chain_err(
      || "while loading input file"
    ) ?,
    Output::of_str(model).chain_err(
      || "while loading model"
    ) ?
  ) ? ;

  let mut kid = Kid::new( conf.solver.conf() ).chain_err(
    || ErrorKind::Z3SpawnError
  ) ? ;
  {
    let solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the checkers solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("check") ? {
      data.check(solver.tee(log)) ?
    } else {
      data.check(solver) ?
    }
  }
  kid.kill().chain_err(
    || "while killing solver kid"
  ) ? ;
  Ok(())
}










mod smt {
  use rsmt2::parse::{ IdentParser, ValueParser, ExprParser } ;
  use rsmt2::SmtRes ;

  use check::{ Ident, Value, Term } ;


/// Parser for the output of the SMT solver.
///
/// Parses idents and values as strings.
#[derive(Clone, Copy)]
pub struct Parser ;


  impl<'a> IdentParser<Ident, (), & 'a str> for Parser {
    fn parse_ident(self, input: & 'a str) -> SmtRes< Ident > {
      Ok( input.into() )
    }
    fn parse_type(self, _: & 'a str) -> SmtRes<()> {
      Ok(())
    }
  }

  impl<'a> ExprParser<Term, (), & 'a str> for Parser {
    fn parse_expr(self, input: & 'a str, _: ()) -> SmtRes<Term> {
      Ok( input.into() )
    }
  }

  impl<'a> ValueParser<Value, & 'a str> for Parser {
    fn parse_value(self, input: & 'a str) -> SmtRes<Value> {
      Ok( input.into() )
    }
  }
}
#![doc = r#"Checks the result of a `hoice` run.

This code is completely separated from the rest of the code, on purpose. It
basically takes the original `smt2` file, a file containing the output of the
`hoice` run, and checks that the result makes sense.

It does so using an SMT solver, and performing string substitution (roughly)
to rewrite the problem as a pure SMT query. In particular, there is no real
notion of term here."#]

use common::* ;

pub mod parse ;

use self::parse::{ parse_input, parse_output, parse_eld_output } ;

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
  pub body: Term,
}

/// A clause.
pub struct Clause {
  /// Arguments.
  pub args: Args,
  /// LHS.
  pub lhs: Vec<Term>,
  /// RHS.
  pub rhs: Term,
}

/// Data from the input file.
pub struct Input {
  /// Predicate declarations.
  pub pred_decs: Vec<PredDec>,
  /// Clauses.
  pub clauses: Vec<Clause>,
}
impl Input {
  /// Loads some input data from some bytes.
  pub fn of_bytes(bytes: & [u8]) -> Res<Self> {
    use nom::IResult ;
    match parse_input(bytes) {
      IResult::Done(_, input) => Ok(input),
      IResult::Error(e) => bail!(
        "parse error: {:?}", e
      ),
      IResult::Incomplete(_) => bail!(
        "parse error: incomplete..."
      ),
    }
  }
  /// Loads some input data from a file.
  pub fn of_file(file: & str) -> Res<Self> {
    use std::fs::OpenOptions ;
    info!{ "loading horn clause file {}...", conf.emph(file) }
    let mut buff = Vec::new() ;
    OpenOptions::new().read(true).open(file).chain_err(
      || format!( "while opening file {}", conf.emph(file) )
    )?.read_to_end(& mut buff).chain_err(
      || format!( "while reading file {}", conf.emph(file) )
    )? ;
    Self::of_bytes(& buff).chain_err(
      || format!( "while parsing file {}", conf.emph(file) )
    )
  }
}

/// Output of a `hoice` run.
pub struct Output {
  /// Predicate definitions.
  pub pred_defs: Vec<PredDef>,
}
impl Output {
  /// Loads some input data from some bytes.
  pub fn of_bytes(bytes: & [u8]) -> Res<Self> {
    use nom::IResult ;
    match if conf.check_eld {
      println!("eld...") ;
      parse_eld_output(bytes)
    } else {
      parse_output(bytes)
    } {
      IResult::Done(_, input) => Ok(input),
      IResult::Error(e) => bail!(
        "parse error: {:?}", e
      ),
      IResult::Incomplete(_) => bail!(
        "parse error: incomplete..."
      ),
    }
  }
  /// Loads some input data from a file.
  pub fn of_file(file: & str) -> Res<Self> {
    use std::fs::OpenOptions ;
    info!{ "loading hoice output file {}...", conf.emph(file) }
    let mut buff = Vec::new() ;
    OpenOptions::new().read(true).open(file).chain_err(
      || format!( "while opening file {}", conf.emph(file) )
    )?.read_to_end(& mut buff).chain_err(
      || format!( "while reading file {}", conf.emph(file) )
    )? ;
    Self::of_bytes(& buff).chain_err(
      || format!( "while parsing file {}", conf.emph(file) )
    )
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
          PredDef { pred: pred.clone(), args, body: "true".into() }
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
  pub fn mk(input: Input, mut output: Output) -> Res<Self> {
    output.check_consistency(& input) ? ;
    Ok( Data { input, output } )
  }
  /// Reads two files for input and output data.
  pub fn of_files(input_file: & str, output_file: & str) -> Res<Self> {
    let input = Input::of_file(input_file) ? ;
    let output = Output::of_file(output_file) ? ;
    Self::mk(input, output)
  }

  /// Checks the output data works with the input data using an SMT solver.
  pub fn check< 'kid, S: Solver<'kid, Parser> >(
    & self, mut solver: S
  ) -> Res<()> {
    // Define all predicates.
    for & PredDef { ref pred, ref args, ref body } in & self.output.pred_defs {
      solver.define_fun(
        pred, args, & "Bool".to_string(), body, & ()
      ) ?
    }

    let mut okay = true ;
    let mut count = 0 ;

    // Check all clauses one by one.
    for & Clause { ref args, ref lhs, ref rhs } in & self.input.clauses {
      count += 1 ;
      solver.push(1) ? ;

      // Declare arguments.
      for & (ref ident, ref typ) in args {
        solver.declare_const(ident, typ, & ()) ?
      }

      // Build term.
      let term = {
        let mut term = format!("(and (not {})", rhs) ;
        for lhs in lhs {
          term.push(' ') ;
          term.push_str(lhs)
        }
        term.push_str(")") ;
        term
      } ;

      solver.assert(& term, & ()) ? ;

      if solver.check_sat() ? {
        okay = false ;
        let model = solver.get_model() ? ;
        println!("") ;
        println!("(error \"") ;
        println!("  clause {}", count) ;
        print!(  "   ") ;
        for & (ref id, ref ty) in args {
          print!(" ({} {})", id, ty)
        }
        println!("") ;
        println!("    (=>") ;
        println!("      (and") ;
        for lhs in lhs {
          println!("        {}", lhs)
        }
        println!("      ) {}", rhs) ;
        println!("    )") ;
        println!("  is falsifiable with {{") ;
        for (ident, value) in model {
          println!("    {}: {},", ident, value)
        }
        println!("  }}") ;
        println!("\")") ;
        println!("")
      } else {
        info!("clause {} is fine", count)
      }

      solver.pop(1) ?
    }

    if ! okay {
      bail!(
        "predicates do not verify all the clauses of the input file"
      )
    }

    Ok(())
  }
}



/// Checks a `hoice` run.
pub fn do_it(input_file: & str, output_file: & str) -> Res<()> {
  use rsmt2::{ solver, Kid } ;
  let data = Data::of_files(input_file, output_file) ? ;

  let mut kid = Kid::mk( conf.solver_conf() ).chain_err(
    || ErrorKind::Z3SpawnError
  ) ? ;
  {
    let solver = solver(& mut kid, Parser).chain_err(
      || "while constructing the checkers solver"
    ) ? ;
    if let Some(log) = conf.smt_log_file("check") ? {
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













/// Parser for the output of the SMT solver.
///
/// Parses idents and values as strings.
pub struct Parser ;
impl ::rsmt2::ParseSmt2 for Parser {
  type Ident = Ident ;
  type Value = Value ;
  type Expr = () ;
  type Proof = () ;
  type I = () ;

  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], Ident> {
    ::check::parse::s_expr(bytes)
  }

  fn parse_value<'a>(
    & self, bytes: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], Value> {
    ::check::parse::s_expr(bytes)
  }

  fn parse_expr<'a>(
    & self, _: & 'a [u8], _: & ()
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_expr` of the teacher parser should never be called")
  }

  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!("[bug] `parse_proof` of the teacher parser should never be called")
  }
}
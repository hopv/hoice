//! Checks the result of a `hoice` run.
//!
//! This code is completely separated from the rest of the code, on purpose. It
//! basically takes the original [`smt2`][smt2] file, a file containing the
//! output of the [`hoice`][hoice] run, and checks that the result makes sense.
//!
//! It does so using an SMT solver, and performing string substitution
//! (roughly) to rewrite the problem as a pure SMT query. In particular, there
//! is no real notion of term here.
//!
//! [hoice]: https://github.com/hopv/hoice (hoice github repository)
//! [smt]: http://smtlib.cs.uiowa.edu/ (SMT-LIB website)

use crate::{
    common::{conf, ColorExt, HashMap, Instance, Read, Solver},
    errors::*,
};

pub mod parse;

use self::parse::InParser;
use self::smt::*;

/// A predicate is just a string.
pub type Pred = String;
/// A type is just a string.
pub type Typ = String;
/// A signature.
pub type Sig = Vec<Typ>;

/// A function definition.
#[derive(Clone)]
pub struct FunDef {
    /// Name.
    pub name: String,
    /// Arguments.
    pub args: Args,
    /// Return type.
    pub typ: Typ,
    /// Body.
    pub body: Term,
}

/// A predicate declaration.
#[derive(Clone)]
pub struct PredDec {
    /// Predicate.
    pub pred: Pred,
    /// Signature.
    pub sig: Sig,
}

/// An ident is just a string.
pub type Ident = String;
/// A value is a string.
pub type Value = String;
/// A list of arguments.
pub type Args = Vec<(Ident, Typ)>;
/// A term is just a string.
pub type Term = String;

/// A predicate definition.
#[derive(Clone)]
pub struct PredDef {
    /// Predicate.
    pub pred: Pred,
    /// Arguments.
    pub args: Args,
    /// Body.
    pub body: Option<Term>,
}

/// A clause.
#[derive(Clone)]
pub struct Clause {
    /// Arguments.
    pub args: Args,
    /// Body.
    pub body: Term,
}

/// Data from the input file.
pub struct Input {
    /// Unknown stuff.
    pub unknown: Vec<String>,
    /// Predicate declarations.
    pub pred_decs: Vec<PredDec>,
    /// Function definitions.
    pub fun_defs: Vec<FunDef>,
    /// Clauses.
    pub clauses: Vec<Clause>,
}
impl Input {
    /// Loads some input data from a file.
    pub fn of_file<P: AsRef<::std::path::Path>>(file: P) -> Res<Self> {
        use std::fs::OpenOptions;
        let file = file.as_ref();
        log_info! {
          "loading horn clause file {}...", conf.emph(file.to_string_lossy())
        }
        let mut buff = String::new();
        OpenOptions::new()
            .read(true)
            .open(file)
            .chain_err(|| format!("while opening file {}", conf.emph(file.to_string_lossy())))?
            .read_to_string(&mut buff)
            .chain_err(|| format!("while reading file {}", conf.emph(file.to_string_lossy())))?;
        Self::of_str(&buff)
    }
    /// Loads some input data from a string.
    pub fn of_str(data: &str) -> Res<Self> {
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
    pub fn of_file(file: &str) -> Res<Self> {
        use std::fs::OpenOptions;
        log_info! { "loading hoice output file {}...", conf.emph(file) }
        let mut buff = String::new();
        OpenOptions::new()
            .read(true)
            .open(file)
            .chain_err(|| format!("while opening file {}", conf.emph(file)))?
            .read_to_string(&mut buff)
            .chain_err(|| format!("while reading file {}", conf.emph(file)))?;
        Self::of_str(&buff)
    }
    /// Loads some input data from a string.
    pub fn of_str(data: &str) -> Res<Self> {
        InParser::new(data).parse_output()
    }

    /// Checks the signature of the predicates match the declarations of an input
    /// `smt2` file. Also checks that all predicates are defined *once*.
    pub fn check_consistency(&mut self, input: &Input) -> Res<()> {
        log_info! { "checking predicate signature consistency..." }
        let mut map = HashMap::with_capacity(self.pred_defs.len());
        log! { @4 "checking for duplicate definitions" }
        for &PredDef {
            ref pred, ref args, ..
        } in &self.pred_defs
        {
            let prev = map.insert(pred.clone(), args.clone());
            if prev.is_some() {
                error_chain::bail!(
                    "predicate {} is defined twice in hoice's output",
                    conf.emph(pred)
                )
            }
        }
        log! { @4 "checking signatures" }
        for &PredDec { ref pred, ref sig } in &input.pred_decs {
            if let Some(args) = map.get(pred) {
                if sig.len() != args.len() {
                    error_chain::bail!(
                        "arguments of predicate {}'s definition \
                         does not match its signature",
                        conf.emph(pred)
                    )
                }

                let iter = sig.iter().zip(args.iter()).enumerate();
                for (count, (ty_1, &(ref arg, ref ty_2))) in iter {
                    if ty_1 != ty_2 {
                        error_chain::bail!(
                            "type of argument {} ({}) in predicate {}'s definition ({}) \
                             match that of the input file ({})",
                            count,
                            arg,
                            conf.emph(pred),
                            ty_2,
                            ty_1
                        )
                    }
                }
            } else {
                warn!(
                    "predicate {} is not defined in hoice's output",
                    conf.emph(pred)
                );
                let mut args = vec![];

                for (cnt, ty) in sig.iter().enumerate() {
                    args.push((format!("v_{}", cnt), ty.clone()))
                }
                self.pred_defs.push(PredDef {
                    pred: pred.clone(),
                    args,
                    body: None,
                })
            }
        }
        log! { @4 "done" }
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
        output.check_consistency(&input)?;
        Ok(Data { input, output })
    }
    /// Reads two files for input and output data.
    pub fn of_files(input_file: &str, output_file: &str) -> Res<Self> {
        let input = Input::of_file(input_file)?;
        let output = Output::of_file(output_file)?;
        Self::new(input, output)
    }

    /// Checks a single clause.
    pub fn check_clause(
        &self,
        solver: &mut Solver<Parser>,
        Clause { args, body }: &Clause,
        count: usize,
    ) -> Res<Option<bool>> {
        solver.reset()?;

        for unknown in &self.input.unknown {
            use std::io::Write;
            writeln!(solver, "{}", unknown)?
        }

        // Define all functions.
        for &FunDef {
            ref name,
            ref args,
            ref typ,
            ref body,
        } in &self.input.fun_defs
        {
            solver.define_fun(name, args, typ, body)?
        }

        // Define all predicates.
        for &PredDef {
            ref pred,
            ref args,
            ref body,
        } in &self.output.pred_defs
        {
            if let Some(body) = body.as_ref() {
                solver.define_fun(pred, args, &"Bool".to_string(), body)?
            } else {
                solver.declare_fun(
                    pred,
                    &args
                        .iter()
                        .map(|&(_, ref typ)| typ.clone())
                        .collect::<Vec<_>>(),
                    &"Bool".to_string(),
                )?
            }
        }

        // Declare arguments.
        for &(ref ident, ref typ) in args {
            solver.declare_const(ident, typ)?
        }

        solver.assert(&format!("(not {})", body))?;

        let res = solver.check_sat_or_unk()?;

        if let Some(true) = res {
            let exprs: Vec<_> = args.iter().map(|&(ref id, _)| id.clone()).collect();
            let model = solver.get_values(&exprs)?;
            println!();
            println!("({} \"", conf.bad("error"));
            println!("  clause {} is falsifiable with {{", count);
            // print!(  "   ") ;
            // for & (ref id, ref ty) in args {
            //   print!(" ({} {})", id, ty)
            // }
            // println!() ;
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
            println!("  }}");
            println!("\")");
            println!();
            Ok(Some(false))
        } else if let Some(false) = res {
            log_info!("clause {} is fine", count);
            Ok(Some(true))
        } else {
            log_info!("got unknown on clause {}, assuming it's okay", count);
            Ok(None)
        }
    }

    /// Checks the output data works with the input data using an SMT solver.
    pub fn check(&self, solver: &mut Solver<Parser>) -> Res<()> {
        let mut okay = true;
        let mut err = false;

        // Check all clauses one by one.
        for (count, clause) in self.input.clauses.iter().enumerate() {
            match self.check_clause(solver, clause, count) {
                Ok(Some(ok)) => okay = okay && ok,
                Ok(None) => (),
                Err(e) => {
                    err = true;
                    let e = e.chain_err(|| format!("while checking clause {}", count));
                    print_err(&e)
                }
            }
        }

        if !okay {
            error_chain::bail!("predicates do not verify all the clauses of the input file")
        } else if err {
            error_chain::bail!("at least one error while checking the clauses")
        } else {
            Ok(())
        }
    }
}

/// Checks a `hoice` run from two files.
pub fn do_it(input_file: &str, output_file: &str) -> Res<()> {
    let data = Data::of_files(input_file, output_file)?;

    log! { @4 "spawning solver" }

    let mut solver = conf.solver.spawn("check", Parser, &Instance::new())?;

    let res = data.check(&mut solver);
    if res.is_ok() {
        println!("(safe)")
    }

    let end_res = solver.kill().chain_err(|| "While killing solver");

    res.and_then(|_| end_res)
}

/// Checks a `hoice` run, script from a file, model from a string.
///
/// This is currently only used for testing purposes.
pub fn do_it_from_str<P: AsRef<::std::path::Path>>(input_file: P, model: &str) -> Res<()> {
    println!("model:");
    println!("{}", model);
    let data = Data::new(
        Input::of_file(input_file).chain_err(|| "while loading input file")?,
        Output::of_str(model).chain_err(|| "while loading model")?,
    )?;

    let mut solver = conf.solver.spawn("check", Parser, &Instance::new())?;
    let res = data.check(&mut solver);
    let end_res = solver.kill().chain_err(|| "While killing solver");
    res.and_then(|_| end_res)
}

mod smt {
    use rsmt2::parse::{ExprParser, IdentParser, ValueParser};
    use rsmt2::SmtRes;

    use crate::check::{Ident, Term, Value};

    /// Parser for the output of the SMT solver.
    ///
    /// Parses idents and values as strings.
    #[derive(Clone, Copy)]
    pub struct Parser;

    impl<'a> IdentParser<Ident, (), &'a str> for Parser {
        fn parse_ident(self, input: &'a str) -> SmtRes<Ident> {
            Ok(input.into())
        }
        fn parse_type(self, _: &'a str) -> SmtRes<()> {
            Ok(())
        }
    }

    impl<'a> ExprParser<Term, (), &'a str> for Parser {
        fn parse_expr(self, input: &'a str, _: ()) -> SmtRes<Term> {
            Ok(input.into())
        }
    }

    impl<'a> ValueParser<Value, &'a str> for Parser {
        fn parse_value(self, input: &'a str) -> SmtRes<Value> {
            Ok(input.into())
        }
    }
}

//! [Hoice][hoice] is Horn clause solver based on the [ICE][ice] framework. The
//! original approach was modified to handle non-linear Horn clauses and
//! multi-predicates natively.
//!
//! [hoice]: https://github.com/hopv/hoice
//! (hoice repository on github)
//! [ice]: http://madhu.cs.illinois.edu/CAV14ice.pdf
//! (ICE paper PDF)

#![doc(test(attr(deny(warnings))))]

#![allow(non_upper_case_globals)]
#[macro_use]
extern crate lazy_static ;
#[macro_use]
extern crate mylib ;
#[macro_use]
extern crate error_chain ;
#[macro_use]
extern crate clap ;
extern crate ansi_term as ansi ;
extern crate hashconsing ;
extern crate rsmt2 ;
extern crate num ;
extern crate either ;
extern crate rand ;
extern crate isatty ;

pub mod errors ;
#[macro_use]
pub mod common ;
pub mod term ;
pub mod instance ;
pub mod teacher ;
pub mod learning ;
pub mod check ;
pub mod split ;
pub mod unsat_core ;

#[cfg( all(test, not(windows)) )]
mod tests ;

use common::* ;
use instance::Instance ;

/// Parses command-line arguments and works.
pub fn work() -> Res<()> {

  // Reading from file?
  if let Some(file_path) = conf.in_file() {
    use std::fs::{ OpenOptions } ;

    // Are we in check mode?
    if let Some(output_file) = conf.check_file() {
      return ::check::do_it(file_path, output_file)
    }

    // Not in check mode, open file
    let file = OpenOptions::new().read(true).open(file_path).chain_err(
      || format!("while opening input file `{}`", conf.emph(file_path))
    ) ? ;

    read_and_work(file, true, false, false) ? ;
    Ok(())

  } else {
    // Reading from stdin.

    let stdin = ::std::io::stdin() ;

    read_and_work(stdin, false, false, false) ? ;
    Ok(())

  }
}




/// Reads from a `Read`er.
///
/// Arguments:
/// 
/// - `file_input`: indicates whether we're reading from a file. If true, parse
///   errors will mention the line where the error occured.
///
/// - `stop_on_check`: forces the function to return once the first check is
///   complete. Only used in tests.
///
/// - `stop_on_err`: forces to stop at the first error. Only used in tests.
pub fn read_and_work<R: ::std::io::Read>(
  reader: R, file_input: bool, stop_on_check: bool, stop_on_err: bool
) -> Res< (Option<ConjModel>, Instance) > {
  use instance::parse::ItemRead ;

  reset() ;

  let profiler = Profiler::new() ;

  let mut reader = ::std::io::BufReader::new(reader) ;
  // String buffer.
  let buf = & mut String::with_capacity(2000) ;
  // Parser context.
  let mut parser_cxt = ::instance::parse::ParserCxt::new() ;
  // Line offset of the parser.
  let mut line_off = 0 ;
  // Instance.
  let mut instance = Instance::new() ;
  // Current model.
  let mut model = None ;
  // Any error encountered?
  // let mut error = false ;

  // Unsat core.
  //
  // - `None`             if not unsat
  // - `Some(None)`       if unsat but no core
  // - `Some(Some(core))` otherwise
  let mut unsat = None ;

  'parse_work: loop {
    use instance::parse::Parsed ;

    profile!{ |profiler| tick "parsing" }

    buf.clear() ;
    let lines_parsed = reader.read_item(buf).chain_err(
      || "while reading input"
    ) ? ;

    if lines_parsed == 0 && file_input {
      profile!{ |profiler| mark "parsing" }
      break 'parse_work
    }
    let parse_res = parser_cxt.parser(
      & buf, line_off
    ).parse(& mut instance) ;

    line_off += lines_parsed ;

    let parse_res = match parse_res {
      Ok(res) => res,
      Err(e) => {
        if stop_on_err { return Err(e) }
        // error = true ;
        print_err(e) ;
        continue 'parse_work
      },
    } ;

    profile!{ |profiler| mark "parsing" }
    
    match parse_res {

      // Check-sat on unsat instance?
      Parsed::CheckSat if unsat.is_some() => {
        println!("unsat") ;

        if stop_on_check {
          return Ok( (model, instance) )
        }
      },

      // Check-sat, start class.
      Parsed::CheckSat => {

        log! { @info "Running top pre-processing" }

        let preproc_profiler = Profiler::new() ;
        match profile! {
          |profiler| wrap {
            instance::preproc::work(& mut instance, & preproc_profiler)
          } "top preproc"
        } {
          Ok(()) => (),
          Err(e) => if e.is_timeout() {
            if e.is_timeout() {
              println!("unknown") ;
              print_stats("top", profiler) ;
              ::std::process::exit(0)
            }
          } else {
            bail!(e)
          },
        }
        print_stats("top preproc", preproc_profiler) ;

        model = if let Some(maybe_model) = instance.is_trivial_conj() ? {
          // Pre-processing already decided satisfiability.
          log! { @info "solved by pre-processing" }
          if maybe_model.is_some() {
            println!("sat")
          } else {
            println!("unsat") ;
            unimplemented!("unsat core from preproc")
          }
          maybe_model
        } else {

          let arc_instance = Arc::new(instance) ;
          let solve_res = split::work(arc_instance.clone(), & profiler) ;

          while Arc::strong_count(& arc_instance) != 1 {}
          instance = if let Ok(
            instance
          ) = Arc::try_unwrap( arc_instance ) { instance } else {
            bail!("\
              [bug] finalized teacher but there are still \
              strong references to the instance\
            ")
          } ;

          match solve_res {
            Ok(Some(Either::Left(res))) => {
              println!("sat") ;
              Some(
                instance.extend_model(res) ?
              )
            },
            Ok(None) => {
              println!("unknown") ;
              None
            },
            Ok(Some(Either::Right(res))) => {
              unsat = Some(res) ;
              println!("unsat") ;
              None
            }
            Err(ref e) if e.is_unsat() => {
              unsat = Some(None) ;
              println!("unsat") ;
              None
            },
            Err(ref e) if e.is_timeout() => {
              println!("unknown") ;
              print_stats("top", profiler) ;
              ::std::process::exit(0)
            },
            Err(e) => bail!(e),
          }
        } ;

        if stop_on_check {
          return Ok( (model, instance) )
        }

      },

      Parsed::GetUnsatCore |
      Parsed::GetModel if ! conf.infer => (),


      // Print unsat core if available.
      Parsed::GetUnsatCore => match unsat {
        Some(None) | None => println!(
          "({} \"\n  \
            unsat cores are only available {},\n  \
            and if the command {}\n  \
            was issued at the beginning of the script\n\")\
          ", conf.bad("error"), conf.emph("after an unsat result"),
          conf.emph("`(set-option :produce-unsat-cores true)`")
        ),
        Some(Some(ref mut graph)) => graph.write_core(
          & mut stdout(), & instance
        ) ?,
      }


      // Print model if available.
      Parsed::GetModel => if let Some(model) = model.as_mut() {
        // Simplify model before writing it.
        // instance.simplify_pred_defs(model) ? ;
        let stdout = & mut stdout() ;
        instance.write_model(& model, stdout) ?
      } else {
        bail!("no model available")
      },

      Parsed::Items => if conf.print_success() {
        println!("success")
      },

      Parsed::Reset => {
        reset() ;
        parser_cxt.reset() ;
        instance = Instance::new() ;
        model = None
      },

      Parsed::Eof => if stop_on_check {
        bail!("reached <eof> without reading a check-sat...")
      } else {
        ()
      },

      Parsed::Exit => break 'parse_work,
    }
  }

  print_stats("top", profiler) ;

  Ok( (model, instance) )
}


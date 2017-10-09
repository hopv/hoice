#![doc = r#"# TODO

- improve `rsmt2` and make smt learner more efficient and less ad hoc
- remove all the useless error messages in lo-level rsmt2 writers
- investigate problems with trivial clauses of the form `true => false`
"#]

#![allow(non_upper_case_globals)]

#[macro_use]
extern crate lazy_static ;
#[macro_use]
extern crate mylib ;
#[macro_use]
extern crate error_chain ;
#[macro_use]
extern crate log ;
#[macro_use]
extern crate clap ;
extern crate ansi_term as ansi ;
extern crate regex ;
extern crate hashconsing ;
extern crate rsmt2 ;
extern crate num ;
extern crate rayon ;
extern crate either ;

pub mod errors ;
#[macro_use]
pub mod common ;
pub mod term ;
pub mod instance ;
pub mod teacher ;
pub mod learning ;
pub mod check ;

#[cfg(test)]
mod tests ;

use common::* ;
use instance::Instance ;

/// Parses command-line arguments and works.
pub fn work() -> Res<()> {

  // Creates smt log directory if needed.
  conf.init() ? ;

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

    read_and_work(file, true, false) ? ;
    Ok(())

  } else {
    // Reading from stdin.

    let stdin = ::std::io::stdin() ;

    read_and_work(stdin, false, false) ? ;
    Ok(())

  }
}




/// Reads from a [Read][read]er.
///
/// The `file_input` flag indicates whether we're reading from a file. If true,
/// parse errors will mention the line where the error occured.
///
/// The `stop_on_check` flag forces the function to return once the first check
/// is complete. Only used in tests.
///
/// [read]: https://doc.rust-lang.org/std/io/trait.Read.html (Read trait)
pub fn read_and_work<R: ::std::io::Read>(
  reader: R, file_input: bool, stop_on_check: bool,
) -> Res< (Option<Model>, Instance) > {
  use instance::parse::ItemRead ;

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
    ).parse(& mut instance) ? ;

    line_off += lines_parsed ;

    profile!{ |profiler| mark "parsing" }
    
    match parse_res {

      // Check-sat, start class.
      Parsed::CheckSat => {
        if conf.preproc.active {
          instance::preproc::work(& mut instance, & profiler) ?
        }
        instance.finalize() ;

        if ! conf.infer { continue 'parse_work }

        model = if let Some(maybe_model) = instance.is_trivial() ? {
          // Pre-processing already decided satisfiability.
          log_info!(
            "answering satisfiability query by pre-processing only"
          ) ;
          maybe_model
        } else {
          let arc_instance = Arc::new(instance) ;
          let partial_model = teacher::start_class(
            & arc_instance, & profiler
          ) ? ;
          { // Careful with this block, so that the unwrap does not fail
            while Arc::strong_count(& arc_instance) != 1 {}
            instance = if let Ok(
              instance
            ) = Arc::try_unwrap( arc_instance ) { instance } else {
              bail!("\
                [bug] finalized teacher but there are still \
                strong references to the instance\
              ")
            }
          }
          if let Some(partial_model) = partial_model {
            Some( instance.model_of(partial_model) ? )
          } else {
            None
          }
        } ;
        if stop_on_check {
          return Ok( (model, instance) )
        }
        if model.is_some() {
          println!("sat")
        } else {
          println!("unsat")
        }

      },

      Parsed::GetModel if ! conf.infer => (),

      // Print model if available.
      Parsed::GetModel => if let Some(ref model) = model {
        let stdout = & mut ::std::io::stdout() ;
        instance.write_model(model, stdout) ?
      } else {
        bail!("no model available")
      },

      Parsed::Items => (),

      Parsed::Reset => {
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

  print_stats(profiler) ;

  Ok( (model, instance) )
}








/// Prints the stats if asked. Does nothing in bench mode.
#[cfg(feature = "bench")]
fn print_stats(_: Profiler) {}
/// Prints the stats if asked. Does nothing in bench mode.
#[cfg( not(feature = "bench") )]
fn print_stats(profiler: Profiler) {
  if conf.stats {
    println!("") ;
    let (tree, stats) = profiler.extract_tree() ;
    tree.print() ;
    if ! stats.is_empty() {
      println!("; stats:") ;
      stats.print()
    }
    println!("") ;
  }
}
#![doc = r#"
# TODO

- improve `rsmt2` and make smt learner more efficient and less ad hoc
- remove all the useless error messages in lo-level rsmt2 writers
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
#[macro_use]
extern crate nom ;
extern crate hashconsing ;
#[macro_use]
extern crate rsmt2 ;
extern crate num ;
extern crate rayon ;

pub mod errors ;
#[macro_use]
pub mod common ;
pub mod term ;
pub mod instance ;
pub mod teacher ;
pub mod learning ;

pub mod check ;

use common::* ;
use instance::Instance ;

/// Parses command-line arguments and works.
pub fn work() -> Res<()> {

  // Creates smt log directory if needed.
  conf.init() ? ;

  // Reading from file?
  if let Some(file_path) = conf.file.as_ref() {
    use std::fs::{ OpenOptions } ;

    // Are we in check mode?
    if let Some(output_file) = conf.check.as_ref() {
      return ::check::do_it(file_path, output_file)
    }

    // Not in check mode, open file
    let file = OpenOptions::new().read(true).open(file_path).chain_err(
      || format!("while opening input file `{}`", conf.emph(file_path))
    ) ? ;

    read_and_work(file, true)

  } else {
    // Reading from stdin.

    let stdin = ::std::io::stdin() ;

    read_and_work(stdin, false)

  }
}





fn read_and_work<R: ::std::io::Read>(
  reader: R, file_input: bool
) -> Res<()> {
  use instance::parse::ItemRead ;
  
  let profiler = Profiler::mk() ;

  let mut reader = ::std::io::BufReader::new(reader) ;
  // String buffer.
  let buf = & mut String::with_capacity(2000) ;
  // Parser context.
  let mut parser_cxt = ::instance::parse::ParserCxt::mk() ;
  // Line offset of the parser.
  let mut line_off = 0 ;
  // Instance.
  let mut instance = Instance::new(3_000, 42, 42) ;
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

    let parse_res = match parser_cxt.parser(
      & buf, line_off
    ).parse(& mut instance) {
      Ok(res) => res,
      Err(e) => {
        ::errors::print_err(e) ;
        continue 'parse_work
      },
    } ;
    line_off += lines_parsed ;

    profile!{ |profiler| mark "parsing" }
    
    match parse_res {

      // Check-sat, start class.
      Parsed::CheckSat => {

        if conf.pre_proc {
          instance::preproc::work(& mut instance, & profiler) ?
        }
        instance.finalize() ;

        model = if let Some(model) = instance.is_trivial() ? {
          // Pre-processing already decided satisfiability.
          log_info!(
            "answering satisfiability query by pre-processing only"
          ) ;
          Some(model)
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
        if model.is_some() {
          println!("sat")
        } else {
          println!("unsat")
        }

      },

      // Print model if available.
      Parsed::GetModel => if let Some(ref model) = model {
        let stdout = & mut ::std::io::stdout() ;
        println!("(model") ;
        for & (ref pred, ref tterms) in model {
          if ! tterms.is_empty() {
            let pred_info = & instance[* pred] ;
            println!("  (define-fun {}", pred_info.name) ;
            print!(  "    (") ;
            for (var, typ) in pred_info.sig.index_iter() {
              print!(" ({} {})", instance.var(var), typ)
            }
            println!(" ) Bool") ;
            if tterms.len() > 1 {
              print!("    (and\n") ;
              for tterm in tterms {
                print!("      ") ;
                instance.print_tterm_as_model(stdout, tterm) ? ;
                println!("")
              }
              println!("    )")
            } else if tterms.len() == 1 {
              print!("    ") ;
              instance.print_tterm_as_model(stdout, & tterms[0]) ? ;
              println!("")
            } else {
              bail!(
                "model for predicate {} is empty",
                conf.sad( & pred_info.name )
              )
            }
            println!("  )")
          }
        }
        println!(")")
      } else {
        bail!("no model available")
      },

      Parsed::Items => (),

      Parsed::Eof => (),

      Parsed::Exit => break 'parse_work,
    }
  }

  print_stats(profiler) ;

  Ok(())
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
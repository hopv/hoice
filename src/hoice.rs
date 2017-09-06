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
pub mod instance ;
pub mod teacher ;
pub mod learning ;

pub mod check ;

use common::* ;

/// Parses command-line arguments and works.
pub fn work() -> Res<()> {

  // Creates smt log directory if needed.
  conf.init() ? ;

  let profiler = Profile::mk() ;

  if let Some(file_path) = conf.file.as_ref() {
    use std::fs::{ OpenOptions } ;
    use std::io::* ;

    // Are we in check mode?
    if let Some(output_file) = conf.check.as_ref() {
      return ::check::do_it(file_path, output_file)
    }

    profile!{ |profiler| tick "loading" }


    profile!{ |profiler| tick "loading", "reading file" }
    let mut txt = String::with_capacity(2000) ;
    let mut file = OpenOptions::new().read(true).open(file_path).chain_err(
      || format!("while opening input file `{}`", conf.emph(file_path))
    ) ? ;
    let _ = file.read_to_string(& mut txt).chain_err(
      || format!("while reading input file `{}`", conf.emph(file_path))
    ) ? ;
    profile!{ |profiler| mark "loading", "reading file" }

    let mut parser = ::instance::parse::Parser::mk(& txt) ;
    let mut instance = ::instance::Instance::mk(3_000, 42, 42) ;

    profile!{ |profiler| tick "loading", "parsing" }
    let mut parse_res = parser.parse( & mut instance ) ? ;
    profile!{ |profiler| mark "loading", "parsing" }

    log_info!{
      "instance:\n{}\n\n", instance.to_string_info(()) ?
    }

    profile!{ |profiler| tick "loading", "simplify" }
    instance.simplify_clauses() ? ;
    profile!{ |profiler| mark "loading", "simplify" }
    
    log_info!{
      "instance after simplification:\n{}\n\n",
      instance.to_string_info(()) ?
    }

    profile!{ |profiler| tick "loading", "reducing" }
    ::instance::reduction::work(& mut instance, & profiler) ? ;
    profile!{ |profiler| mark "loading", "reducing" }

    log_info!{
      "instance after reduction:\n{}\n\n", instance.to_string_info(()) ?
    }

    instance.finalize() ;

    profile!{ |profiler| mark "loading" }

    let mut model = None ;

    'parse_and_work: loop {

      use instance::parse::Parsed ;
      
      match parse_res {

        // Check-sat, start class.
        Parsed::CheckSat => {
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
          println!(")")
        } else {
          bail!("no model available")
        },

        Parsed::None => break 'parse_and_work,
      }

      parse_res = parser.parse( & mut instance ) ? ;
    }

    print_stats(profiler) ;

    // let qualifiers = ::learning::ice::mining::Qualifiers::mk(& instance) ;

    // for pred in PrdRange::zero_to(
    //   instance.preds().len()
    // ) {
    //   println!("qualifiers for {}", conf.emph(& instance[pred].name) ) ;
    //   for qual in qualifiers.of(pred) {
    //     println!("  {}", qual)
    //   }
    //   println!("")
    // }

    Ok(())

  } else {
    log_info!{ "loading instance from `{}`...", conf.emph("stdin") }
    bail!("parsing from stdin is not implemented")
  }
}


/// Prints the stats if asked. Does nothing in bench mode.
#[cfg(feature = "bench")]
fn print_stats(_: Profile) {}
/// Prints the stats if asked. Does nothing in bench mode.
#[cfg( not(feature = "bench") )]
fn print_stats(profiler: Profile) {
  if conf.stats {
    let (tree, stats) = profiler.extract_tree() ;
    tree.print() ;
    if ! stats.is_empty() {
      println!("; stats:") ;
      stats.print()
    }
    println!("") ;
  }
}
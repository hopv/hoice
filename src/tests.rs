//! Top-level tests on regression scripts in `rsc`.

use std::fs::read_dir ;
use std::fs::OpenOptions ;

use common::* ;
use read_and_work ;

static sat_files_dir: & str = "tests/rsc/sat" ;
static unsat_files_dir: & str = "tests/rsc/unsat" ;

#[test]
fn sat() {
  if let Err(e) = run_sat() {
    println!("Error:") ;
    for e in e.iter() {
      let mut pref = "> " ;
      for line in format!("{}", e).lines() {
        println!("{}{}", pref, line) ;
        pref = "  "
      }
    }
    panic!("failure")
  }
}

#[test]
fn unsat() {
  if let Err(e) = run_unsat() {
    for e in e.iter() {
      println!("Error:") ;
      let mut pref = "> " ;
      for line in format!("{}", e).lines() {
        println!("{}{}", pref, line) ;
        pref = "  "
      }
    }
    panic!("failure")
  }
}

macro_rules! map_err {
  ($e:expr, $msg:expr) => (
    $e.map_err( |e| format!("{}:\n{}", $msg, e) ) ?
  ) ;
  ($e:expr, $($tt:tt)*) => (
    $e.map_err( |e| format!("{}:\n{}", format!($($tt)*), e) ) ?
  ) ;
}

fn run_sat() -> Res<()> {

  let files = map_err!(
    read_dir(sat_files_dir), format!("while reading `{}`", sat_files_dir)
  ) ;

  for entry in files {
    let entry = map_err!(
      entry, "while reading entry"
    ) ;
    let file_name = format!("{}", entry.file_name().to_string_lossy()) ;
    if map_err!(
      entry.file_type(), "while reading entry (file type of `{}`)", file_name
    ).is_file() {
      println!("looking at `{}`", file_name) ;
      let file = OpenOptions::new().read(true).open(entry.path()).chain_err(
        || format!( "while opening file {}", file_name )
      ) ? ;
      let (model, instance) = read_and_work(file, true, true).chain_err(
        || "while reading file and getting model"
      ) ? ;
      if let Some(model) = model {
        let mut buff: Vec<u8> = vec![] ;
        instance.write_model(& model, & mut buff).chain_err(
          || "while writing model"
        ) ? ;
        let buff = map_err!(
          String::from_utf8(buff), "converting model from bytes to utf8"
        ) ;
        ::check::do_it_from_str(entry.path(), & buff).chain_err(
          || "while checking model"
        ) ? ;
        println!("- is okay")
      } else {
        bail!( "got unsat on `{}`, expected sat", file_name )
      }
    }
  }

  Ok(())

}

fn run_unsat() -> Res<()> {

  let files = map_err!(
    read_dir(unsat_files_dir), format!("while reading `{}`", unsat_files_dir)
  ) ;

  for entry in files {
    let entry = map_err!(
      entry, "while reading entry"
    ) ;
    let file_name = format!("{}", entry.file_name().to_string_lossy()) ;
    if map_err!(
      entry.file_type(), "while reading entry (file type of `{}`)", file_name
    ).is_file() {
      println!("looking at `{}`", file_name) ;
      let file = OpenOptions::new().read(true).open(entry.path()).chain_err(
        || format!( "while opening file {}", file_name )
      ) ? ;
      let (model, instance) = read_and_work(file, true, true) ? ;
      if let Some(model) = model {
        println!("sat") ;
        instance.write_model(& model, & mut ::std::io::stdout()) ? ;
        println!("") ;
        bail!( "got sat on `{}`, expected unsat", file_name )
      } else {
        println!("- is okay")
      }
    }
  }

  Ok(())

}
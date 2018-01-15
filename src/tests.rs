//! Top-level tests on regression scripts in `rsc`.

use std::fs::read_dir ;
use std::fs::OpenOptions ;

use common::* ;
use read_and_work ;

static sat_files_dir: & str = "tests/sat" ;
static unsat_files_dir: & str = "tests/unsat" ;
static err_files_dir: & str = "tests/error" ;

fn run<F: Fn() -> Res<()>>(f: F) {
  if let Err(e) = f() {
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
fn sat() { run(run_sat) }

#[test]
fn unsat() { run(run_unsat) }

#[test]
fn err() { run(run_err) }

macro_rules! map_err {
  ($e:expr, $msg:expr) => (
    $e.map_err( |e| format!("{}:\n{}", $msg, e) ) ?
  ) ;
  ($e:expr, $($tt:tt)*) => (
    $e.map_err( |e| format!("{}:\n{}", format!($($tt)*), e) ) ?
  ) ;
}

fn run_err() -> Res<()> {

  let files = map_err!(
    read_dir(err_files_dir), format!("while reading `{}`", err_files_dir)
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
      match read_and_work(file, true, true, true) {
        Err(e) => println!("got {}", e),
        Ok((model, _)) => bail!(
          "expected error, got {}",
          if model.is_some() { "sat" } else { "unsat" }
        ),
      }
    }
  }
  Ok(())
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
      let (model, instance) = read_and_work(file, true, true, true).chain_err(
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
      let (model, instance) = read_and_work(file, true, true, true) ? ;
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
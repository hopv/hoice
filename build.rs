use std::process::Command ;


fn get_revision() -> Option<String> {
  if let Ok(out) = Command::new("git").args(
    & [ "rev-parse", "--verify", "HEAD" ]
  ).output() {
    if out.status.success() {
      return Some(
        String::from_utf8_lossy(& out.stdout).trim().to_string()
      )
    }
  }
  None
}


fn main() {
  use std::fs::OpenOptions ;
  use std::io::Write ;
  let mut file = OpenOptions::new().write(
    true
  ).truncate(true).create(true).open(
    "src/common/revision.rs"
  ).expect("while opening revision file") ;
  let revision = if let Some(rev) = get_revision() {
    format!("Some(\"{}\")", rev)
  } else {
    format!("None")
  } ;
  file.write_fmt(
    format_args!("\
      //! Stores the current revision.\n\
      \n\
      /// The current revision.\n\
      pub const REVISION: Option<& str> = {} ;\n\
    ", revision)
  ).unwrap() ;
  file.flush().unwrap() ;

  ()
}
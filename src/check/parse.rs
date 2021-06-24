//! Parsers used by the checker.

use std::iter::Extend;

use crate::check::*;

/// Parser.
#[derive(Clone)]
pub struct InParser<'a> {
    /// Unknown stuff. Datatype declarations, recursive function definitions and
    /// such.
    pub unknown: Vec<String>,
    /// Predicate definitions.
    pub pred_defs: Vec<PredDef>,
    /// Predicate declarations.
    pub pred_decs: Vec<PredDec>,
    /// Function definitions.
    pub fun_defs: Vec<FunDef>,
    /// Clauses.
    pub clauses: Vec<Clause>,
    /// Characters.
    chars: ::std::str::Chars<'a>,
    /// Buffer storing characters pushed back.
    buf: Vec<char>,
}
impl<'a> InParser<'a> {
    /// Constructor.
    pub fn new(s: &'a str) -> Self {
        InParser {
            unknown: vec![],
            pred_defs: vec![],
            pred_decs: vec![],
            fun_defs: vec![],
            clauses: vec![],
            chars: s.chars(),
            buf: vec![],
        }
    }

    /// Swaps input characters.
    pub fn swap(&mut self, s: &'a str) {
        self.chars = s.chars();
        assert!(self.buf.is_empty())
    }

    /// True if there is a next character.
    fn has_next(&mut self) -> bool {
        if !self.buf.is_empty() {
            true
        } else if let Some(c) = self.next() {
            self.buf.push(c);
            true
        } else {
            false
        }
    }

    /// Next character.
    fn next(&mut self) -> Option<char> {
        if let Some(c) = self.buf.pop() {
            Some(c)
        } else {
            self.chars.next()
        }
    }

    /// Pushes back a character.
    fn txen(&mut self, c: char) {
        self.buf.push(c)
    }

    /// Backtracks some characters.
    fn backtrack<I>(&mut self, mem: impl IntoIterator<IntoIter = I>)
    where
        I: Iterator<Item = char> + DoubleEndedIterator,
    {
        for c in mem.into_iter().rev() {
            self.buf.push(c)
        }
    }

    /// Parses a tag or fails.
    fn tag(&mut self, tag: &str) -> Res<()> {
        if !self.tag_opt(tag) {
            error_chain::bail!("expected tag `{}`", conf.emph(tag))
        } else {
            Ok(())
        }
    }
    /// Tries to parse a tag.
    fn tag_opt(&mut self, tag: &str) -> bool {
        let mut mem = vec![];
        for c in tag.chars() {
            if let Some(next) = self.next() {
                mem.push(next);
                if c != next {
                    self.backtrack(mem);
                    return false;
                }
            } else {
                self.backtrack(mem);
                return false;
            }
        }
        true
    }

    /// Parses a character or fails.
    fn char(&mut self, c: char) -> Res<()> {
        if !self.char_opt(c) {
            error_chain::bail!(
                "expected character `{}`, got `{}`",
                conf.emph(&c.to_string()),
                conf.sad(if let Some(c) = self.next() {
                    format!("{}", c)
                } else {
                    "<eof>".into()
                })
            )
        } else {
            Ok(())
        }
    }
    /// Tries to parse a character.
    fn char_opt(&mut self, c: char) -> bool {
        if let Some(next) = self.next() {
            if next == c {
                true
            } else {
                self.txen(next);
                false
            }
        } else {
            false
        }
    }

    /// Parses everything it can until (and excluding) some character.
    fn not_char(&mut self, c: char) -> String {
        let mut s = String::new();
        while let Some(next) = self.next() {
            if next == c {
                self.txen(next);
                break;
            } else {
                s.push(next)
            }
        }
        s
    }

    /// Parses an sexpression.
    fn sexpr(&mut self) -> Res<Term> {
        if self.tag_opt("true") {
            return Ok("true".into());
        } else if self.tag_opt("false") {
            return Ok("false".into());
        } else if let Some(id) = self.ident_opt()? {
            return Ok(id);
        }
        let mut s = String::new();
        let mut cnt = 0;
        while let Some(next) = self.next() {
            s.push(next);
            if next == '(' {
                cnt += 1;
            } else if next == ')' {
                cnt -= 1;
                if cnt == 0 {
                    break;
                }
            }
        }
        if cnt != 0 {
            error_chain::bail!("found eof while parsing sexpr")
        }
        Ok(s)
    }

    /// Reads whitespaces and comments.
    fn ws_cmt(&mut self) {
        'ws: while let Some(next) = self.next() {
            if !next.is_whitespace() {
                if next == ';' {
                    'cmt: while let Some(next) = self.next() {
                        if next == '\n' {
                            break 'cmt;
                        }
                    }
                } else {
                    self.txen(next);
                    break 'ws;
                }
            }
        }
    }

    /// Unquoted identifier char.
    fn ident_char(c: char) -> bool {
        if c.is_alphanumeric() {
            true
        } else {
            match c {
                '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | ':' | '_' | '-' | '+' | '='
                | '<' | '>' | '.' | '?' | '/' => true,
                _ => false,
            }
        }
    }

    /// Identifier or fails.
    fn ident(&mut self) -> Res<Ident> {
        if let Some(id) = self.ident_opt()? {
            Ok(id)
        } else {
            error_chain::bail!("expected identifier")
        }
    }
    /// Identifier.
    fn ident_opt(&mut self) -> Res<Option<Ident>> {
        if let Some(next) = self.next() {
            let id = if next == '|' {
                let id = self.not_char('|');
                self.char('|')?;
                id
            } else if Self::ident_char(next) && !next.is_numeric() {
                let mut id = String::new();
                id.push(next);
                while let Some(next) = self.next() {
                    if Self::ident_char(next) {
                        id.push(next)
                    } else {
                        self.txen(next);
                        break;
                    }
                }
                id
            } else {
                self.txen(next);
                return Ok(None);
            };
            Ok(Some(format!("|{}|", id)))
        } else {
            Ok(None)
        }
    }

    /// Set-logic.
    fn set_logic(&mut self) -> Res<bool> {
        if !self.tag_opt("set-logic") {
            return Ok(false);
        }
        self.ws_cmt();
        self.tag("HORN")?;
        Ok(true)
    }

    /// Set-info.
    fn set_info(&mut self) -> Res<bool> {
        if !self.tag_opt("set-info") {
            return Ok(false);
        }
        self.ws_cmt();
        self.char(':')?;
        self.ident()?;
        self.ws_cmt();
        if self.char_opt('|') {
            self.not_char('|');
            self.char('|')?
        } else if self.char_opt('"') {
            let _blah = self.not_char('"');
            self.char('"')?
        } else {
            let _blah = self.not_char(')');
        }
        Ok(true)
    }

    /// Set-option.
    fn set_option(&mut self) -> Res<Option<(String, String)>> {
        if !self.tag_opt("set-option") {
            return Ok(None);
        }
        self.ws_cmt();
        self.char(':')?;
        let key = self.ident()?;
        self.ws_cmt();
        let val = if self.char_opt('|') {
            let res = self.not_char('|');
            self.char('|')?;
            res
        } else if self.char_opt('"') {
            let res = self.not_char('"');
            self.char('"')?;
            res
        } else {
            let res = self.not_char(')');
            res.trim().into()
        };
        Ok(Some((key, val)))
    }

    /// Declare-fun.
    fn declare_fun(&mut self) -> Res<bool> {
        if !self.tag_opt("declare-fun") {
            return Ok(false);
        }
        self.ws_cmt();
        let pred = self.ident()?;
        self.ws_cmt();
        self.char('(')?;
        self.ws_cmt();
        let mut sig = vec![];
        while !self.char_opt(')') {
            sig.push(self.sexpr()?);
            self.ws_cmt()
        }
        self.ws_cmt();
        self.tag("Bool")?;

        self.pred_decs.push(PredDec { pred, sig });

        Ok(true)
    }

    /// Arguments.
    fn args(&mut self) -> Res<Args> {
        self.char('(')?;
        self.ws_cmt();
        let mut args = vec![];
        while self.char_opt('(') {
            let id = self.ident()?;
            self.ws_cmt();
            let ty = self.sexpr()?;
            self.ws_cmt();
            self.char(')')?;
            self.ws_cmt();
            args.push((id, ty))
        }
        self.char(')')?;
        Ok(args)
    }

    /// Assert.
    fn assert(&mut self) -> Res<bool> {
        if !self.tag_opt("assert") {
            return Ok(false);
        }
        self.ws_cmt();

        let mut cnt = 0;

        let negated = if self.char_opt('(') {
            if self.tag_opt("not") {
                self.ws_cmt();
                if self.char_opt('(') {
                    cnt += 1;
                }
                true
            } else {
                cnt += 1;
                false
            }
        } else {
            false
        };

        let (args, body) = if self.tag_opt("forall") {
            if negated {
                error_chain::bail!("negated forall in assertion")
            }
            self.ws_cmt();
            let mut args = vec![];
            loop {
                let these_args = self.args().chain_err(|| "while parsing arguments")?;
                args.extend(these_args);
                self.ws_cmt();
                if self.char_opt('(') {
                    self.ws_cmt();
                    if self.tag_opt("forall") {
                        cnt += 1;
                        self.ws_cmt()
                    } else {
                        self.txen('(');
                        break;
                    }
                } else {
                    break;
                }
            }
            self.ws_cmt();
            let body = self.sexpr().chain_err(|| "while parsing body")?;
            (args, body)
        } else if self.tag_opt("exists") {
            self.ws_cmt();
            let args = self.args().chain_err(|| "while parsing arguments")?;
            self.ws_cmt();
            let body = self.sexpr().chain_err(|| "while parsing body")?;
            (args, body)
        } else {
            if cnt > 0 {
                self.backtrack(Some('('));
                cnt -= 1;
            }
            let body = self.sexpr().chain_err(|| "while parsing body")?;
            (Vec::new(), body)
        };
        self.ws_cmt();

        let body = if negated {
            format!("(not {})", body)
        } else {
            body
        };

        while cnt > 0 {
            self.char(')').chain_err(|| "closing qualifier")?;
            self.ws_cmt();
            cnt -= 1
        }
        if negated {
            self.char(')').chain_err(|| "closing negation")?;
        }

        self.clauses.push(Clause { args, body });

        Ok(true)
    }

    /// Parses anything.
    fn parse_unknown(&mut self) -> Res<()> {
        let mut s = "(".to_string();

        let mut count = 1;

        while let Some(char) = self.next() {
            s.push(char);
            match char {
                ')' => count -= 1,
                '(' => count += 1,
                _ => (),
            }
            if count == 0 {
                self.backtrack(vec![')']);
                self.unknown.push(s);
                return Ok(());
            }
        }

        error_chain::bail!("expected closing paren, found <eof>")
    }

    /// Parses an `smt2` file.
    pub fn parse_input(mut self) -> Res<Input> {
        self.ws_cmt();

        while self.char_opt('(') {
            self.ws_cmt();

            if self.set_logic() ?
      || self.set_info() ?
      || self.set_option()?.is_some()
      || self.declare_fun() ?
      // || self.define_fun() ?
      || self.assert() ?
      || self.tag_opt("check-sat")
      || self.tag_opt("get-model")
      || self.tag_opt("exit")
            {
                ()
            } else {
                self.parse_unknown()?
                // print!("> `") ;
                // while let Some(next) = self.next() {
                //   if next != '\n' {
                //     print!("{}", next)
                //   } else {
                //     break
                //   }
                // }
                // println!("`") ;
                // error_chain::bail!("expected item")
            }

            self.ws_cmt();
            self.char(')').chain_err(|| "closing item")?;
            self.ws_cmt()
        }

        if self.has_next() {
            print!("> `");
            while let Some(next) = self.next() {
                if next != '\n' {
                    print!("{}", next)
                } else {
                    break;
                }
            }
            println!("`");
            error_chain::bail!("could not parse the whole input file")
        }

        Ok(Input {
            unknown: self.unknown,
            pred_decs: self.pred_decs,
            fun_defs: self.fun_defs,
            clauses: self.clauses,
        })
    }

    /// Define-fun.
    fn define_pred(&mut self) -> Res<bool> {
        if !self.tag_opt("define-fun") {
            return Ok(false);
        }
        self.ws_cmt();
        let name = self
            .ident()
            .chain_err(|| "while parsing predicate identifier")?;
        self.ws_cmt();
        let args = self.args().chain_err(|| "while parsing arguments")?;
        self.ws_cmt();
        let typ = self.sexpr()?;
        self.ws_cmt();
        let body = self.sexpr().chain_err(|| "while parsing body")?;
        self.ws_cmt();
        if typ == "|Bool|" {
            self.pred_defs.push(PredDef {
                pred: name,
                args,
                body: Some(body),
            })
        } else {
            self.fun_defs.push(FunDef {
                name,
                args,
                typ,
                body,
            })
        }

        Ok(true)
    }

    /// Parses an `smt2` file.
    pub fn parse_output(mut self) -> Res<Output> {
        if conf.check_eld {
            self.ws_cmt();
            self.tag_opt("Warning: ignoring get-model");
        }
        self.ws_cmt();
        if self.tag_opt("sat") {
            self.ws_cmt();
        }

        let error = "expected `(model (define-fun ...))`";

        if !conf.check_eld {
            self.char('(').chain_err(|| error)?;
            self.ws_cmt();
            self.tag("model").chain_err(|| error)?;
            self.ws_cmt()
        }

        while self.char_opt('(') {
            self.ws_cmt();

            if self
                .define_pred()
                .chain_err(|| "while parsing a define-fun")?
            {
                ()
            } else {
                print!("> `");
                while let Some(next) = self.next() {
                    if next != '\n' {
                        print!("{}", next)
                    } else {
                        break;
                    }
                }
                println!("`");
                error_chain::bail!("expected define-fun")
            }

            self.ws_cmt();
            self.char(')').chain_err(|| "closing define-fun")?;
            self.ws_cmt()
        }
        if !conf.check_eld {
            self.char(')').chain_err(|| "closing model")?;
            self.ws_cmt();
        }

        if self.has_next() {
            print!("> `");
            while let Some(next) = self.next() {
                if next != '\n' {
                    print!("{}", next)
                } else {
                    break;
                }
            }
            println!("`");
            error_chain::bail!("could not parse the whole output file")
        }

        Ok(Output {
            pred_defs: self.pred_defs,
        })
    }
}

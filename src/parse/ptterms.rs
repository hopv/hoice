//! Terms built by the parser before constructing the actual terms.

use crate::common::*;

/// Boolean combination of top terms used by the parser.
#[derive(Clone)]
pub enum PTTerms {
    And(Vec<PTTerms>),
    Or(Vec<PTTerms>),
    NTTerm(TTerm),
    TTerm(TTerm),
}
impl PTTerms {
    /// Type of the top terms.
    pub fn typ(&self) -> Typ {
        match *self {
            PTTerms::And(_) | PTTerms::Or(_) | PTTerms::NTTerm(_) => typ::bool(),
            PTTerms::TTerm(ref tterm) => tterm.typ(),
        }
    }

    /// True if the top term is true.
    pub fn is_true(&self) -> bool {
        if let PTTerms::TTerm(ref tterm) = *self {
            tterm.is_true()
        } else {
            false
        }
    }
    /// True if the top term is false.
    pub fn is_false(&self) -> bool {
        if let PTTerms::TTerm(ref tterm) = *self {
            tterm.is_false()
        } else {
            false
        }
    }

    /// The top term true.
    pub fn tru() -> Self {
        PTTerms::TTerm(TTerm::tru())
    }
    /// The top term false.
    pub fn fls() -> Self {
        PTTerms::TTerm(TTerm::fls())
    }

    /// Total substitution over top terms.
    ///
    /// # TODO
    ///
    /// - eliminate recursion
    pub fn subst_total(&self, subst: &VarMap<PTTerms>) -> Res<Self> {
        let res = match self {
            PTTerms::Or(ref kids) => {
                let mut nu_kids = Vec::with_capacity(kids.len());
                for kid in kids {
                    nu_kids.push(kid.subst_total(subst)?)
                }
                PTTerms::or(nu_kids)
            }
            PTTerms::And(ref kids) => {
                let mut nu_kids = Vec::with_capacity(kids.len());
                for kid in kids {
                    nu_kids.push(kid.subst_total(subst)?)
                }
                PTTerms::and(nu_kids)
            }

            PTTerms::NTTerm(ref tterm) => {
                if let Some(term) = tterm.term() {
                    if let Some(var) = term.var_idx() {
                        return Ok(PTTerms::not(subst[var].clone())?);
                    }
                }
                PTTerms::NTTerm(tterm.subst_total(subst)?)
            }

            PTTerms::TTerm(ref tterm) => {
                if let Some(term) = tterm.term() {
                    if let Some(var) = term.var_idx() {
                        return Ok(subst[var].clone());
                    }
                }
                PTTerms::TTerm(tterm.subst_total(subst)?)
            }
        };
        Ok(res)
    }

    pub fn and(mut tterms: Vec<PTTerms>) -> Self {
        debug_assert!(!tterms.is_empty());
        let mut cnt = 0;
        while cnt < tterms.len() {
            if tterms[cnt].is_true() {
                tterms.swap_remove(cnt);
            } else if tterms[cnt].is_false() {
                return PTTerms::fls();
            } else if let PTTerms::And(_) = tterms[cnt] {
                let and = tterms.swap_remove(cnt);
                if let PTTerms::And(tts) = and {
                    tterms.extend(tts)
                } else {
                    unreachable!()
                }
            } else {
                cnt += 1
            }
        }

        match tterms.len() {
            0 => PTTerms::tru(),
            1 => tterms.pop().unwrap(),
            _ => PTTerms::And(tterms),
        }
    }

    pub fn or(mut tterms: Vec<PTTerms>) -> Self {
        debug_assert!(!tterms.is_empty());
        let mut cnt = 0;

        while cnt < tterms.len() {
            if tterms[cnt].is_false() {
                tterms.swap_remove(cnt);
            } else if tterms[cnt].is_true() {
                return PTTerms::tru();
            } else if let PTTerms::Or(_) = tterms[cnt] {
                let or = tterms.swap_remove(cnt);
                if let PTTerms::Or(tts) = or {
                    tterms.extend(tts)
                } else {
                    unreachable!()
                }
            } else {
                cnt += 1
            }
        }

        match tterms.len() {
            0 => PTTerms::fls(),
            1 => tterms.pop().unwrap(),
            _ => PTTerms::Or(tterms),
        }
    }

    pub fn not(mut tterms: PTTerms) -> Res<Self> {
        enum Frame {
            And(Vec<PTTerms>, Vec<PTTerms>),
            Or(Vec<PTTerms>, Vec<PTTerms>),
        }
        let mut stack: Vec<Frame> = vec![];

        'go_down: loop {
            tterms = match tterms {
                PTTerms::And(mut args) => {
                    if let Some(first) = args.pop() {
                        tterms = first;
                        args.reverse();
                        let done = Vec::with_capacity(args.len() + 1);
                        stack.push(Frame::Or(args, done));
                        continue 'go_down;
                    } else {
                        bail!("nullary conjunction")
                    }
                }

                PTTerms::Or(mut args) => {
                    if let Some(first) = args.pop() {
                        tterms = first;
                        args.reverse();
                        let done = Vec::with_capacity(args.len() + 1);
                        stack.push(Frame::And(args, done));
                        continue 'go_down;
                    } else {
                        bail!("nullary disjunction")
                    }
                }

                PTTerms::NTTerm(tt) => PTTerms::TTerm(tt),

                PTTerms::TTerm(tt) => {
                    if tt.is_true() {
                        PTTerms::tterm(TTerm::fls())
                    } else if tt.is_false() {
                        PTTerms::tterm(TTerm::tru())
                    } else {
                        PTTerms::NTTerm(tt)
                    }
                }
            };

            'go_up: loop {
                match stack.pop() {
                    Some(Frame::And(mut to_do, mut done)) => {
                        done.push(tterms);
                        if let Some(tt) = to_do.pop() {
                            stack.push(Frame::And(to_do, done));
                            tterms = tt;
                            continue 'go_down;
                        } else {
                            tterms = Self::and(done);
                            continue 'go_up;
                        }
                    }
                    Some(Frame::Or(mut to_do, mut done)) => {
                        done.push(tterms);
                        if let Some(tt) = to_do.pop() {
                            stack.push(Frame::Or(to_do, done));
                            tterms = tt;
                            continue 'go_down;
                        } else {
                            tterms = Self::or(done);
                            continue 'go_up;
                        }
                    }
                    None => break 'go_down Ok(tterms),
                }
            }
        }
    }

    pub fn tterm(tterm: TTerm) -> Self {
        PTTerms::TTerm(tterm)
    }

    /// True if `PTTerms` does not contain a non-negated predicate.
    pub fn is_legal_lhs(&self) -> bool {
        let mut to_do = Vec::with_capacity(37);
        to_do.push(self);

        while let Some(ptterm) = to_do.pop() {
            match *ptterm {
                PTTerms::And(ref args) => {
                    for arg in args {
                        to_do.push(arg)
                    }
                }
                PTTerms::Or(ref args) => {
                    for arg in args {
                        to_do.push(arg)
                    }
                }
                PTTerms::NTTerm(_) => (),
                PTTerms::TTerm(ref term) => {
                    if term.pred().is_some() {
                        return false;
                    }
                }
            }
        }

        true
    }

    pub fn into_clauses(self) -> Res<Vec<(Vec<TTerm>, TTerm)>> {
        match self {
            PTTerms::TTerm(tterm) => Ok(vec![(vec![], tterm)]),
            PTTerms::NTTerm(tterm) => Ok(vec![(vec![tterm], TTerm::fls())]),

            PTTerms::Or(ptterms) => {
                let mut lhs = Vec::with_capacity(ptterms.len());
                let mut multipliers = Vec::with_capacity(3);
                let mut rhs = None;

                for ptt in ptterms {
                    match ptt {
                        PTTerms::TTerm(tt) => {
                            if let TTerm::T(term) = tt {
                                lhs.push(TTerm::T(term::not(term)))
                            } else if rhs.is_none() {
                                rhs = Some(vec![tt])
                            } else {
                                bail!("ill-formed horn clause (or, 1)")
                            }
                        }

                        PTTerms::NTTerm(tt) => lhs.push(tt),

                        PTTerms::And(ptts) => {
                            let mut tts = Vec::with_capacity(ptts.len());
                            let mut positive_preds = None;
                            for ptt in ptts {
                                match ptt {
                                    PTTerms::NTTerm(tterm) => tts.push(tterm),
                                    PTTerms::TTerm(tterm) => match tterm {
                                        TTerm::T(term) => tts.push(TTerm::T(term::not(term))),
                                        tterm => {
                                            let positive_preds = positive_preds
                                                .get_or_insert_with(|| Vec::with_capacity(7));
                                            positive_preds.push(tterm)
                                        }
                                    },
                                    ptt => {
                                        if let Some(term) = ptt.to_term()? {
                                            tts.push(TTerm::T(term::not(term)))
                                        } else {
                                            bail!("ill-formed horn clause (or, 2)")
                                        }
                                    }
                                }
                            }
                            if let Some(pos_preds) = positive_preds {
                                tts.extend(pos_preds);
                                rhs = Some(tts)
                            } else {
                                multipliers.push(tts)
                            }
                        }

                        _ => bail!("ecountered normalization issue (or, 3)"),
                    }
                }

                let nu_lhs = if multipliers.len() <= 2 {
                    let mut nu_lhs = Vec::with_capacity(multipliers.len() * 2);
                    nu_lhs.push(lhs);
                    let mut tmp_lhs = Vec::with_capacity(nu_lhs.len());
                    for mut vec in multipliers {
                        if let Some(last) = vec.pop() {
                            tmp_lhs.clear();
                            for tterm in vec {
                                for lhs in &nu_lhs {
                                    let mut lhs = lhs.clone();
                                    lhs.push(tterm.clone());
                                    tmp_lhs.push(lhs)
                                }
                            }
                            for mut lhs in nu_lhs.drain(0..) {
                                lhs.push(last.clone());
                                tmp_lhs.push(lhs)
                            }
                            ::std::mem::swap(&mut nu_lhs, &mut tmp_lhs)
                        }
                    }

                    nu_lhs
                } else {
                    for disj in multipliers {
                        let mut nu_disj = Vec::with_capacity(disj.len());
                        for tterm in disj {
                            if let TTerm::T(term) = tterm {
                                nu_disj.push(term)
                            } else {
                                bail!("error during clause conversion")
                            }
                        }
                        lhs.push(TTerm::T(term::or(nu_disj)))
                    }
                    vec![lhs]
                };

                if let Some(rhs) = rhs {
                    let mut res = Vec::with_capacity(rhs.len());
                    let mut rhs = rhs.into_iter();
                    if let Some(last) = rhs.next() {
                        for rhs in rhs {
                            for lhs in &nu_lhs {
                                res.push((lhs.clone(), rhs.clone()))
                            }
                        }
                        for lhs in nu_lhs {
                            res.push((lhs, last.clone()))
                        }
                    }
                    Ok(res)
                } else {
                    Ok(nu_lhs.into_iter().map(|lhs| (lhs, TTerm::fls())).collect())
                }
            }

            PTTerms::And(ppterms) => {
                let mut clauses = Vec::with_capacity(ppterms.len());
                for ppt in ppterms {
                    clauses.extend(ppt.into_clauses()?)
                    //              ^^^^^^^^^^^^^^^^
                    // This is a recursive call, but there can be no other rec call
                    // inside it because
                    //
                    // - there can be no `PTTerms::And` inside a `PTTerms::And` by
                    //   construction
                    // - this is the only place `into_clauses` calls itself.
                }
                Ok(clauses)
            }
        }
    }

    /// Transforms a parser's combination of top terms into a term, if possible.
    pub fn to_term(&self) -> Res<Option<Term>> {
        let mut stack = Vec::with_capacity(17);

        let mut ptterm = self;

        'go_down: loop {
            let mut term = match *ptterm {
                PTTerms::And(ref args) => {
                    let mut args = args.iter();
                    if let Some(head) = args.next() {
                        stack.push((Op::And, args, vec![]));
                        ptterm = head;
                        continue 'go_down;
                    } else {
                        bail!("illegal nullary conjunction")
                    }
                }
                PTTerms::Or(ref args) => {
                    let mut args = args.iter();
                    if let Some(head) = args.next() {
                        stack.push((Op::Or, args, vec![]));
                        ptterm = head;
                        continue 'go_down;
                    } else {
                        bail!("illegal nullary conjunction")
                    }
                }
                PTTerms::TTerm(ref tterm) => {
                    if let Some(term) = tterm.term() {
                        term.clone()
                    } else {
                        return Ok(None);
                    }
                }
                PTTerms::NTTerm(ref tterm) => {
                    if let Some(term) = tterm.term() {
                        term::not(term.clone())
                    } else {
                        return Ok(None);
                    }
                }
            };

            'go_up: loop {
                if let Some((op, mut to_do, mut done)) = stack.pop() {
                    done.push(term);
                    if let Some(next) = to_do.next() {
                        stack.push((op, to_do, done));
                        ptterm = next;
                        continue 'go_down;
                    } else {
                        term = term::app(op, done);
                        continue 'go_up;
                    }
                } else {
                    break 'go_down Ok(Some(term));
                }
            }
        }
    }

    pub fn print(&self, pref: &str) {
        match *self {
            PTTerms::And(ref args) => {
                println!("{}(and", pref);
                for arg in args {
                    arg.print(&format!("{}  ", pref))
                }
                println!("{})", pref)
            }
            PTTerms::Or(ref args) => {
                println!("{}(or", pref);
                for arg in args {
                    arg.print(&format!("{}  ", pref))
                }
                println!("{})", pref)
            }
            PTTerms::NTTerm(ref arg) => println!("{}(not {})", pref, arg),
            PTTerms::TTerm(ref tt) => println!("{}{}", pref, tt),
        }
    }
}

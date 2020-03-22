#![allow(unused_imports)]
use crate::context::{Context, LlTable, Nonterm, Production, Symbol, Term};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

/// Generate the parser code.
pub fn codegen(ctx: &mut Context) {
    info!("Generating code");
    let root = ctx.root_nonterms.clone();
    let mut cg = Codegen::new(ctx);
    for nt in root {
        debug!("Triggering root {}", nt);
        cg.schedule(nt);
    }
    cg.generate();
}

struct Codegen<'a, 'b> {
    ctx: &'b mut Context<'a>,
    nonterm_seen: HashSet<Nonterm<'a>>,
    nonterm_todo: VecDeque<Nonterm<'a>>,
    nonterm_code: BTreeMap<Nonterm<'a>, Code<'a>>,
}

impl<'a, 'b> Codegen<'a, 'b> {
    pub fn new(ctx: &'b mut Context<'a>) -> Self {
        Codegen {
            ctx,
            nonterm_seen: Default::default(),
            nonterm_todo: Default::default(),
            nonterm_code: Default::default(),
        }
    }

    pub fn schedule(&mut self, nt: Nonterm<'a>) {
        if self.nonterm_seen.insert(nt) {
            self.nonterm_todo.push_back(nt);
        }
    }

    pub fn generate(&mut self) {
        while let Some(nt) = self.nonterm_todo.pop_front() {
            let code = self.emit_callable(nt);
            self.nonterm_code.insert(nt, code);
        }
    }

    fn emit_callable(&mut self, nt: Nonterm<'a>) -> Code<'a> {
        // trace!("Generating {}", nt);

        // Analyze the discriminant.
        let mut prods = BTreeMap::<&'a Production<'a>, BTreeSet<Term<'a>>>::new();
        let mut ambig = BTreeMap::<&'a BTreeSet<&'a Production<'a>>, BTreeSet<Term<'a>>>::new();
        let mut epsilon_terms = BTreeSet::<Term<'a>>::new();
        // let mut has_epsilon = false;
        for (&t, ps) in &self.ctx.ll_table[&nt] {
            for p in ps {
                prods.entry(p).or_default().insert(t);
                if p.is_epsilon {
                    epsilon_terms.insert(t);
                }
            }
            if ps.len() > 1 {
                ambig.entry(ps).or_default().insert(t);
            }
        }

        // Generate trivial code if possible.
        if prods.len() == 1 {
            return self.emit_production(prods.keys().nth(0).unwrap());
        }

        // Handle ambiguous code.
        if !ambig.is_empty() {
            trace!("Ambiguity in {}:", nt);
            for (&ts, ps) in &ambig {
                for t in ts {
                    trace!("  {}", t);
                }
                trace!("  = {:?}", ps);
            }
            return Code::Error;
        }

        // Generate a simple match code.
        let mut cases = vec![];
        for (p, ts) in prods {
            let code = self.emit_production(p);
            cases.push((ts, Box::new(code)));
        }
        let code = Code::Match {
            cases,
            expect: vec![nt].into_iter().collect(),
        };
        code
    }

    fn emit_production(&mut self, p: &'a Production<'a>) -> Code<'a> {
        let mut actions = vec![];
        for &sym in &p.syms {
            actions.push(self.emit_symbol(sym));
        }
        Code::Actions(actions)
    }

    fn emit_symbol(&mut self, sym: Symbol<'a>) -> Code<'a> {
        match sym {
            Symbol::Error => Code::Error,
            Symbol::Epsilon => Code::Nil,
            Symbol::This => unreachable!(),
            Symbol::Term(t) => Code::Require(t),
            Symbol::Nonterm(nt) => {
                self.schedule(nt);
                Code::CallNonterm(nt)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Code<'a> {
    Error,
    Nil,
    Require(Term<'a>),
    CallNonterm(Nonterm<'a>),
    Actions(Vec<Code<'a>>),
    Match {
        cases: Vec<(BTreeSet<Term<'a>>, Box<Code<'a>>)>,
        expect: BTreeSet<Nonterm<'a>>,
    },
}

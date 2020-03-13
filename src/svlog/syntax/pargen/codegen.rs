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
}

impl<'a, 'b> Codegen<'a, 'b> {
    pub fn new(ctx: &'b mut Context<'a>) -> Self {
        Codegen {
            ctx,
            nonterm_seen: Default::default(),
            nonterm_todo: Default::default(),
        }
    }

    pub fn schedule(&mut self, nt: Nonterm<'a>) {
        if self.nonterm_seen.insert(nt) {
            self.nonterm_todo.push_back(nt);
        }
    }

    pub fn generate(&mut self) {
        while let Some(nt) = self.nonterm_todo.pop_front() {
            self.emit_callable(nt);
        }
    }

    fn emit_callable(&mut self, nt: Nonterm<'a>) {
        trace!("Generating {}", nt);

        // Analyze the discriminant.
        let mut prods = BTreeMap::<&'a Production<'a>, BTreeSet<Term<'a>>>::new();
        let mut ambig = BTreeMap::<Term<'a>, &'a BTreeSet<&'a Production<'a>>>::new();
        let mut epsilon_terms = BTreeSet::<Term<'a>>::new();
        let mut has_epsilon = false;
        for (&t, ps) in &self.ctx.ll_table[&nt] {
            for p in ps {
                prods.entry(p).or_default().insert(t);
                if p.is_epsilon {
                    epsilon_terms.insert(t);
                }
            }
            if ps.len() > 1 {
                ambig.insert(t, ps);
            }
        }

        // Generate trivial code if possible.
        if prods.len() == 1 {
            self.emit_callable_trivial(nt, prods.keys().nth(0).unwrap());
            return;
        }

        // Handle ambiguous code.
        if !ambig.is_empty() {
            trace!("  Ambiguous: {:?}", ambig);
            return;
        }

        // Generate a simple match code.
        let mut cases = vec![];
        for (p, ts) in prods {
            let actions = self.emit_production(p);
            cases.push((ts, Box::new(Code::Actions(actions))));
        }
        let code = Code::Match {
            cases,
            expect: vec![nt].into_iter().collect(),
        };
    }

    fn emit_callable_trivial(&mut self, nt: Nonterm<'a>, p: &'a Production<'a>) {
        trace!("Generating trivial {}", nt);
        let actions = self.emit_production(p);
        trace!("{:?}", actions);
    }

    fn emit_production(&mut self, p: &'a Production<'a>) -> Vec<Code<'a>> {
        let mut actions = vec![];
        for &sym in &p.syms {
            actions.push(self.emit_symbol(sym));
        }
        actions
    }

    fn emit_symbol(&mut self, sym: Symbol<'a>) -> Code<'a> {
        match sym {
            Symbol::Error => Code::Error,
            Symbol::Epsilon => Code::Nil,
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

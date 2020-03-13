use itertools::Itertools;
use std::collections::{BTreeMap, HashMap};
use typed_arena::Arena;

pub struct Context<'a> {
    arena: &'a ContextArena<'a>,
    pub next_term: usize,
    pub next_nonterm: usize,
    term_lookup: HashMap<&'a str, Term<'a>>,
    nonterm_lookup: HashMap<&'a str, Nonterm<'a>>,
    sym_lookup: HashMap<&'a str, Symbol<'a>>,
    pub prods: BTreeMap<Nonterm<'a>, Vec<&'a Production<'a>>>,
}

impl<'a> Context<'a> {
    pub fn new(arena: &'a ContextArena<'a>) -> Self {
        Context {
            arena,
            next_term: 0,
            next_nonterm: 0,
            term_lookup: Default::default(),
            nonterm_lookup: Default::default(),
            sym_lookup: Default::default(),
            prods: Default::default(),
        }
    }

    /// Allocate a terminal.
    pub fn intern_term(&mut self, name: &str) -> Term<'a> {
        if let Some(&t) = self.term_lookup.get(name) {
            t
        } else {
            let interned_name = self.arena.term_arena.alloc_str(name);
            let v = Term(interned_name, self.next_term);
            self.next_term += 1;
            self.term_lookup.insert(interned_name, v);
            self.sym_lookup.insert(interned_name, v.into());
            v
        }
    }

    /// Allocate a nonterminal.
    pub fn intern_nonterm(&mut self, name: &str) -> Nonterm<'a> {
        if let Some(&t) = self.nonterm_lookup.get(name) {
            t
        } else {
            let interned_name = self.arena.nonterm_arena.alloc_str(name);
            let v = Nonterm(NontermName::Name(interned_name), self.next_nonterm);
            self.next_nonterm += 1;
            self.nonterm_lookup.insert(interned_name, v);
            self.sym_lookup.insert(interned_name, v.into());
            v
        }
    }

    /// Create a new anonymous nonterminal.
    pub fn anonymous_nonterm(&mut self) -> Nonterm<'a> {
        let v = Nonterm(NontermName::Anonymous, self.next_nonterm);
        self.next_nonterm += 1;
        v
    }

    /// Try to find an already-interned symbol.
    pub fn lookup_symbol(&self, name: &str) -> Option<Symbol<'a>> {
        self.sym_lookup.get(name).cloned()
    }

    /// Add a production.
    pub fn add_production(&mut self, nt: Nonterm<'a>, syms: Vec<Symbol<'a>>) -> &'a Production<'a> {
        let prod = self.arena.prod_arena.alloc(Production { nt, syms });
        trace!("Added production {}", prod);
        self.prods.entry(nt).or_default().push(prod);
        prod
    }
}

#[derive(Default)]
pub struct ContextArena<'a> {
    term_arena: Arena<u8>,
    nonterm_arena: Arena<u8>,
    prod_arena: Arena<Production<'a>>,
    _dummy: std::marker::PhantomData<&'a ()>,
}

/// A terminal.
#[derive(Copy, Clone, Eq, Ord)]
pub struct Term<'a>(&'a str, usize);

impl std::fmt::Display for Term<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialEq for Term<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

impl PartialOrd for Term<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(&self.1, &other.1)
    }
}

impl std::hash::Hash for Term<'_> {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        std::hash::Hash::hash(&self.1, hasher)
    }
}

/// A nonterminal.
#[derive(Copy, Clone, Eq, Ord)]
pub struct Nonterm<'a>(NontermName<'a>, usize);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum NontermName<'a> {
    Name(&'a str),
    Anonymous,
}

impl std::fmt::Display for Nonterm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0 {
            NontermName::Name(name) => write!(f, "{}", name),
            NontermName::Anonymous => write!(f, "n{}", self.1),
        }
    }
}

impl PartialEq for Nonterm<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

impl PartialOrd for Nonterm<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(&self.1, &other.1)
    }
}

impl std::hash::Hash for Nonterm<'_> {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        std::hash::Hash::hash(&self.1, hasher)
    }
}

/// A symbol in a production.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Symbol<'a> {
    Error,
    Epsilon,
    Term(Term<'a>),
    Nonterm(Nonterm<'a>),
}

impl<'a> From<Term<'a>> for Symbol<'a> {
    fn from(x: Term<'a>) -> Self {
        Symbol::Term(x)
    }
}

impl<'a> From<Nonterm<'a>> for Symbol<'a> {
    fn from(x: Nonterm<'a>) -> Self {
        Symbol::Nonterm(x)
    }
}

impl std::fmt::Display for Symbol<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            Symbol::Error => write!(f, "?"),
            Symbol::Epsilon => write!(f, "ε"),
            Symbol::Term(x) => write!(f, "{}", x),
            Symbol::Nonterm(x) => write!(f, "{}", x),
        }
    }
}

/// A production in the grammar.
pub struct Production<'a> {
    pub nt: Nonterm<'a>,
    pub syms: Vec<Symbol<'a>>,
}

impl std::fmt::Display for Production<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} -> {}", self.nt, self.syms.iter().format(" "))
    }
}

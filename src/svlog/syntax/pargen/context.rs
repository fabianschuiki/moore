use itertools::Itertools;
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap},
};
use typed_arena::Arena;

pub struct Context<'a> {
    arena: &'a ContextArena<'a>,
    terms: Vec<Term<'a>>,
    nonterms: Vec<Nonterm<'a>>,
    term_lookup: HashMap<&'a str, Term<'a>>,
    nonterm_lookup: HashMap<&'a str, Nonterm<'a>>,
    sym_lookup: HashMap<&'a str, Symbol<'a>>,
    pub prods: BTreeMap<Nonterm<'a>, Vec<&'a Production<'a>>>,
    pub root_nonterms: BTreeSet<Nonterm<'a>>,
    pub ll_table: LlTable<'a>,

    // Caches
    production_epsilon_cache: RefCell<HashMap<Nonterm<'a>, bool>>,
    symbols_epsilon_cache: RefCell<HashMap<Vec<Symbol<'a>>, bool>>,
}

impl<'a> Context<'a> {
    pub fn new(arena: &'a ContextArena<'a>) -> Self {
        Context {
            arena,
            terms: Default::default(),
            nonterms: Default::default(),
            term_lookup: Default::default(),
            nonterm_lookup: Default::default(),
            sym_lookup: Default::default(),
            prods: Default::default(),
            root_nonterms: Default::default(),
            ll_table: Default::default(),
            production_epsilon_cache: Default::default(),
            symbols_epsilon_cache: Default::default(),
        }
    }

    /// Allocate a terminal.
    pub fn intern_term(&mut self, name: &str) -> Term<'a> {
        if let Some(&t) = self.term_lookup.get(name) {
            t
        } else {
            let interned_name = self.arena.term_arena.alloc_str(name);
            let v = Term(interned_name, self.terms.len());
            self.terms.push(v);
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
            let v = Nonterm(NontermName::Name(interned_name), self.nonterms.len());
            self.nonterms.push(v);
            self.nonterm_lookup.insert(interned_name, v);
            self.sym_lookup.insert(interned_name, v.into());
            v
        }
    }

    /// Create a new anonymous nonterminal.
    pub fn anonymous_nonterm(&mut self) -> Nonterm<'a> {
        let v = Nonterm(NontermName::Anonymous, self.nonterms.len());
        self.nonterms.push(v);
        v
    }

    /// Obtain an iterator over all terminals.
    pub fn terms(&self) -> impl Iterator<Item = Term<'a>> + '_ {
        self.terms.iter().cloned()
    }

    /// Obtain an iterator over all nonterminals.
    pub fn nonterms(&self) -> impl Iterator<Item = Nonterm<'a>> + '_ {
        self.nonterms.iter().cloned()
    }

    /// Try to find an already-interned symbol.
    pub fn lookup_symbol(&self, name: &str) -> Option<Symbol<'a>> {
        self.sym_lookup.get(name).cloned()
    }

    /// Add a production.
    pub fn add_production(&mut self, nt: Nonterm<'a>, syms: Vec<Symbol<'a>>) -> &'a Production<'a> {
        let is_epsilon = syms.is_empty() || syms.iter().all(|&s| s == Symbol::Epsilon);
        let prod = self.arena.prod_arena.alloc(Production {
            nt,
            syms,
            is_epsilon,
        });
        trace!("Added production {}", prod);
        self.prods.entry(nt).or_default().push(prod);
        prod
    }

    /// Check if a nontermnial can expand to epsilon.
    pub fn production_expands_to_epsilon(&self, nt: Nonterm<'a>) -> bool {
        if let Some(&e) = self.production_epsilon_cache.borrow().get(&nt) {
            return e;
        }
        let mut epsilon = self.prods[&nt].iter().any(|p| p.is_epsilon);
        self.production_epsilon_cache
            .borrow_mut()
            .insert(nt, epsilon);
        if !epsilon {
            epsilon = self.prods[&nt]
                .iter()
                .any(|p| self.symbols_expand_to_epsilon(&p.syms));
        }
        self.production_epsilon_cache
            .borrow_mut()
            .insert(nt, epsilon);
        if epsilon {
            trace!("May expand to epsilon: {}", nt);
        }
        epsilon
    }

    /// Check if a sequence of symbols can expand to epsilon.
    pub fn symbols_expand_to_epsilon(&self, syms: &[Symbol<'a>]) -> bool {
        if let Some(&b) = self.symbols_epsilon_cache.borrow().get(syms) {
            return b;
        }
        let mut epsilon = true;
        let mut iter = syms.iter();
        while let Some(&sym) = iter.next() {
            match sym {
                Symbol::Error => break,
                Symbol::Epsilon => {
                    break;
                }
                Symbol::Term(_) => {
                    epsilon = false;
                    break;
                }
                Symbol::Nonterm(nt) => {
                    if !self.production_expands_to_epsilon(nt) {
                        epsilon = false;
                        break;
                    }
                }
            }
        }
        self.symbols_epsilon_cache
            .borrow_mut()
            .insert(syms.to_vec(), epsilon);
        epsilon
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

impl std::fmt::Debug for Term<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
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

impl std::fmt::Debug for Nonterm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
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

impl std::fmt::Debug for Symbol<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// A production in the grammar.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Production<'a> {
    pub nt: Nonterm<'a>,
    pub syms: Vec<Symbol<'a>>,
    pub is_epsilon: bool,
}

impl std::fmt::Display for Production<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} -> {}", self.nt, self.syms.iter().format(" "))
    }
}

/// A LL(1) parse table.
pub type LlTable<'a> = BTreeMap<Nonterm<'a>, BTreeMap<Term<'a>, BTreeSet<&'a Production<'a>>>>;

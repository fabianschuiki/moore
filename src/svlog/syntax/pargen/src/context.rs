use itertools::Itertools;
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    rc::Rc,
};
use typed_arena::Arena;

pub struct Context<'a> {
    arena: &'a ContextArena<'a>,
    terms: Vec<Term<'a>>,
    nonterms: Vec<Nonterm<'a>>,
    term_lookup: HashMap<&'a str, Term<'a>>,
    nonterm_lookup: HashMap<&'a str, Nonterm<'a>>,
    sym_lookup: HashMap<&'a str, Symbol<'a>>,
    pub prods: BTreeMap<Nonterm<'a>, BTreeSet<&'a Production<'a>>>,
    pub root_nonterms: BTreeSet<Nonterm<'a>>,
    pub ll_table: LlTable<'a>,

    // Caches
    production_epsilon_cache: RefCell<HashMap<Nonterm<'a>, bool>>,
    symbols_epsilon_cache: RefCell<HashMap<Vec<Symbol<'a>>, bool>>,
    follow_set_cache: RefCell<Option<Rc<FollowSets<'a>>>>,
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
            follow_set_cache: Default::default(),
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
    // #[deprecated]
    pub fn add_production(
        &mut self,
        nt: Nonterm<'a>,
        mut syms: Vec<Symbol<'a>>,
    ) -> &'a Production<'a> {
        let is_epsilon = syms.is_empty();
        for sym in &mut syms {
            if *sym == Symbol::This {
                *sym = Symbol::Nonterm(nt)
            }
        }
        let prod = self.arena.prod_arena.alloc(Production {
            nt,
            syms,
            is_epsilon,
        });
        // trace!("Added production {}", prod);
        self.prods.entry(nt).or_default().insert(prod);
        self.production_epsilon_cache.borrow_mut().clear();
        self.symbols_epsilon_cache.borrow_mut().clear();
        self.follow_set_cache.replace(None);
        prod
    }

    /// Add an anonymous set of productions.
    pub fn anonymous_productions(&mut self, prods: Vec<Vec<Symbol<'a>>>) -> Nonterm<'a> {
        let nt = self.anonymous_nonterm();
        self.set_productions(nt, prods);
        nt
    }

    /// Set the productions for a nonterminal.
    ///
    /// Returns the actual nonterminal that was used. In case the productions
    /// align with an existing nonterminal, that nonterminal will be returned.
    pub fn set_productions(
        &mut self,
        nt: Nonterm<'a>,
        prods: Vec<Vec<Symbol<'a>>>,
    ) -> (Nonterm<'a>, &BTreeSet<&'a Production<'a>>) {
        let mut out = BTreeSet::<&Production>::new();
        for mut syms in prods {
            let is_epsilon = syms.is_empty();
            for sym in &mut syms {
                if *sym == Symbol::This {
                    *sym = Symbol::Nonterm(nt)
                }
            }
            let prod = self.arena.prod_arena.alloc(Production {
                nt,
                syms,
                is_epsilon,
            });
            out.insert(prod);
        }
        self.prods.insert(nt, out);
        self.production_epsilon_cache.borrow_mut().clear();
        self.symbols_epsilon_cache.borrow_mut().clear();
        self.follow_set_cache.replace(None);
        (nt, &self.prods[&nt])
    }

    /// Remove a production.
    pub fn remove_production(&mut self, prod: &Production<'a>) {
        // trace!("Removed production {}", prod);
        self.prods.entry(prod.nt).or_default().remove(prod);
        self.production_epsilon_cache.borrow_mut().clear();
        self.symbols_epsilon_cache.borrow_mut().clear();
        self.follow_set_cache.replace(None);
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
        // if epsilon {
        //     trace!("May expand to epsilon: {}", nt);
        // }
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
                Symbol::This => break,
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

    /// Collect the set of starting symbols that can be derived from a slice of
    /// symbols.
    pub fn first_set_of_symbols(&self, syms: &[Symbol<'a>]) -> BTreeSet<Term<'a>> {
        let mut into = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut todo = VecDeque::new();
        seen.insert(syms);
        todo.push_back(syms);

        while let Some(syms) = todo.pop_front() {
            let mut iter = syms.iter();
            while let Some(&sym) = iter.next() {
                match sym {
                    Symbol::This => unreachable!(),
                    Symbol::Term(t) => {
                        into.insert(t);
                        break;
                    }
                    Symbol::Nonterm(nt) => {
                        for p in &self.prods[&nt] {
                            if seen.insert(&p.syms) {
                                todo.push_back(&p.syms);
                            }
                        }
                        if !self.production_expands_to_epsilon(nt) {
                            break;
                        }
                    }
                }
            }
        }

        into
    }

    /// Collect the set of starting symbols that can be derived from a NT.
    pub fn first_set_of_nonterm(&self, nt: Nonterm<'a>) -> BTreeSet<Term<'a>> {
        let mut into = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut todo = VecDeque::new();
        seen.insert(nt);
        todo.push_back(nt);

        while let Some(nt) = todo.pop_front() {
            for p in &self.prods[&nt] {
                let mut iter = p.syms.iter();
                while let Some(&sym) = iter.next() {
                    match sym {
                        Symbol::This => unreachable!(),
                        Symbol::Term(t) => {
                            into.insert(t);
                            break;
                        }
                        Symbol::Nonterm(nt) => {
                            if seen.insert(nt) {
                                todo.push_back(nt);
                            }
                            if !self.production_expands_to_epsilon(nt) {
                                break;
                            }
                        }
                    }
                }
            }
        }

        into
    }

    /// Get the follow set of a nonterminal.
    pub fn follow_set(&self, nt: Nonterm<'a>) -> BTreeSet<Term<'a>> {
        let fs = self.follow_sets();
        fs[&nt].clone()
    }

    /// Get the follow sets of the entire grammar.
    pub fn follow_sets(&self) -> Rc<FollowSets<'a>> {
        if let Some(fs) = self.follow_set_cache.borrow().as_ref() {
            return fs.clone();
        }
        let fs = Rc::new(compute_follow_sets(&self));
        self.follow_set_cache.replace(Some(fs.clone()));
        fs
    }

    // Minimize the grammar by removing redundant rules where possible.
    pub fn minimize(&mut self) {
        debug!("Minimizing grammar");
        let mut removed = HashSet::new();
        let mut lookup = HashMap::<Vec<Vec<Symbol>>, Nonterm>::new();
        let mut deps = HashMap::<Nonterm, HashSet<Nonterm>>::new();
        let mut repls = HashMap::<Symbol, Symbol>::new();
        let mut todo_vec: VecDeque<_> = self.prods.keys().cloned().collect();
        let mut todo_set: HashSet<_> = self.prods.keys().cloned().collect();
        while let Some(nt) = todo_vec.pop_front() {
            todo_set.remove(&nt);

            // Build the lookup key for this nonterm.
            let mut outdated_prods = HashSet::new();
            let mut nt_deps = HashSet::new();
            let key: Vec<Vec<_>> = self.prods[&nt]
                .iter()
                .map(|&p| {
                    p.syms
                        .iter()
                        .cloned()
                        .map(|sym| if sym == nt.into() { Symbol::This } else { sym })
                        .map(|sym| match repls.get(&sym).cloned() {
                            Some(sym) => {
                                outdated_prods.insert(p);
                                sym
                            }
                            None => sym,
                        })
                        .inspect(|&sym| match sym {
                            Symbol::Nonterm(sym_nt) => {
                                nt_deps.insert(sym_nt);
                            }
                            _ => (),
                        })
                        .collect()
                })
                .collect();

            // Update dependencies.
            deps.insert(nt, nt_deps);

            // Update productions with outdated nonterminals.
            for p in outdated_prods {
                trace!("Update {}", p);
                let new_syms = p
                    .syms
                    .iter()
                    .cloned()
                    .map(|sym| repls.get(&sym).cloned().unwrap_or(sym))
                    .collect();
                self.remove_production(p);
                let p = self.add_production(nt, new_syms);
                trace!("    to {}", p);
            }
            // trace!("Key for {} is {:?}", nt, key);

            // See if there is already a matching nonterminal.
            if let Some(&other_nt) = lookup.get(&key) {
                if nt.is_anonymous() {
                    if nt != other_nt {
                        debug!("Replacing {} with {}", nt, other_nt);
                        repls.insert(nt.into(), other_nt.into());
                        for &dep_nt in deps.get(&nt).into_iter().flatten() {
                            if todo_set.insert(dep_nt) {
                                trace!("Retriggering {}", dep_nt);
                                todo_vec.push_back(dep_nt);
                            }
                        }
                        self.prods.insert(nt, Default::default());
                        removed.insert(nt);
                    }
                    continue;
                }
            }
            lookup.insert(key, nt);
        }

        debug!("Removed {} nonterminals", removed.len());
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

impl<'a> Nonterm<'a> {
    pub fn is_anonymous(&self) -> bool {
        match self.0 {
            NontermName::Anonymous => true,
            _ => false,
        }
    }

    pub fn is_named(&self) -> bool {
        match self.0 {
            NontermName::Name(..) => true,
            _ => false,
        }
    }

    //     pub fn this() -> Nonterm<'static> {
    //         static THIS: Nonterm = Nonterm(NontermName::Name("$this"), usize::max_value());
    //         THIS
    //     }

    //     pub fn is_this(self) -> bool {
    //         self == Self::this()
    //     }
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
    This,
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
            Symbol::This => write!(f, "$this"),
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

/// A formatter for symbol sequences.
pub struct SymbolsFormatter<'a>(&'a [Symbol<'a>]);

impl std::fmt::Display for SymbolsFormatter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "ε")
        } else {
            write!(f, "{}", self.0.iter().format(" "))
        }
    }
}

impl std::fmt::Debug for SymbolsFormatter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

pub fn format_symbols<'a>(syms: &'a [Symbol<'a>]) -> SymbolsFormatter<'a> {
    SymbolsFormatter(syms.as_ref())
}

/// A production in the grammar.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Production<'a> {
    pub nt: Nonterm<'a>,
    pub syms: Vec<Symbol<'a>>,
    pub is_epsilon: bool,
}

impl Production<'_> {
    pub fn is_epsilon(&self) -> bool {
        self.syms.is_empty() || self.is_epsilon
    }
}

impl std::fmt::Display for Production<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} -> {}", self.nt, format_symbols(&self.syms))
    }
}

impl std::fmt::Debug for Production<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// A LL(1) parse table.
pub type LlTable<'a> = BTreeMap<Nonterm<'a>, BTreeMap<Term<'a>, BTreeSet<&'a Production<'a>>>>;

/// A mapping from each nonterminal to its follow set.
pub type FollowSets<'a> = BTreeMap<Nonterm<'a>, BTreeSet<Term<'a>>>;

/// Compute the follow sets across the grammar.
fn compute_follow_sets<'a>(ctx: &Context<'a>) -> FollowSets<'a> {
    debug!("Computing follow sets");
    let mut result = FollowSets::new();

    // Keep iterating until the algorithm has converged.
    for i in 0.. {
        trace!("Follow set iteration {}", i);
        let mut into = result.clone();

        // Iterate over all productions, since we want to scan over each
        // production's symbols to determine the follow sets.
        for (nt, prods) in &ctx.prods {
            for p in prods {
                let mut leads: HashSet<Nonterm<'a>> = Default::default();
                for &sym in &p.syms {
                    match sym {
                        // Self-references cannot appear here.
                        Symbol::This => unreachable!(),
                        // If we encounter a terminal, add it to the follow set
                        // of all leads, then clear the leads since there is no
                        // longer any NT whose follow set could include anything
                        // beyond the T.
                        Symbol::Term(t) => {
                            for &lead in &leads {
                                into.entry(lead).or_default().insert(t);
                            }
                            leads.clear();
                        }
                        // If we encounter a NT, add all first Ts it may expand
                        // to to all leads. Then if the NT cannot expand to
                        // epsilon, clear the leads since there is no longer any
                        // NT whose follow set could include anything beyond
                        // this NT. Then immediately add this NT as a lead.
                        Symbol::Nonterm(nt) => {
                            let first = ctx.first_set_of_nonterm(nt);
                            for &lead in &leads {
                                into.entry(lead).or_default().extend(first.iter().cloned());
                            }
                            if !ctx.production_expands_to_epsilon(nt) {
                                leads.clear();
                            }
                            leads.insert(nt);
                        }
                    }
                }

                // Having any leads left at this point indicates that there were
                // NTs in the production where all subsequent symbols could
                // expand to epsilon. These leads inherit the follow set of the
                // current production's NT.
                for &lead in &leads {
                    if let Some(follow) = result.get(nt) {
                        into.entry(lead).or_default().extend(follow.iter().cloned());
                    }
                }
            }
        }

        // Keep iterating until the set converges.
        if result == into {
            break;
        }
        result = into;
    }

    // Ensure there's an entry for every nonterminal in the grammar.
    for nt in ctx.nonterms() {
        result.entry(nt).or_default();
    }

    result
}

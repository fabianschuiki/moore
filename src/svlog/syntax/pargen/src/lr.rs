use crate::context::{Context, Production, Symbol, Term};
use itertools::Itertools;
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
};
use typed_arena::Arena;

/// Populate a context with an LR(1) table.
pub fn build_lr(ctx: &mut Context) {
    info!("Constructing LR(1) table");

    let eof = ctx.intern_term("$");
    let root = &ctx.root_nonterms;
    let table = LrTable::new(&ctx.arena.lr_arena, eof);
    let mut kernels_seen = HashSet::new();
    let mut kernels_todo = VecDeque::new();
    for nt in root {
        let mut kb = KernelBuilder::new();
        for &p in &ctx.prods[&nt] {
            kb.add(p, 0, Some(eof));
        }
        let kernel = table.intern_kernel(kb.build(&table));
        debug!("Scheduling root {} with {:#?}", nt, kernel);
        kernels_seen.insert(kernel);
        kernels_todo.push_back(kernel);
    }

    while let Some(kernel) = kernels_todo.pop_front() {
        // debug!("Adding state {:#?}", kernel);

        // Expand the items.
        let mut items = kernel.clone();
        let mut todo = VecDeque::new();
        todo.extend(items.iter().copied());
        while let Some(item) = todo.pop_front() {
            match item.current() {
                Some(Symbol::Nonterm(nt)) => {
                    // trace!("Expanding {}", item);
                    let mut lookahead = ctx.first_set_of_symbols(item.next_tail());
                    if ctx.symbols_expand_to_epsilon(item.next_tail()) {
                        lookahead.extend(item.lookahead);
                    }
                    let lookahead = table.intern_lookahead(lookahead);
                    for &p in &ctx.prods[&nt] {
                        let item = LrItem::new(p, 0, lookahead);
                        if items.insert(item.clone()) {
                            todo.push_back(item);
                        }
                    }
                }
                _ => (),
            }
        }
        // trace!("Items: {:#?}", items);

        // Determine the kernels of the next states.
        let mut next_items = BTreeMap::<_, KernelBuilder>::new();
        for &item in &items {
            if let Some(sym) = item.current() {
                let mut item = item.clone();
                item.pos += 1;
                next_items.entry(sym).or_default().add_item(item);
            }
        }
        // trace!("Next: {:#?}", next_items);

        for (_sym, kb) in next_items {
            let kernel = table.intern_kernel(kb.build(&table));
            if kernels_seen.insert(kernel) {
                kernels_todo.push_back(kernel);
            }
        }

        // trace!("{} kernels left", kernels_todo.len());
        // std::io::stdin().read_line(&mut Default::default()).unwrap();
    }

    info!("Created {} states", kernels_seen.len());
}

/// An arena for LR(1) structure interning.
#[derive(Default)]
pub struct LrArena<'a> {
    pub(crate) kernel_arena: Arena<Kernel<'a>>,
    pub(crate) lookahead_arena: Arena<BTreeSet<Term<'a>>>,
    pub(crate) state_arena: Arena<State<'a>>,
}

/// An LR(1) parsing table.
pub struct LrTable<'a> {
    pub arena: &'a LrArena<'a>,
    /// The end-of-file marker terminal.
    pub eof: Term<'a>,
    pub kernels: RefCell<BTreeSet<&'a Kernel<'a>>>,
    pub lookaheads: RefCell<BTreeSet<&'a Lookahead<'a>>>,
    pub states: BTreeMap<&'a Kernel<'a>, &'a State<'a>>,
}

impl<'a> LrTable<'a> {
    pub fn new(arena: &'a LrArena<'a>, eof: Term<'a>) -> Self {
        Self {
            arena,
            eof,
            kernels: Default::default(),
            lookaheads: Default::default(),
            states: Default::default(),
        }
    }

    pub fn intern_kernel(&self, kernel: Kernel<'a>) -> &'a Kernel<'a> {
        if let Some(k) = self.kernels.borrow().get(&kernel) {
            return k;
        }
        let ptr = self.arena.kernel_arena.alloc(kernel);
        self.kernels.borrow_mut().insert(ptr);
        ptr
    }

    pub fn intern_lookahead(&self, lookahead: Lookahead<'a>) -> &'a Lookahead<'a> {
        if let Some(k) = self.lookaheads.borrow().get(&lookahead) {
            return k;
        }
        let ptr = self.arena.lookahead_arena.alloc(lookahead);
        self.lookaheads.borrow_mut().insert(ptr);
        ptr
    }
}

/// An LR(1) parser state.
pub struct State<'a> {
    pub kernel: &'a Kernel<'a>,
    pub items: BTreeSet<LrItem<'a>>,
}

/// The kernel item set of a state.
pub type Kernel<'a> = BTreeSet<LrItem<'a>>;

/// A builder for a kernel.
///
/// The main purpose of the builder is to collapse items that only differ in the
/// lookahead into one item.
#[derive(Default)]
pub struct KernelBuilder<'a> {
    items: HashMap<(&'a Production<'a>, usize), Lookahead<'a>>,
}

impl<'a> KernelBuilder<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn add(
        &mut self,
        prod: &'a Production<'a>,
        pos: usize,
        lookahead: impl IntoIterator<Item = Term<'a>>,
    ) -> &mut Self {
        self.items.entry((prod, pos)).or_default().extend(lookahead);
        self
    }

    pub fn add_item(&mut self, item: LrItem<'a>) -> &mut Self {
        self.items
            .entry((item.prod, item.pos))
            .or_default()
            .extend(item.lookahead);
        self
    }

    pub fn build(self, table: &LrTable<'a>) -> Kernel<'a> {
        self.items
            .into_iter()
            .map(|((prod, pos), lookahead)| {
                LrItem::new(prod, pos, table.intern_lookahead(lookahead))
            })
            .collect()
    }
}

/// The lookahead terminals of an item.
pub type Lookahead<'a> = BTreeSet<Term<'a>>;

/// An item in an LR(1) state.
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct LrItem<'a> {
    pub prod: &'a Production<'a>,
    pub pos: usize,
    pub lookahead: &'a Lookahead<'a>,
}

impl<'a> LrItem<'a> {
    /// Create a new item.
    pub fn new(prod: &'a Production<'a>, pos: usize, lookahead: &'a Lookahead<'a>) -> Self {
        Self {
            prod,
            pos,
            lookahead,
        }
    }

    /// Get the current symbol in the production, or `None` if at the end.
    pub fn current(&self) -> Option<Symbol<'a>> {
        self.prod.syms.get(self.pos).cloned()
    }

    /// Get the next symbol in the production, or `None` if at the end.
    pub fn next(&self) -> Option<Symbol<'a>> {
        self.prod.syms.get(self.pos + 1).cloned()
    }

    /// Get the remaining symbols in the production, including the current one.
    pub fn current_tail(&self) -> &'a [Symbol<'a>] {
        &self.prod.syms[self.pos..]
    }

    /// Get the remaining symbols in the production, excluding the current one.
    pub fn next_tail(&self) -> &'a [Symbol<'a>] {
        if self.pos + 1 <= self.prod.syms.len() {
            &self.prod.syms[self.pos + 1..]
        } else {
            &[]
        }
    }
}

impl std::fmt::Display for LrItem<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.prod.is_epsilon() {
            write!(f, "[{} -> ε, #{}]", self.prod.nt, self.lookahead.len())
        } else {
            write!(
                f,
                "[{} -> {} · {}, #{}]",
                self.prod.nt,
                self.prod.syms[0..self.pos].iter().format(" "),
                self.prod.syms[self.pos..].iter().format(" "),
                self.lookahead.len()
            )
        }
    }
}

impl std::fmt::Debug for LrItem<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

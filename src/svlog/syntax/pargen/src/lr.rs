use crate::context::{Context, Nonterm, Production, Symbol, Term};
use anyhow::Result;
use itertools::Itertools;
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    io::Write,
};

/// Populate a context with an LR(1) table.
pub fn build_lr(ctx: &mut Context) {
    info!("Constructing LR(1) table");

    let eof = ctx.intern_term("$");
    let mut tb = TableBuilder::new(&ctx.arena.lr_arena);
    let mut states_seen = HashSet::new();
    let mut states_todo = VecDeque::new();

    // Populate the worklist with the kernels of the root items.
    for &nt in &ctx.root_nonterms {
        let mut kb = KernelBuilder::new();
        for &p in &ctx.prods[&nt] {
            kb.add(p, 0, Some(eof));
        }
        let kernel = tb.intern_kernel(kb.build(&tb));
        let state = tb.intern_state(kernel, ctx);
        tb.table.root_states.insert(nt, state);
        debug!("Scheduling root {} as {:?}", nt, state);
        if states_seen.insert(state) {
            states_todo.push_back(state);
        }
    }

    // Keep processing new kernels and states.
    while let Some(state) = states_todo.pop_front() {
        // debug!("Adding state {:#?}", state);
        // println!("State {:?}", state);
        let mut actions = StateActions::new();

        // Determine the kernels of the next states.
        let mut next_items = BTreeMap::<_, KernelBuilder>::new();
        for &item in &state.items {
            if let Some(sym) = item.current() {
                let mut item = item.clone();
                item.pos += 1;
                next_items.entry(sym).or_default().add_item(item);
            } else {
                for &sym in item.lookahead {
                    actions
                        .entry(sym.into())
                        .or_default()
                        .insert(Action::Reduce(item.prod));
                }
            }
        }
        // trace!("Next: {:#?}", next_items);

        for (sym, kb) in next_items {
            let kernel = tb.intern_kernel(kb.build(&tb));
            let state = tb.intern_state(kernel, ctx);
            actions.entry(sym).or_default().insert(Action::Shift(state));
            if states_seen.insert(state) {
                states_todo.push_back(state);
            }
        }
        // println!("{:#?}", actions);
        tb.table.actions.insert(state, actions);

        // trace!("{} kernels left", states_todo.len());
        // std::io::stdin().read_line(&mut Default::default()).unwrap();
    }

    info!("Created {} states", states_seen.len());
    ctx.lr_table = tb.build();
}

/// An arena for LR(1) structure interning.
#[derive(Default)]
pub struct Arena<'a> {
    pub(crate) kernel_arena: typed_arena::Arena<Kernel<'a>>,
    pub(crate) lookahead_arena: typed_arena::Arena<BTreeSet<Term<'a>>>,
    pub(crate) state_arena: typed_arena::Arena<StateData<'a>>,
}

/// An LR(1) parsing table.
#[derive(Default)]
pub struct Table<'a> {
    /// The end-of-file marker terminal.
    pub states: Vec<State<'a>>,
    pub state_lookup: HashMap<&'a Kernel<'a>, State<'a>>,
    pub root_states: BTreeMap<Nonterm<'a>, State<'a>>,
    /// The action table.
    pub actions: BTreeMap<State<'a>, StateActions<'a>>,
}

/// Emit the states in an LR(1) parsing table.
pub fn dump_states(table: &Table, out: &mut impl Write) -> Result<()> {
    write!(out, "Parser has {} states\n", table.states.len())?;
    for &state in &table.states {
        write!(
            out,
            "\nState {} {:#?} {:#?} {{\n",
            state,
            state.kernel,
            state
                .items
                .difference(state.kernel)
                .collect::<BTreeSet<_>>(),
        )?;
        let mut actions = BTreeMap::<Action, BTreeSet<Symbol>>::new();
        for (&sym, acs) in &table.actions[&state] {
            for &action in acs {
                actions.entry(action).or_default().insert(sym);
            }
        }
        for (action, syms) in actions {
            write!(out, "    {} upon {:?},\n", action, syms)?;
        }
        write!(out, "}}\n")?;
    }
    Ok(())
}

/// Emit the conflicts in an LR(1) parsing table.
pub fn dump_conflicts(table: &Table, out: &mut impl Write) -> Result<usize> {
    let mut num_conflicts = 0;
    for (&state, actions) in &table.actions {
        let mut reported = false;
        for (&sym, actions) in actions {
            if actions.len() > 1 {
                if !reported {
                    write!(
                        out,
                        "Conflict in {} {:#?} {:#?} {{\n",
                        state,
                        state.kernel,
                        state
                            .items
                            .difference(state.kernel)
                            .collect::<BTreeSet<_>>(),
                    )?;
                    reported = true;
                }
                write!(out, "    {} -> {:?}\n", sym, actions)?;
                num_conflicts += 1;
            }
        }
        if reported {
            write!(out, "}}\n\n")?;
        }
    }
    write!(out, "Found {} conflicts\n", num_conflicts)?;
    Ok(num_conflicts)
}

/// A parsing table builder.
pub struct TableBuilder<'a> {
    arena: &'a Arena<'a>,
    table: Table<'a>,
    kernels: RefCell<BTreeSet<&'a Kernel<'a>>>,
    lookaheads: RefCell<BTreeSet<&'a Lookahead<'a>>>,
}

impl<'a> TableBuilder<'a> {
    pub fn new(arena: &'a Arena<'a>) -> Self {
        Self {
            arena,
            table: Default::default(),
            kernels: Default::default(),
            lookaheads: Default::default(),
        }
    }

    pub fn build(self) -> Table<'a> {
        self.table
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

    pub fn intern_state(&mut self, kernel: &'a Kernel<'a>, ctx: &Context<'a>) -> State<'a> {
        if let Some(&state) = self.table.state_lookup.get(&kernel) {
            return state;
        }

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
                    let lookahead = self.intern_lookahead(lookahead);
                    for &p in &ctx.prods[&nt] {
                        let item = Item::new(p, 0, lookahead);
                        if items.insert(item.clone()) {
                            todo.push_back(item);
                        }
                    }
                }
                _ => (),
            }
        }

        // Combine items which only differ in their lookaheads.
        let mut kb = KernelBuilder::new();
        for item in items {
            kb.add_item(item);
        }
        let items = kb.build(self);

        // Create the state data and internalize.
        let data = self.arena.state_arena.alloc(StateData { kernel, items });
        let v = State(data, self.table.states.len());
        self.table.states.push(v);
        self.table.state_lookup.insert(kernel, v);
        v
    }
}

/// An interned LR(1) parser state.
#[derive(Copy, Clone)]
pub struct State<'a>(&'a StateData<'a>, usize);

impl std::fmt::Display for State<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "s{}", self.1)
    }
}

impl std::fmt::Debug for State<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "s{} {}", self.1, self.0)
    }
}

impl Eq for State<'_> {}

impl PartialEq for State<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

impl Ord for State<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&self.1, &other.1)
    }
}

impl PartialOrd for State<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(&self.1, &other.1)
    }
}

impl std::hash::Hash for State<'_> {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        std::hash::Hash::hash(&self.1, hasher)
    }
}

impl<'a> std::ops::Deref for State<'a> {
    type Target = &'a StateData<'a>;

    fn deref(&self) -> &&'a StateData<'a> {
        &self.0
    }
}

/// An LR(1) parser state.
pub struct StateData<'a> {
    pub kernel: &'a Kernel<'a>,
    pub items: BTreeSet<Item<'a>>,
}

impl std::fmt::Display for StateData<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:#?}", self.kernel)
    }
}

impl std::fmt::Debug for StateData<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// The kernel item set of a state.
pub type Kernel<'a> = BTreeSet<Item<'a>>;

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

    pub fn add_item(&mut self, item: Item<'a>) -> &mut Self {
        self.items
            .entry((item.prod, item.pos))
            .or_default()
            .extend(item.lookahead);
        self
    }

    pub fn build(self, tb: &TableBuilder<'a>) -> Kernel<'a> {
        self.items
            .into_iter()
            .map(|((prod, pos), lookahead)| Item::new(prod, pos, tb.intern_lookahead(lookahead)))
            .collect()
    }
}

/// The lookahead terminals of an item.
pub type Lookahead<'a> = BTreeSet<Term<'a>>;

/// An item in an LR(1) state.
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Item<'a> {
    pub prod: &'a Production<'a>,
    pub pos: usize,
    pub lookahead: &'a Lookahead<'a>,
}

impl<'a> Item<'a> {
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

impl std::fmt::Display for Item<'_> {
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

impl std::fmt::Debug for Item<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// An action to be taken in a parser state.
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Action<'a> {
    /// Shift the next symbol and advance to another state.
    Shift(State<'a>),
    /// Reduce using a production.
    Reduce(&'a Production<'a>),
}

impl std::fmt::Display for Action<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            Action::Shift(s) => write!(f, "shift({})", s),
            Action::Reduce(p) => write!(f, "reduce({})", p.nt),
        }
    }
}

impl std::fmt::Debug for Action<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// The actions that can be taken in a state.
pub type StateActions<'a> = BTreeMap<Symbol<'a>, BTreeSet<Action<'a>>>;

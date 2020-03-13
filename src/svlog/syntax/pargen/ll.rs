use crate::context::{Context, LlTable, Nonterm, Production, Symbol, Term};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

/// Populate a context with an LL(1) table.
pub fn build_ll(ctx: &mut Context) {
    info!("Constructing LL(1) table");
    let follow = collect_follow(ctx);
    let mut table = Default::default();
    for (&nt, prods) in &ctx.prods {
        for p in prods {
            for t in first_set_of_smybols(ctx, &p.syms) {
                add_action(&mut table, nt, t, p);
            }
            if ctx.symbols_expand_to_epsilon(&p.syms) {
                // trace!("Adding follow set {}", nt);
                for &t in &follow[&nt] {
                    add_action(&mut table, nt, t, p);
                }
            }
        }
    }
    ctx.ll_table = table;
}

fn add_action<'a>(table: &mut LlTable<'a>, nt: Nonterm<'a>, term: Term<'a>, p: &'a Production<'a>) {
    if table
        .entry(nt)
        .or_default()
        .entry(term)
        .or_default()
        .insert(p)
    {
        // trace!("[{}, {}] = {}", nt, term, p);
    }
}

/// Collect the set of starting symbols that can be derived from a slice of
/// symbols.
fn first_set_of_smybols<'a>(ctx: &Context<'a>, syms: &[Symbol<'a>]) -> BTreeSet<Term<'a>> {
    let mut into = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut todo = VecDeque::new();
    seen.insert(syms);
    todo.push_back(syms);

    while let Some(syms) = todo.pop_front() {
        let mut iter = syms.iter();
        while let Some(&sym) = iter.next() {
            match sym {
                Symbol::Error => break,
                Symbol::Epsilon => continue,
                Symbol::Term(t) => {
                    into.insert(t);
                    break;
                }
                Symbol::Nonterm(nt) => {
                    for p in &ctx.prods[&nt] {
                        if seen.insert(&p.syms) {
                            todo.push_back(&p.syms);
                        }
                    }
                    if !ctx.production_expands_to_epsilon(nt) {
                        break;
                    }
                }
            }
        }
    }

    into
}

/// Collect the set of starting symbols that can be derived from a NT.
fn first_set_of_nonterm<'a>(ctx: &Context<'a>, nt: Nonterm<'a>) -> BTreeSet<Term<'a>> {
    let mut into = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut todo = VecDeque::new();
    seen.insert(nt);
    todo.push_back(nt);

    while let Some(nt) = todo.pop_front() {
        for p in &ctx.prods[&nt] {
            let mut iter = p.syms.iter();
            while let Some(&sym) = iter.next() {
                match sym {
                    Symbol::Error => break,
                    Symbol::Epsilon => continue,
                    Symbol::Term(t) => {
                        into.insert(t);
                        break;
                    }
                    Symbol::Nonterm(nt) => {
                        if seen.insert(nt) {
                            todo.push_back(nt);
                        }
                        if !ctx.production_expands_to_epsilon(nt) {
                            break;
                        }
                    }
                }
            }
        }
    }

    into
}

/// Compute the follow sets across the grammar.
fn collect_follow<'a>(ctx: &Context<'a>) -> BTreeMap<Nonterm<'a>, BTreeSet<Term<'a>>> {
    let mut result = BTreeMap::<Nonterm<'a>, BTreeSet<Term<'a>>>::new();

    // Keep iterating until the algorithm has converged.
    loop {
        trace!("Follow set iteration");
        let mut into = result.clone();

        // Iterate over all productions, since we want to scan over each
        // production's symbols to determine the follow sets.
        for (nt, prods) in &ctx.prods {
            for p in prods {
                let mut leads: HashSet<Nonterm<'a>> = Default::default();
                for &sym in &p.syms {
                    match sym {
                        // In case of an error, just abort.
                        Symbol::Error => {
                            leads.clear();
                            break;
                        }
                        // Epsilons are treated as transparent.
                        Symbol::Epsilon => continue,
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
                            let first = first_set_of_nonterm(ctx, nt);
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

/// Left-factor the LL(1) table in a context.
///
/// Returns whether any changes have been performed, and thus the table should
/// be reconstructed.
pub fn left_factor(ctx: &mut Context) -> bool {
    info!("Left-factoring LL(1) table");
    let mut changes = false;
    let mut ambigs = vec![];
    for (&nt, ts) in &ctx.ll_table {
        let mut prods = BTreeSet::new();
        for (t, ps) in ts {
            if ps.len() > 1 {
                prods.insert(ps.clone());
            }
        }
        for ps in prods {
            ambigs.push((nt, ps));
        }
    }
    for (nt, prods) in ambigs {
        changes |= handle_ambiguity(ctx, nt, &prods);
    }
    changes
}

fn handle_ambiguity<'a>(
    ctx: &mut Context<'a>,
    nt: Nonterm<'a>,
    prods: &BTreeSet<&'a Production<'a>>,
) -> bool {
    // trace!("Handling ambiguous {}:", nt);
    // for p in prods {
    //     trace!("  {}", p);
    // }

    // Left-factor the productions if they have a unique symbol in first
    // position.
    let mut any_epsilon = false;
    let mut firsts = BTreeSet::new();
    for p in prods {
        if let Some(&first) = p.syms.iter().next() {
            firsts.insert(first);
        }
        any_epsilon |= p.is_epsilon;
    }
    if any_epsilon {
        warn!("Skipping left-factoring {} due to epsilon", nt);
        return false;
    } else if firsts.len() == 1 {
        let sym = firsts.into_iter().next().unwrap();
        debug!("Left-factoring {} out of {}", sym, nt);
        let aux = ctx.anonymous_nonterm();
        ctx.add_production(nt, vec![sym, Symbol::Nonterm(aux)]);
        for p in prods {
            let mut new_syms: Vec<_> = p.syms.iter().skip(1).cloned().collect();
            ctx.add_production(aux, new_syms);
            ctx.remove_production(p);
        }
        return true;
    }

    // Inline any nonterminals in first position.
    let mut any_inlined = false;
    for p in prods {
        if let Some(&Symbol::Nonterm(lnt)) = p.syms.iter().next() {
            // TODO: We somehow need to keep track of the fact that this was
            // inlined, and probably needs some wrapping up to be done.
            debug!("Inlining {} in {}", lnt, p);
            for lp in ctx.prods[&lnt].clone() {
                // trace!("  {}", lp);
                let new_syms = lp
                    .syms
                    .iter()
                    .chain(p.syms.iter().skip(1))
                    .cloned()
                    .collect();
                ctx.add_production(nt, new_syms);
            }
            ctx.remove_production(p);
            any_inlined = true;
        }
    }

    any_inlined
}

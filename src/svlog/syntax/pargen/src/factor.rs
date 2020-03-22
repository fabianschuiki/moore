#![allow(unused_imports)]
use crate::context::{format_symbols, Context, LlTable, Nonterm, Production, Symbol, Term};
use itertools::Itertools;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    rc::Rc,
};

/// Eliminate epsilon derivations from the grammar.
pub fn remove_epsilon_derivation(ctx: &mut Context) -> bool {
    debug!("Removing ε-derivation");
    let mut modified = false;
    while remove_epsilon_derivation_inner(ctx) {
        modified = true;
    }
    modified
}

fn remove_epsilon_derivation_inner(ctx: &mut Context) -> bool {
    // Find all nonterminals which can derive epsilon and cause ambiguity.
    let mut todo = vec![];
    for (&nt, ps) in &ctx.prods {
        for &p in ps {
            if p.is_epsilon() {
                let first = ctx.first_set_of_nonterm(nt);
                let follow = ctx.follow_set(nt);
                if !first.is_disjoint(&follow) {
                    todo.push(p);
                }
            }
        }
    }

    // Process the problematic rules.
    let mut repls = HashMap::new();
    for outer in todo {
        debug!("Eliminating {}", outer);
        ctx.remove_production(outer);
        for (_, ps) in &ctx.prods {
            for &p in ps {
                if let Some(repl) = expand_epsilon(ctx, outer.nt, p) {
                    trace!("Expanding {} to {} productions", p, repl.len());
                    repls.insert(p, repl);
                }
            }
        }
    }

    // Apply the replacements.
    let modified = !repls.is_empty();
    for (p, repl) in repls {
        ctx.remove_production(p);
        for syms in repl {
            ctx.add_production(p.nt, syms);
        }
    }
    modified
}

fn expand_epsilon<'a>(
    _ctx: &Context<'a>,
    nt: Nonterm<'a>,
    prod: &'a Production<'a>,
) -> Option<Vec<Vec<Symbol<'a>>>> {
    let mut leads = vec![vec![]];
    for &sym in &prod.syms {
        if sym == Symbol::Nonterm(nt) {
            for mut l in std::mem::replace(&mut leads, vec![]) {
                leads.push(l.clone());
                l.push(sym);
                leads.push(l);
            }
        } else {
            leads.iter_mut().for_each(|l| l.push(sym));
        }
    }
    if leads.len() > 1 {
        Some(leads)
    } else {
        None
    }
}

/// Remove indirect left-recursion from the grammar.
pub fn remove_indirect_left_recursion(ctx: &mut Context) -> bool {
    debug!("Removing indirect left-recursion");
    for (&nt, _) in &ctx.prods {
        find_indirect_left_recursion(
            ctx,
            nt,
            nt,
            &mut Default::default(),
            &mut Default::default(),
        );
    }
    false
}

fn find_indirect_left_recursion<'a>(
    ctx: &Context<'a>,
    root: Nonterm<'a>,
    nt: Nonterm<'a>,
    seen: &mut HashSet<Nonterm<'a>>,
    stack: &mut Vec<&'a Production<'a>>,
) {
    for &p in &ctx.prods[&nt] {
        if let Some(Symbol::Nonterm(first)) = p.syms.iter().cloned().next() {
            if first == root {
                if seen.contains(&first) {
                    error!("Unhandled indirect left-recursion in {}", root);
                    for s in stack.iter() {
                        error!("  {}", s);
                    }
                }
            } else if !seen.contains(&first) {
                seen.insert(first);
                stack.push(p);
                find_indirect_left_recursion(ctx, root, first, seen, stack);
                seen.remove(&first);
                stack.pop();
            }
        }
    }
}

/// Remove left-recursion from the grammar.
pub fn remove_direct_left_recursion(ctx: &mut Context) -> bool {
    debug!("Removing direct left-recursion");

    // Find the left-recursive NTs.
    let mut rec = vec![];
    for (&nt, ps) in &ctx.prods {
        let left_rec: HashSet<_> = ps
            .iter()
            .cloned()
            .filter(|p| p.syms.iter().next() == Some(&Symbol::Nonterm(p.nt)))
            .collect();
        if !left_rec.is_empty() {
            rec.push((nt, left_rec));
        }
    }

    // Remove left-recursions.
    let modified = !rec.is_empty();
    for (nt, left_rec) in rec {
        debug!("Removing left-recursion in {}", nt);
        let aux = ctx.anonymous_nonterm();

        // Add the recursive productions to the new nonterminal.
        for p in left_rec {
            let mut new_syms: Vec<_> = p.syms.iter().skip(1).cloned().collect();
            new_syms.push(Symbol::Nonterm(aux));
            ctx.add_production(aux, new_syms);
            ctx.remove_production(p);
        }
        ctx.add_production(aux, vec![]);

        // Update the non-recursive productions in the old non-terminal.
        for p in ctx.prods[&nt].clone() {
            let mut new_syms = p.syms.clone();
            new_syms.push(Symbol::Nonterm(aux));
            ctx.add_production(nt, new_syms);
            ctx.remove_production(p);
        }
    }
    modified
}

/// Perform a simple left-factorization of the grammar.
pub fn left_factorize_simple(ctx: &mut Context) -> bool {
    debug!("Left-factoring grammar (simple)");

    // Identify ambiguous rules that require factoring.
    let mut conflicts = vec![];
    for (&nt, ps) in &ctx.prods {
        if has_conflict(ctx, ps) {
            conflicts.push((
                nt,
                ctx.prods[&nt]
                    .iter()
                    .cloned()
                    .filter(|p| !p.is_epsilon())
                    .collect(),
            ));
        }
    }

    // Refactor those rules.
    let mut modified = false;
    for (nt, ps) in conflicts {
        modified |= left_factorize_conflict(ctx, nt, ps);
    }

    modified
}

pub(crate) fn has_conflict<'a>(ctx: &Context<'a>, ps: &BTreeSet<&Production<'a>>) -> bool {
    let mut seen = HashSet::new();
    for p in ps {
        for s in ctx.first_set_of_symbols(&p.syms) {
            if !seen.insert(s) {
                return true;
            }
        }
    }
    false
}

fn left_factorize_conflict<'a>(
    ctx: &mut Context<'a>,
    nt: Nonterm<'a>,
    mut todo: BTreeSet<&'a Production<'a>>,
) -> bool {
    let firsts: HashMap<&Production, BTreeSet<Term>> = todo
        .iter()
        .map(|&p| (p, ctx.first_set_of_symbols(&p.syms)))
        .collect();
    let mut modified = false;
    while let Some(&init) = todo.iter().next() {
        todo.remove(&init);
        let mut colliders = BTreeSet::new();
        colliders.insert(init);
        let mut seen = HashSet::new();
        seen.extend(firsts[init].iter().cloned());
        for s in std::mem::take(&mut todo) {
            let mut any_hit = false;
            for &f in &firsts[&s] {
                if seen.contains(&f) {
                    any_hit = true;
                    break;
                }
            }
            if any_hit {
                seen.extend(firsts[&s].iter().cloned());
                colliders.insert(s);
            } else {
                todo.insert(s);
            }
        }
        if colliders.len() > 1 {
            modified |= left_factorize_disambiguate(ctx, nt, colliders.into_iter().collect());
        }
    }
    modified
}

fn left_factorize_disambiguate<'a>(
    ctx: &mut Context<'a>,
    nt: Nonterm<'a>,
    prods: Vec<&'a Production<'a>>,
) -> bool {
    // trace!("  Disambiguate:");
    // for p in &prods {
    //     trace!("    {}", p.syms.iter().format(" "));
    // }

    // Find a common prefix, considering balanced tokens to factor out parts of
    // the rules.
    let mut prefix = vec![];
    let mut offsets: Vec<usize> = prods.iter().map(|_| 0).collect();
    loop {
        // Find the set of next symbols in the rules.
        let symbols: HashSet<_> = prods
            .iter()
            .zip(offsets.iter())
            .map(|(p, &offset)| p.syms.get(offset))
            .collect();

        // Check if we have one unique prefix symbol.
        if symbols.len() != 1 {
            break;
        }
        let symbol = match symbols.into_iter().next().unwrap() {
            Some(&p) => p,
            None => break,
        };

        // If the symbol is the left of a balanced pair, advance ahead to its
        // counterpart and gobble up the symbols in between.
        prefix.push(symbol);
        let balanced_end = match symbol.to_string().as_str() {
            "'('" => ctx.lookup_symbol("')'"),
            "'['" => ctx.lookup_symbol("']'"),
            "'{'" => ctx.lookup_symbol("'}'"),
            _ => None,
        };
        if let Some(balanced_end) = balanced_end {
            // trace!("    Factoring-out balanced {} {}", symbol, balanced_end);
            let mut subseqs = vec![];
            for (p, offset) in prods.iter().zip(offsets.iter_mut()) {
                *offset += 1;
                let mut subsyms = vec![];
                while p.syms[*offset] != balanced_end {
                    subsyms.push(p.syms[*offset]);
                    *offset += 1;
                }
                *offset += 1;
                subseqs.push(subsyms);
            }
            // trace!("  Gobbled up subsequences:");
            let aux = ctx.anonymous_nonterm();
            for s in subseqs {
                // trace!("    {}", s.iter().format(" "));
                ctx.add_production(aux, s);
            }
            prefix.push(Symbol::Nonterm(aux));
            prefix.push(balanced_end);
        } else {
            offsets.iter_mut().for_each(|o| *o += 1);
        }
    }
    // trace!("  Prefix {}", format_symbols(&prefix));
    if prefix.is_empty() {
        return false;
    }
    debug!("Factoring {} out from {}", format_symbols(&prefix), nt);

    // Compute the tails that are left over after prefix extraction.
    let tails: BTreeSet<_> = prods
        .iter()
        .zip(offsets.iter())
        .map(|(p, &offset)| &p.syms[offset..])
        .collect();

    // If there is one common tail, add that to the prefix immediately.
    // Otherwise just go ahead and create an auxiliary nonterminal that will
    // contain all of the tails.
    if tails.len() == 1 {
        let tail = tails.into_iter().next().unwrap();
        if !tail.is_empty() {
            // trace!("  Adding unique tail {}", format_symbols(tail));
            prefix.extend(tail);
        }
    } else {
        let aux = ctx.anonymous_nonterm();
        // trace!("  Adding auxiliary tail {}:", aux);
        prefix.push(Symbol::Nonterm(aux));
        for tail in tails {
            let _p = ctx.add_production(aux, tail.to_vec());
            // trace!("    {}", p);
        }
    }

    // Actually replace the production.
    // trace!("  Replacing:");
    for &p in &prods {
        // trace!("    {}", p);
        ctx.remove_production(p);
    }
    // trace!("  With:");
    let _p = ctx.add_production(nt, prefix);
    // trace!("    {}", p);

    true
}

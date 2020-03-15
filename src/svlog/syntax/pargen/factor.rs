use crate::context::{Context, LlTable, Nonterm, Production, Symbol, Term};
use itertools::Itertools;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    rc::Rc,
};

/// Remove left-recursion from the grammar.
pub fn remove_left_recursion(ctx: &mut Context) {
    info!("Removing left-recursion");

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
}

/// Left-factor the grammar.
pub fn left_factor(ctx: &mut Context) {
    info!("Left-factoring grammar");

    // Identift ambiguous rules that require factoring.
    for (&nt, ps) in &ctx.prods {
        if has_conflict(ctx, ps) {
            debug!("Conflict in {}", nt);
            for p in ps {
                trace!("  {}", p);
            }
            handle_conflict(
                ctx,
                ctx.prods[&nt].iter().map(|p| p.syms.as_slice()).collect(),
                &mut Default::default(),
            );
        }
    }
}

fn has_conflict<'a>(ctx: &Context<'a>, ps: &BTreeSet<&Production<'a>>) -> bool {
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

fn handle_conflict<'a>(
    ctx: &Context<'a>,
    seqs: BTreeSet<&[Symbol<'a>]>,
    stack: &mut HashSet<Vec<Symbol<'a>>>,
) {
    let mut todo: BTreeSet<_> = seqs.into_iter().filter(|s| !s.is_empty()).collect();
    let mut firsts: HashMap<&[Symbol], BTreeSet<Term>> = todo
        .iter()
        .map(|&s| (s, ctx.first_set_of_symbols(s)))
        .collect();
    while let Some(&init) = todo.iter().next() {
        todo.remove(&init);
        let mut colliders = BTreeSet::new();
        colliders.insert(init);
        let mut seen = HashSet::new();
        seen.extend(firsts[init].iter().cloned());
        // trace!("Starting with {} firsts {:?}", init, seen);
        for s in std::mem::take(&mut todo) {
            // trace!("  {} firsts {:?}", s, firsts[&s]);
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
        // trace!("Colliders {:?}", colliders);
        disambiguate(ctx, colliders.into_iter().collect(), stack);
    }
}

fn disambiguate<'a>(
    ctx: &Context<'a>,
    seqs: Vec<&[Symbol<'a>]>,
    stack: &mut HashSet<Vec<Symbol<'a>>>,
) {
    // Handle the trivial case.
    if seqs.len() == 1 {
        return;
    }
    trace!("Disambiguate:");
    for syms in &seqs {
        trace!("  {}", syms.iter().format(" "));
    }

    // Fully expand nonterminals in first place.
    #[derive(Clone)]
    struct Lead<'a> {
        parent: Option<Rc<Lead<'a>>>,
        syms: Vec<Symbol<'a>>,
    }
    let mut done = vec![];
    let mut leads: Vec<Lead<'a>> = seqs
        .iter()
        .map(|s| Lead {
            parent: None,
            syms: s.to_vec(),
        })
        .collect();

    while !leads.is_empty() {
        for lead in std::mem::take(&mut leads) {
            assert!(
                !lead.syms.is_empty(),
                "there should be no expansion to epsilon"
            );
            match lead.syms[0] {
                Symbol::Nonterm(nt) => {
                    let parent = Rc::new(lead);
                    for p in &ctx.prods[&nt] {
                        leads.push(Lead {
                            parent: Some(parent.clone()),
                            syms: p
                                .syms
                                .iter()
                                .cloned()
                                .chain(parent.syms.iter().skip(1).cloned())
                                .collect(),
                        });
                    }
                }
                _ => {
                    done.push(lead);
                }
            }
        }
    }

    // Step-by-step revert the expansion as long as all leads match.
    loop {
        let firsts: BTreeSet<_> = done
            .iter()
            .map(|lead| lead.parent.as_ref().map(|p| p.syms[0]))
            .collect();
        if firsts.len() == 1 && firsts.iter().next().unwrap().is_some() {
            for lead in std::mem::take(&mut done) {
                done.push((*lead.parent.unwrap()).clone());
            }
        } else {
            break;
        }
    }
    let mut done: Vec<_> = done.into_iter().map(|lead| lead.syms).collect();
    done.sort();
    done.dedup();

    trace!("Expanded:");
    for d in &done {
        trace!("  {}", d.iter().format(" "));
    }

    // No need to further disambiguate if we have only one lead.
    if done.len() <= 1 {
        return;
    }

    // Find a common prefix, considering balanced tokens to factor out parts of
    // the rules.
    let mut prefix = vec![];
    let mut offsets: Vec<usize> = done.iter().map(|_| 0).collect();
    loop {
        // Find the set of next symbols in the rules.
        let symbols: HashSet<_> = done
            .iter()
            .zip(offsets.iter())
            .map(|(syms, &offset)| syms.get(offset))
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
            trace!("  Factoring-out balanced {} {}", symbol, balanced_end);
            let mut subseqs = vec![];
            for (syms, offset) in done.iter().zip(offsets.iter_mut()) {
                *offset += 1;
                let mut subsyms = vec![];
                while syms[*offset] != balanced_end {
                    subsyms.push(syms[*offset]);
                    *offset += 1;
                }
                *offset += 1;
                subseqs.push(subsyms);
            }
            trace!("  Gobbled up subsequences:");
            for s in &subseqs {
                trace!("    {}", s.iter().format(" "));
            }
            prefix.push(Symbol::Error);
            prefix.push(balanced_end);
            break;
        } else {
            offsets.iter_mut().for_each(|o| *o += 1);
        }
    }
    trace!("  Prefix {}", prefix.iter().format(" "));

    // // Find common prefices and suffices.
    // let mut prefix = vec![];
    // loop {
    //     let set: HashSet<_> = done
    //         .iter()
    //         .map(|syms| syms.iter().skip(prefix.len()).next())
    //         .collect();
    //     if set.len() == 1 {
    //         if let Some(p) = set.into_iter().next().unwrap() {
    //             prefix.push(p);
    //         } else {
    //             break;
    //         }
    //     } else {
    //         break;
    //     }
    // }
    // let mut suffix = vec![];
    // loop {
    //     let set: HashSet<_> = done
    //         .iter()
    //         .map(|syms| syms.iter().rev().skip(suffix.len()).next())
    //         .collect();
    //     if set.len() == 1 {
    //         if let Some(s) = set.into_iter().next().unwrap() {
    //             suffix.push(s);
    //         } else {
    //             break;
    //         }
    //     } else {
    //         break;
    //     }
    // }
    // trace!(
    //     "  [{} ... {}]",
    //     prefix.iter().format(" "),
    //     suffix.iter().format(" ")
    // );

    // // Disambiguate whatever is left.
    // let set: BTreeSet<_> = done
    //     .iter()
    //     .map(|d| &d[prefix.len()..d.len() - suffix.len()])
    //     .collect();
    // if set.iter().any(|&s| stack.contains(s)) {
    //     warn!("Recursion in disambiguation:");
    //     for s in &set {
    //         warn!("  {}", s.iter().format(" "));
    //     }
    //     return;
    // }
    // for s in &set {
    //     stack.insert(s.to_vec());
    // }
    // handle_conflict(ctx, set.clone(), stack);
    // for &s in &set {
    //     stack.remove(s);
    // }

    // // Find the most shallow expansion possible that produces a common prefix
    // // for all sequences.
    // let mut expansions = HashMap::<Symbol, HashMap<usize, usize>>::new();
    // for (seq_idx, seq) in seqs.iter().enumerate() {
    //     let mut leads = vec![seq[0]];
    //     for level in 0.. {
    //         for sym in std::mem::take(&mut leads) {
    //             expansions
    //                 .entry(sym)
    //                 .or_default()
    //                 .entry(seq_idx)
    //                 .or_insert(level);
    //             match sym {
    //                 Symbol::Nonterm(nt) => {
    //                     leads.extend(ctx.prods[&nt].iter().flat_map(|p| p.syms.iter().next()))
    //                 }
    //                 _ => (),
    //             }
    //         }
    //         if leads.is_empty() {
    //             break;
    //         }
    //     }
    // }
    // trace!("Expansions: {:?}", expansions);
}

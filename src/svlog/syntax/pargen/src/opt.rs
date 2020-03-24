use crate::{
    context::{format_symbols, Context, Nonterm, Production, Symbol, Term},
    factor::has_conflict,
};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Optimize the grammar.
pub fn optimize(ctx: &mut Context) -> bool {
    // Identify ambiguous rules that require factoring.
    let mut conflicts = vec![];
    for (&nt, ps) in &ctx.prods {
        if has_conflict(ctx, ps) {
            conflicts.push((nt, ctx.prods[&nt].iter().cloned().collect()));
        }
    }

    // Refactor those rules.
    for (nt, ps) in conflicts {
        optimize_conflicting(ctx, nt, ps);
    }

    false
}

/// Optimize a set of conflicting productions.
fn optimize_conflicting<'a>(
    ctx: &mut Context<'a>,
    nt: Nonterm<'a>,
    mut todo: BTreeSet<&'a Production<'a>>,
) {
    // Build a map from productions to first symbols.
    let firsts: HashMap<&Production, BTreeSet<Term>> = todo
        .iter()
        .map(|&p| (p, ctx.first_set_of_symbols(&p.syms)))
        .collect();

    // Find the smallest-sized collision groups among the productions.
    while let Some(&init) = todo.iter().next() {
        todo.remove(&init);

        // Initialize a collider set with this production and its first symbols.
        let mut colliders = BTreeSet::new();
        let mut seen = HashSet::new();
        colliders.insert(init);
        seen.extend(firsts[init].iter().cloned());

        // Process every production in the todo set. If it collides, add it to
        // the collision set. Otherwise add it back into the todo set.
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

        // Handle the collision.
        if colliders.len() > 1 {
            optimize_minimal(ctx, nt, seen, colliders);
        }
    }
}

/// Optimize a minimal-sized set of conflicting productions.
fn optimize_minimal<'a>(
    ctx: &mut Context<'a>,
    nt: Nonterm<'a>,
    ts: HashSet<Term<'a>>,
    colliders: BTreeSet<&'a Production<'a>>,
) {
    trace!("Optimize {} on {:?}:", nt, ts);
    for p in &colliders {
        trace!("  {}", p);
    }

    // Find the safe symbols, i.e. symbols that appear unconditionally in all
    // productions.
    let safe = find_safe_symbols(ctx, &colliders);
    if !safe.is_empty() {
        // trace!("  Safe: {:#?}", safe);
        let mut safe: Vec<_> = safe.into_iter().map(|(sym, exps)| (exps, sym)).collect();
        safe.sort();
        safe.dedup_by(|(exps1, _), (exps2, _)| {
            exps1
                .iter()
                .zip(exps2.iter())
                .all(|(e1, e2)| e1.subsumes(e2))
        });
        trace!("  Safe: {}", safe.iter().map(|(_, sym)| sym).format(" "));

        // Fold the expansions into a recursive expansion recipe.
        let folded = fold_expansions(&safe);
        trace!("  Folded: {:#?}", folded);

        // Apply the expansions.
        let expanded = apply_expansions(&folded);
        trace!("  Expanded:");
        for e in &expanded {
            trace!("    {}  {:?}", format_symbols(&e.syms), e.markers);
        }

        // Isolate the sections in between safe symbols into separate rules.
        let mut main_syms = vec![];
        let mut tails: Vec<_> = expanded.iter().map(|_| 0).collect();
        for (i, &safe_sym) in safe.iter().map(|(_, sym)| sym).enumerate() {
            // Gather the symbol vectors up to this point.
            // trace!("  Isolating to {}", safe_sym);
            let mut syms = BTreeSet::new();
            for (tail, exp) in tails.iter_mut().zip(expanded.iter()) {
                let pos = match exp.markers.get(i) {
                    Some(&(p, s)) if s == safe_sym => p,
                    _ => panic!("markers out of order"),
                };
                // trace!("    Handling {:?}", &exp.syms[*tail..pos]);
                syms.insert(exp.syms[*tail..pos].to_vec());
                *tail = pos + 1;
            }

            // Create a subrule if necessary.
            if syms.len() > 1 {
                let nt = ctx.anonymous_productions(syms.into_iter().collect());
                main_syms.push(nt.into());
            } else {
                main_syms.extend(syms.into_iter().next().unwrap());
            }
            main_syms.push(safe_sym);
        }

        // Add the remaining symbols.
        let mut syms = BTreeSet::new();
        for (tail, exp) in tails.iter().zip(expanded.iter()) {
            syms.insert(exp.syms[*tail..].to_vec());
        }
        if syms.len() > 1 {
            let nt = ctx.anonymous_productions(syms.into_iter().collect());
            main_syms.push(nt.into());
        } else {
            main_syms.extend(syms.into_iter().next().unwrap());
        }
        trace!("  Final: {}", format_symbols(&main_syms));

        // Replace old productions.
        for &p in &colliders {
            ctx.remove_production(p);
        }
        ctx.add_production(nt, main_syms);

        std::io::stdin().read_line(&mut String::new()).unwrap();
    }

    // // Find the minimal inlining for the colliders.
    // let inlined = find_minimal_inlining(ctx, &colliders);
    // trace!("  Inlined:");
    // for p in &inlined {
    //     trace!("    {}", format_symbols(p));
    // }

    // std::process::exit(0);

    // // Check for the special case of unexpanded nonterminals already matching.
    // let firsts: BTreeSet<_> = prods.iter().map(|p| p.syms[0]).collect();
    // let done: Vec<_> = if firsts.len() == 1 {
    //     prods.iter().map(|p| p.syms.to_vec()).collect()
    // } else {
    //     // Fully expand nonterminals in first place.
    //     #[derive(Debug, Clone)]
    //     struct Lead<'a> {
    //         parent: Option<Rc<Lead<'a>>>,
    //         syms: Vec<Symbol<'a>>,
    //     }
    //     let mut done = vec![];
    //     let mut leads: Vec<Lead<'a>> = prods
    //         .iter()
    //         .map(|p| Lead {
    //             parent: None,
    //             syms: p.syms.to_vec(),
    //         })
    //         .collect();

    //     while !leads.is_empty() {
    //         for lead in std::mem::take(&mut leads) {
    //             if lead.syms.is_empty() {
    //                 continue;
    //             }
    //             match lead.syms[0] {
    //                 Symbol::Nonterm(nt) => {
    //                     let parent = Rc::new(lead);
    //                     for p in &ctx.prods[&nt] {
    //                         leads.push(Lead {
    //                             parent: Some(parent.clone()),
    //                             syms: p
    //                                 .syms
    //                                 .iter()
    //                                 .cloned()
    //                                 .chain(parent.syms.iter().skip(1).cloned())
    //                                 .collect(),
    //                         });
    //                     }
    //                 }
    //                 _ => {
    //                     done.push(lead);
    //                 }
    //             }
    //         }
    //     }
    //     // trace!("  Fully unrolled: {:?}", done);

    //     // Step-by-step revert the expansion as long as all leads match.
    //     loop {
    //         let firsts: BTreeSet<_> = done
    //             .iter()
    //             .map(|lead| lead.parent.as_ref().map(|p| p.syms[0]))
    //             .collect();
    //         if firsts.len() == 1 && firsts.iter().next().unwrap().is_some() {
    //             for lead in std::mem::take(&mut done) {
    //                 done.push((*lead.parent.unwrap()).clone());
    //             }
    //         } else {
    //             break;
    //         }
    //     }
    //     let mut done: Vec<_> = done.into_iter().map(|lead| lead.syms).collect();
    //     done.sort();
    //     done.dedup();
    //     done
    // };

    // trace!("  Expanded:");
    // for d in &done {
    //     trace!("    {}", format_symbols(&d));
    // }

    // // No need to further disambiguate if we have only one lead.
    // if done.len() <= 1 {
    //     return;
    // }

    // // Find a common prefix, considering balanced tokens to factor out parts of
    // // the rules.
    // let mut prefix = vec![];
    // let mut offsets: Vec<usize> = done.iter().map(|_| 0).collect();
    // loop {
    //     // Find the set of next symbols in the rules.
    //     let symbols: HashSet<_> = done
    //         .iter()
    //         .zip(offsets.iter())
    //         .map(|(syms, &offset)| syms.get(offset))
    //         .collect();

    //     // Check if we have one unique prefix symbol.
    //     if symbols.len() != 1 {
    //         break;
    //     }
    //     let symbol = match symbols.into_iter().next().unwrap() {
    //         Some(&p) => p,
    //         None => break,
    //     };

    //     // If the symbol is the left of a balanced pair, advance ahead to its
    //     // counterpart and gobble up the symbols in between.
    //     prefix.push(symbol);
    //     let balanced_end = match symbol.to_string().as_str() {
    //         "'('" => ctx.lookup_symbol("')'"),
    //         "'['" => ctx.lookup_symbol("']'"),
    //         "'{'" => ctx.lookup_symbol("'}'"),
    //         _ => None,
    //     };
    //     if let Some(balanced_end) = balanced_end {
    //         trace!("    Factoring-out balanced {} {}", symbol, balanced_end);
    //         let mut subseqs = vec![];
    //         for (syms, offset) in done.iter().zip(offsets.iter_mut()) {
    //             *offset += 1;
    //             let mut subsyms = vec![];
    //             while syms[*offset] != balanced_end {
    //                 subsyms.push(syms[*offset]);
    //                 *offset += 1;
    //             }
    //             *offset += 1;
    //             subseqs.push(subsyms);
    //         }
    //         // trace!("  Gobbled up subsequences:");
    //         let aux = ctx.anonymous_nonterm();
    //         for s in subseqs {
    //             // trace!("    {}", s.iter().format(" "));
    //             ctx.add_production(aux, s);
    //         }
    //         prefix.push(Symbol::Nonterm(aux));
    //         prefix.push(balanced_end);
    //     } else {
    //         offsets.iter_mut().for_each(|o| *o += 1);
    //     }
    // }
    // trace!("  Prefix {}", format_symbols(&prefix));

    // // Compute the tails that are left over after prefix extraction.
    // let tails: BTreeSet<_> = done
    //     .iter()
    //     .zip(offsets.iter())
    //     .map(|(syms, &offset)| &syms[offset..])
    //     .collect();

    // // If there is one common tail, add that to the prefix immediately.
    // // Otherwise just go ahead and create an auxiliary nonterminal that will
    // // contain all of the tails.
    // if tails.len() == 1 {
    //     let tail = tails.into_iter().next().unwrap();
    //     if !tail.is_empty() {
    //         trace!("  Adding unique tail {}", format_symbols(tail));
    //         prefix.extend(tail);
    //     }
    // } else {
    //     let aux = ctx.anonymous_nonterm();
    //     trace!("  Adding auxiliary tail {}:", aux);
    //     prefix.push(Symbol::Nonterm(aux));
    //     for tail in tails {
    //         let p = ctx.add_production(aux, tail.to_vec());
    //         trace!("    {}", p);
    //     }
    // }

    // // Actually replace the production.
    // trace!("  Replacing:");
    // for p in &prods {
    //     trace!("    {}", p);
    //     ctx.remove_production(p);
    // }
    // trace!("  With:");
    // let p = ctx.add_production(nt, prefix);
    // trace!("    {}", p);

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
    // optimize_conflicting(ctx, set.clone(), stack);
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

type SafeSymbols<'a> = BTreeMap<Symbol<'a>, Vec<Expansion<'a>>>;

fn find_safe_symbols<'a>(
    ctx: &Context<'a>,
    prods: &BTreeSet<&'a Production<'a>>,
) -> SafeSymbols<'a> {
    find_safe_symbols_inner(ctx, prods, &mut Default::default())
}

fn find_safe_symbols_inner<'a>(
    ctx: &Context<'a>,
    prods: &BTreeSet<&'a Production<'a>>,
    visited: &mut HashSet<Nonterm<'a>>,
) -> SafeSymbols<'a> {
    let mut safe: Option<SafeSymbols> = None;
    for &prod in prods {
        let mut prod_safe = find_safe_symbols_single(ctx, prod, visited);
        safe = Some(match safe {
            Some(safe) => safe
                .into_iter()
                .flat_map(|(sym, mut exps)| {
                    prod_safe.remove(&sym).map(move |exp| {
                        exps.extend(exp);
                        (sym, exps)
                    })
                })
                .collect(),
            None => prod_safe,
        });
    }
    safe.unwrap_or_else(Default::default)
}

fn find_safe_symbols_single<'a>(
    ctx: &Context<'a>,
    prod: &'a Production<'a>,
    visited: &mut HashSet<Nonterm<'a>>,
) -> SafeSymbols<'a> {
    visited.insert(prod.nt);
    let mut safe = BTreeMap::<_, Vec<_>>::new();
    for (pos, &sym) in prod.syms.iter().enumerate() {
        safe.entry(sym).or_default().push(Expansion {
            prod,
            pos,
            exp: vec![],
        });
        if let Symbol::Nonterm(nt) = sym {
            if !visited.contains(&nt) {
                for (sym, exp) in find_safe_symbols_inner(ctx, &ctx.prods[&nt], visited) {
                    safe.entry(sym)
                        .or_default()
                        .push(Expansion { prod, pos, exp });
                }
            }
        }
    }
    visited.remove(&prod.nt);
    safe
}

/// An expansion locator.
///
/// Describes how a production shall be expanded.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct Expansion<'a> {
    pub pos: usize,
    pub exp: Vec<Expansion<'a>>,
    pub prod: &'a Production<'a>,
}

impl<'a> Expansion<'a> {
    pub fn subsumes(&self, other: &Self) -> bool {
        if self.pos != other.pos || self.prod != other.prod {
            false
        } else if !self.exp.is_empty() {
            self.exp
                .iter()
                .zip(other.exp.iter())
                .all(|(e1, e2)| e1.subsumes(e2))
        } else {
            true
        }
    }
}

fn fold_expansions<'a>(exps: &[(Vec<Expansion<'a>>, Symbol<'a>)]) -> FoldedExpansions<'a> {
    let exps: Vec<&Expansion> = exps.iter().flat_map(|(exps, _)| exps.iter()).collect();
    fold_expansions_inner(&exps)
}

fn fold_expansions_inner<'a>(exps: &[&Expansion<'a>]) -> FoldedExpansions<'a> {
    let mut grouped = HashMap::<_, BTreeMap<usize, Vec<_>>>::new();
    for exp in exps {
        grouped
            .entry(exp.prod)
            .or_default()
            .entry(exp.pos)
            .or_default()
            .extend(&exp.exp);
    }

    let mut out = BTreeMap::new();
    for (prod, pos_exps) in grouped {
        let mut v = vec![];
        for (pos, exps) in pos_exps {
            v.push(FoldedExpansion {
                pos: pos,
                exp: fold_expansions_inner(&exps),
            });
        }
        out.insert(prod, v);
    }
    out
}

#[derive(Debug)]
pub struct FoldedExpansion<'a> {
    pub pos: usize,
    pub exp: FoldedExpansions<'a>,
}

pub type FoldedExpansions<'a> = BTreeMap<&'a Production<'a>, Vec<FoldedExpansion<'a>>>;

fn apply_expansions<'a>(exps: &FoldedExpansions<'a>) -> Vec<ExpandedSymbols<'a>> {
    let mut v = vec![];
    for (prod, exps) in exps {
        v.extend(apply_expansion(prod, exps));
    }
    v
}

fn apply_expansion<'a>(
    prod: &'a Production<'a>,
    exps: &[FoldedExpansion<'a>],
) -> Vec<ExpandedSymbols<'a>> {
    let mut prefices = vec![ExpandedSymbols {
        syms: vec![],
        markers: vec![],
    }];
    let mut exps = exps.into_iter().peekable();
    for (i, &sym) in prod.syms.iter().enumerate() {
        if exps.peek().map(|e| e.pos) == Some(i) {
            let exp = exps.next().unwrap();
            if exp.exp.is_empty() {
                prefices.iter_mut().for_each(|p| {
                    p.markers.push((p.syms.len(), sym));
                    p.syms.push(sym);
                });
            } else {
                let exps = apply_expansions(&exp.exp);
                for prefix in std::mem::take(&mut prefices) {
                    for exp in &exps {
                        let mut v = prefix.clone();
                        let base = v.syms.len();
                        v.markers
                            .extend(exp.markers.iter().map(|&(p, s)| (p + base, s)));
                        v.syms.extend(&exp.syms);
                        prefices.push(v);
                    }
                }
            }
        } else {
            prefices.iter_mut().for_each(|p| p.syms.push(sym));
        }
    }
    prefices
}

#[derive(Clone)]
pub struct ExpandedSymbols<'a> {
    syms: Vec<Symbol<'a>>,
    markers: Vec<(usize, Symbol<'a>)>,
}

fn find_minimal_inlining<'a>(
    ctx: &Context<'a>,
    prods: &BTreeSet<&'a Production<'a>>,
) -> BTreeSet<Vec<Symbol<'a>>> {
    let mut out = BTreeSet::new();
    for &p in prods {
        match p.syms[0] {
            Symbol::Nonterm(nt) => {
                for mut syms in find_minimal_inlining(ctx, &ctx.prods[&nt]) {
                    syms.extend(p.syms[1..].iter().cloned());
                    out.insert(syms);
                }
            }
            _ => {
                out.insert(p.syms.clone());
            }
        }
    }
    out
}

use crate::{
    context::{format_symbols, Context, Nonterm, Production, Symbol, Term},
    factor::has_conflict,
};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Optimize the grammar.
pub fn optimize(ctx: &mut Context) -> bool {
    let mut modified = false;

    // Identify ambiguous rules that require factoring.
    let mut conflicts = vec![];
    for (&nt, ps) in &ctx.prods {
        if has_conflict(ctx, ps) {
            conflicts.push((nt, ctx.prods[&nt].iter().cloned().collect()));
        }
    }

    // Refactor those rules.
    for (nt, ps) in conflicts {
        modified |= optimize_conflicting(ctx, nt, ps);
    }

    modified
}

/// Optimize a set of conflicting productions.
fn optimize_conflicting<'a>(
    ctx: &mut Context<'a>,
    nt: Nonterm<'a>,
    mut todo: BTreeSet<&'a Production<'a>>,
) -> bool {
    let mut modified = false;

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
            modified |= optimize_minimal(ctx, nt, seen, colliders);
        }
    }

    modified
}

/// Optimize a minimal-sized set of conflicting productions.
fn optimize_minimal<'a>(
    ctx: &mut Context<'a>,
    nt: Nonterm<'a>,
    ts: HashSet<Term<'a>>,
    colliders: BTreeSet<&'a Production<'a>>,
) -> bool {
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
        // trace!("  Safe: {:#?}", safe);
        for (exps2, sym2) in std::mem::take(&mut safe) {
            if let Some((exps1, sym1)) = safe.pop() {
                if Expansion::many_subsume(&exps1, &exps2) {
                    safe.push((exps1, sym1));
                } else if Expansion::many_subsume(&exps2, &exps1) {
                    safe.push((exps2, sym2));
                } else {
                    safe.push((exps1, sym1));
                    safe.push((exps2, sym2));
                }
            } else {
                safe.push((exps2, sym2));
            }
        }
        // safe.dedup_by(|(exps1, _), (exps2, _)| Expansion::many_subsume(exps2, exps1));
        // trace!("  Safe: {:#?}", safe);
        let mut safe_syms: Vec<_> = safe.iter().map(|(_, sym)| *sym).collect();
        trace!("  Safe: {}", safe_syms.iter().format(" "));

        // Fold the expansions into a recursive expansion recipe.
        let mut folded = fold_expansions(&safe);
        // trace!("  Folded: {:#?}", folded);

        // Reduce the safe symbols to the prefix that can be produced in all
        // expansions in this order.
        let all_orders = collect_expansion_orders(&folded);
        // trace!("  All orders:");
        // for order in &all_orders {
        //     trace!("    {}", order.iter().format(" "));
        // }

        // TODO: Actually do a Levenshtein-like process here to find the minimal
        // removal of symbols to make the orders equivalent. For now we simply
        // prefix-strip the orders.
        let mut leads: Vec<_> = all_orders.iter().map(|syms| syms.as_slice()).collect();
        for required_sym in std::mem::take(&mut safe_syms) {
            let all = leads.iter_mut().all(|syms| {
                while let Some(&sym) = syms.first() {
                    if sym == required_sym {
                        return true;
                    }
                    *syms = &syms[1..];
                }
                false
            });
            if !all {
                break;
            }
            safe_syms.push(required_sym);
        }
        assert!(
            safe_syms.len() > 0,
            "at least one symbol must be present in all expansions; all expansions {:?}",
            all_orders
        );
        trace!("  Safe (filtered): {}", safe_syms.iter().format(" "));

        // Enforce the symbol order of `safe_syms` on the folded expansions.
        // This is necessary since these may contain multiple expansions for the
        // same symbol, and we only ever want to expand symbols in a very
        // specific order.
        enforce_expansion_order(&mut folded, &safe_syms);
        // trace!("  Enforced Order: {:#?}", folded);

        // Apply the expansions.
        let expanded = apply_expansions(&folded);
        trace!("  Expanded:");
        for e in &expanded {
            trace!("    {}  {:?}", format_symbols(&e.syms), e.markers);
        }

        // Isolate the sections in between safe symbols into separate rules.
        let mut main_syms = vec![];
        let mut tails: Vec<_> = expanded.iter().map(|_| 0).collect();
        for (i, &safe_sym) in safe_syms.iter().enumerate() {
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
        return true;
    }

    // Find the minimal inlining for the colliders.
    if let Some(inlined) = find_minimal_inlining(ctx, &colliders) {
        // for p in &inlined {
        //     trace!("    {}", format_symbols(p));
        // }
        trace!("  Inlined:");
        for syms in inlined {
            let p = ctx.add_production(nt, syms);
            trace!("    {}", p);
        }
        for &p in &colliders {
            ctx.remove_production(p);
        }
        return true;
    }

    // Otherwise just give up.
    warn!("Cannot resolve {} conflict on {:?}", nt, ts);
    for p in &colliders {
        warn!("  {}", p);
    }
    false
}

type SafeSymbols<'a> = BTreeMap<Symbol<'a>, Vec<Expansion<'a>>>;

fn find_safe_symbols<'a>(
    ctx: &Context<'a>,
    prods: &BTreeSet<&'a Production<'a>>,
) -> SafeSymbols<'a> {
    find_safe_symbols_inner(ctx, prods, &mut Default::default(), &mut Default::default())
}

fn find_safe_symbols_inner<'a>(
    ctx: &Context<'a>,
    prods: &BTreeSet<&'a Production<'a>>,
    visited: &mut HashSet<Nonterm<'a>>,
    cache: &mut HashMap<&'a Production<'a>, SafeSymbols<'a>>,
) -> SafeSymbols<'a> {
    let mut safe: Option<SafeSymbols> = None;
    for &prod in prods {
        let mut prod_safe = find_safe_symbols_single(ctx, prod, visited, cache);
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
    cache: &mut HashMap<&'a Production<'a>, SafeSymbols<'a>>,
) -> SafeSymbols<'a> {
    if let Some(safe) = cache.get(&prod) {
        return safe.clone();
    }
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
                for (sym, exp) in find_safe_symbols_inner(ctx, &ctx.prods[&nt], visited, cache) {
                    safe.entry(sym)
                        .or_default()
                        .push(Expansion { prod, pos, exp });
                }
            }
        }
    }
    visited.remove(&prod.nt);
    cache.insert(prod, safe.clone());
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
    pub fn many_subsume(exps1: &[Self], exps2: &[Self]) -> bool {
        // trace!("Many subsume: {:#?} and {:#?}", exps1, exps2);
        for exp in exps1 {
            let mut found = false;
            for exp2 in exps2 {
                if exp.pos == exp2.pos && exp.prod == exp2.prod {
                    found = exp.subsumes(exp2);
                    break;
                }
            }
            if !found {
                // trace!("Does not subsume: {:#?} and {:#?}", exp, exps2);
                return false;
            }
        }
        true
    }

    pub fn subsumes(&self, other: &Self) -> bool {
        if self.pos != other.pos || self.prod != other.prod {
            false
        } else if !self.exp.is_empty() {
            Self::many_subsume(&self.exp, &other.exp)
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

fn collect_expansion_orders<'a>(input: &FoldedExpansions<'a>) -> Vec<Vec<Symbol<'a>>> {
    let mut leads = vec![];
    for (prod, exp) in input {
        leads.extend(collect_expansion_orders_vec(prod, exp));
    }
    leads
}

fn collect_expansion_orders_vec<'a>(
    prod: &'a Production<'a>,
    input: &[FoldedExpansion<'a>],
) -> Vec<Vec<Symbol<'a>>> {
    let mut leads = vec![vec![]];
    for exp in input {
        if exp.exp.is_empty() {
            leads
                .iter_mut()
                .for_each(|lead| lead.push(prod.syms[exp.pos]));
        } else {
            let map = collect_expansion_orders(&exp.exp);
            for lead in std::mem::take(&mut leads) {
                for syms in &map {
                    let mut lead = lead.clone();
                    lead.extend(syms);
                    leads.push(lead);
                }
            }
        }
    }
    leads
}

fn enforce_expansion_order<'a>(input: &mut FoldedExpansions<'a>, order: &[Symbol<'a>]) {
    // trace!("Enforcing order {:?}", order);
    let consumed = enforce_expansion_order_map(input, order);
    assert_eq!(
        consumed,
        order.len(),
        "order enforcing did not consume all symbols"
    );
}

fn enforce_expansion_order_map<'a>(
    input: &mut FoldedExpansions<'a>,
    order: &[Symbol<'a>],
) -> usize {
    let mut consumed = BTreeSet::new();
    for (prod, exps) in input {
        consumed.insert(enforce_expansion_order_vec(prod, exps, order));
    }
    if consumed.len() != 1 {
        panic!(
            "order enforcing consumed uneven number of symbols: {:?}",
            consumed
        );
    }
    consumed.into_iter().next().unwrap()
}

fn enforce_expansion_order_vec<'a>(
    prod: &'a Production<'a>,
    input: &mut Vec<FoldedExpansion<'a>>,
    order: &[Symbol<'a>],
) -> usize {
    let mut pos = 0;
    for mut exp in std::mem::take(input) {
        // Drop expansions which are out of order.
        if exp.exp.is_empty() {
            if Some(&prod.syms[exp.pos]) == order.get(pos) {
                pos += 1;
                input.push(exp);
                // } else {
                //     trace!("Dropping {:#?}", exp);
            }
            continue;
        }

        // Recursively filter out the inner expansions.
        pos += enforce_expansion_order_map(&mut exp.exp, &order[pos..]);

        // If that made this expansion empty, drop it entirely.
        if !exp.exp.values().all(|v| v.is_empty()) {
            input.push(exp);
            // } else {
            //     trace!("Dropping {:#?}", exp);
        }
    }
    pos
}

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
) -> Option<BTreeSet<Vec<Symbol<'a>>>> {
    find_minimal_inlining_inner(ctx, prods, &mut Default::default())
}

fn find_minimal_inlining_inner<'a>(
    ctx: &Context<'a>,
    prods: &BTreeSet<&'a Production<'a>>,
    seen: &mut HashSet<Nonterm<'a>>,
) -> Option<BTreeSet<Vec<Symbol<'a>>>> {
    let mut out = BTreeSet::new();
    for &p in prods {
        match p.syms.first() {
            Some(&Symbol::Nonterm(nt)) => {
                if seen.insert(nt) {
                    for mut syms in find_minimal_inlining_inner(ctx, &ctx.prods[&nt], seen)? {
                        syms.extend(p.syms[1..].iter().cloned());
                        out.insert(syms);
                    }
                    seen.remove(&nt);
                } else {
                    return None;
                }
            }
            _ => {
                out.insert(p.syms.clone());
            }
        }
    }
    Some(out)
}

use crate::context::{Context, LlTable, Nonterm, Production, Symbol, Term};
use std::collections::BTreeSet;

/// Populate a context with an LL(1) table.
pub fn build_ll(ctx: &mut Context) {
    info!("Constructing LL(1) table");
    let mut table = Default::default();
    for (&nt, prods) in &ctx.prods {
        for p in prods {
            for t in ctx.first_set_of_symbols(&p.syms) {
                add_action(&mut table, nt, t, p);
            }
            if ctx.symbols_expand_to_epsilon(&p.syms) {
                // trace!("Adding follow set {}", nt);
                for t in ctx.follow_set(nt) {
                    add_action(&mut table, nt, t, p);
                }
            }
        }
    }
    ctx.ll_table = table;
}

fn add_action<'a>(table: &mut LlTable<'a>, nt: Nonterm<'a>, term: Term<'a>, p: &'a Production<'a>) {
    table
        .entry(nt)
        .or_default()
        .entry(term)
        .or_default()
        .insert(p);
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
        for (_, ps) in ts {
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

pub fn dump_ambiguities(ctx: &Context) {
    for (_, prods) in &ctx.ll_table {
        for (&t, ps) in prods {
            if ps.len() > 1 {
                trace!("Ambiguity on {}:", t);
                for p in ps {
                    trace!("  {}", p);
                }
            }
        }
    }
}

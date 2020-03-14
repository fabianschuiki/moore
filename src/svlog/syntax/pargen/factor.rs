use crate::context::{Context, LlTable, Nonterm, Production, Symbol, Term};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

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
            trace!("Conflict in {}", nt);
            for p in ps {
                trace!("  {}", p);
            }
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

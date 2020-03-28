use crate::{
    ast,
    context::{Context, Symbol},
};
use std::collections::HashMap;

/// Populate a context with a parsed grammar AST.
pub fn add_ast(ctx: &mut Context, ast: ast::Grammar) {
    info!("Adding grammar with {} NTs to context", ast.nts.len());

    // Register the nonterminal names.
    for nt in &ast.nts {
        let nonterm = ctx.intern_nonterm(&nt.name);
        if nt.public {
            ctx.root_nonterms.insert(nonterm);
            info!("Root nonterminal {}", nonterm);
        }
        trace!("Declared nonterm {}", nonterm);
    }

    // Populate the productions.
    let mut cache = Cache::new();
    for nt in &ast.nts {
        let nonterm = ctx.intern_nonterm(&nt.name);
        let prods = nt
            .choices
            .iter()
            .map(|syms| map_symbols(ctx, syms, &mut cache))
            .collect();
        ctx.set_productions(nonterm, prods);
    }
}

type Cache<'ast, 'ctx> = HashMap<&'ast ast::Symbol, Symbol<'ctx>>;

fn map_symbols<'ast, 'ctx>(
    ctx: &mut Context<'ctx>,
    syms: &'ast [ast::Symbol],
    cache: &mut Cache<'ast, 'ctx>,
) -> Vec<Symbol<'ctx>> {
    let mut output = vec![];
    for sym in syms {
        output.push(map_symbol(ctx, sym, cache));
    }
    output
}

fn map_symbol<'ast, 'ctx>(
    ctx: &mut Context<'ctx>,
    sym: &'ast ast::Symbol,
    cache: &mut Cache<'ast, 'ctx>,
) -> Symbol<'ctx> {
    if let Some(&sym) = cache.get(&sym) {
        return sym;
    }
    let out = match sym {
        ast::Symbol::Token(name) => ctx
            .lookup_symbol(name)
            .unwrap_or_else(|| ctx.intern_term(name).into()),
        ast::Symbol::Group(syms) => {
            let syms = map_symbols(ctx, syms, cache);
            let nonterm = ctx.anonymous_productions(vec![syms]);
            nonterm.into()
        }
        ast::Symbol::Choice(choices) => {
            let prods = choices
                .into_iter()
                .map(|syms| map_symbols(ctx, syms, cache))
                .collect();
            let nonterm = ctx.anonymous_productions(prods);
            nonterm.into()
        }
        ast::Symbol::Maybe(sym) => {
            let inner = map_symbol(ctx, sym, cache);
            let outer = ctx.anonymous_productions(vec![vec![], vec![inner]]);
            outer.into()
        }
        ast::Symbol::Any(sym) => {
            let inner = map_symbol(ctx, sym, cache);
            let outer_some =
                ctx.anonymous_productions(vec![vec![inner], vec![Symbol::This, inner]]);
            let outer_any = ctx.anonymous_productions(vec![vec![outer_some.into()], vec![]]);
            outer_any.into()
        }
        ast::Symbol::Some(sym) => {
            let inner = map_symbol(ctx, sym, cache);
            let outer = ctx.anonymous_productions(vec![vec![inner], vec![Symbol::This, inner]]);
            outer.into()
        }
        ast::Symbol::Not(sym) => map_symbol(ctx, sym, cache),
    };
    cache.insert(sym, out);
    out
}

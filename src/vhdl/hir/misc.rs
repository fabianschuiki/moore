// Copyright (c) 2018 Fabian Schuiki

use std;

use crate::hir::prelude::*;

pub fn apply_use_clauses<'a, I>(clauses: I, context: AllocContext)
where
    I: IntoIterator<Item = &'a ast::CompoundName>,
{
    for u in clauses.into_iter() {
        let e = apply_use_clause(u, context);
        std::mem::forget(e);
    }
}

fn apply_use_clause(clause: &ast::CompoundName, context: AllocContext) -> Result<()> {
    debugln!("apply use {}", clause.span.extract());

    // Lookup the primary name.
    let pn = ResolvableName::from_primary_name(&clause.primary, context)?;
    let mut lookup = context.resolve(pn.value, true);
    let mut lookup_name = pn;
    if lookup.is_empty() {
        context.emit(DiagBuilder2::error(format!("`{}` is unknown", pn.value)).span(pn.span));
        return Err(());
    }
    // debugln!("`{}` resolved to {:?}", pn.value, lookup);

    // Process the name parts.
    for part in &clause.parts {
        // Ensure the name is unique.
        if lookup.len() > 1 {
            let mut d = DiagBuilder2::error(format!("`{}` is ambiguous", lookup_name.value))
                .span(lookup_name.span)
                .add_note("Refers to the following:");
            for l in lookup {
                d = d.span(l.span);
            }
            context.emit(d);
            return Err(());
        }
        let def = lookup.into_iter().next().unwrap();
        let scope = match def.value {
            Def2::Lib(x) => x.scope(),
            Def2::Pkg(x) => x.poll()?.scope(),
            _ => {
                context.emit(DiagBuilder2::error(format!("cannot select into {}", def.value.desc_kind())).span(def.span));
                return Err(());
            }
        };

        // Perform the operation that the name part requests.
        match *part {
            ast::NamePart::Select(ref primary) => {
                lookup_name = ResolvableName::from_primary_name(primary, context)?;
                lookup = scope.resolve(lookup_name.value, false);
                // debugln!("`{}` resolved to {:?}", lookup_name.value, lookup);
                if lookup.is_empty() {
                    context.emit(DiagBuilder2::error(format!("`{}` is unknown", lookup_name.value)).span(lookup_name.span));
                    return Err(());
                }
            }
            ast::NamePart::SelectAll(..) => {
                context.import_scope(scope)?;
                return Ok(());
            }
            _ => {
                context.emit(DiagBuilder2::error(format!("`{}` cannot be used", clause.span.extract())).span(clause.span));
                return Err(());
            }
        }
    }

    debugln!("`{}` resolved to {:?}", clause.span.extract(), lookup);
    for l in lookup {
        context.import_def(lookup_name.value, l)?;
    }
    Ok(())
}

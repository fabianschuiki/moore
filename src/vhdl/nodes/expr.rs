// Copyright (c) 2018 Fabian Schuiki

//! Expressions

use std::collections::HashMap;

use common::Verbosity;
use common::errors::*;
use common::source::{Span, Spanned};
use common::score::Result;
use common::name::Name;

use add_ctx::AddContext;
use syntax::ast;
use score::*;
use term::TermContext;
use make_ctx::MakeContext;
use hir;
use typeck::TypeckContext;
use ty::*;

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add an expression.
    pub fn add_expr(&self, expr: &'ast ast::Expr) -> Result<ExprRef> {
        let (mk, _id, scope) = self.make::<ExprRef>(expr.span);
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = TermContext::new(sbc, scope);
            let term = ctx.termify_expr(expr)?;
            ctx.term_to_expr_raw(term)
        }));
        self.schedule_expr(&mk);
        Ok(mk.finish())
    }

    /// Add an expression already lowered to HIR.
    pub fn add_expr_hir(&self, hir: hir::Expr) -> Result<ExprRef> {
        let (mk, _, _) = self.make::<ExprRef>(hir.span);
        mk.set_hir(hir);
        self.schedule_expr(&mk);
        Ok(mk.finish())
    }

    /// Schedule expression tasks.
    pub fn schedule_expr(&self, mk: &MakeContext<ExprRef>) {
        let id = mk.id;
        mk.typeval(Box::new(move |tyc|{
            let hir = tyc.ctx.lazy_hir(id)?;
            let tyctx = tyc.ctx.type_context_resolved(id)?;
            if tyc.ctx.sess.opts.verbosity.contains(Verbosity::TYPE_CONTEXTS) {
                let msg = match tyctx {
                    Some(t) => format!("type context of expression `{}` is {}", hir.span.extract(), t),
                    None => format!("no type context for expression `{}`", hir.span.extract()),
                };
                tyc.emit(
                    DiagBuilder2::note(msg)
                    .span(hir.span)
                );
            }
            let ty = typeval_expr(tyc, id, hir, tyctx)?;
            if tyc.ctx.sess.opts.verbosity.contains(Verbosity::EXPR_TYPES) {
                tyc.emit(
                    DiagBuilder2::note(format!("type of expression `{}` is {}", hir.span.extract(), ty))
                    .span(hir.span)
                );
            }
            Ok(ty)
        }));
    }

    /// Add a list of choices.
    pub fn add_choices<I>(
        &self,
        ast: Spanned<I>
    ) -> Result<Spanned<hir::Choices>>
        where I: IntoIterator<Item=&'ast ast::Expr>
    {
        let ctx = TermContext::new(self.ctx, self.scope);
        let choices = ast.value
            .into_iter()
            .map(|ast|{
                let term = ctx.termify_expr(ast)?;
                ctx.term_to_choice(term)
            })
            .collect::<Vec<Result<_>>>()
            .into_iter()
            .collect::<Result<Vec<_>>>()?;
        Ok(Spanned::new(choices, ast.span))
    }

    /// Add a discrete range.
    pub fn add_discrete_range(&self, ast: &'ast ast::Expr) -> Result<Spanned<hir::DiscreteRange>> {
        let ctx = TermContext::new(self.ctx, self.scope);
        let term = ctx.termify_expr(ast)?;
        ctx.term_to_discrete_range(term)
    }

    /// Add an aggregate already lowered to HIR.
    pub fn add_aggregate_hir(&self, hir: hir::Aggregate) -> Result<AggregateRef> {
        let (mk, _, _) = self.make::<AggregateRef>(hir.span);
        mk.set_hir(hir);
        self.schedule_aggregate(&mk);
        Ok(mk.finish())
    }

    /// Schedule aggregate tasks.
    pub fn schedule_aggregate(&self, mk: &MakeContext<AggregateRef>) {
        let id = mk.id;
        mk.typeval(Box::new(move |tyc|{
            let hir = tyc.ctx.lazy_hir(id)?;
            let tyctx = tyc.ctx.type_context_resolved(id)?;
            if tyc.ctx.sess.opts.verbosity.contains(Verbosity::TYPE_CONTEXTS) {
                let msg = match tyctx {
                    Some(t) => format!("type context of aggregate `{}` is {}", hir.span.extract(), t),
                    None => format!("no type context for aggregate `{}`", hir.span.extract()),
                };
                tyc.emit(
                    DiagBuilder2::note(msg)
                    .span(hir.span)
                );
            }

            // // Determine whether this is a record or an array aggregate. This is
            // // either evident from the aggregate itself, or must be determined
            // // from context.
            // match (&hir.named, tyctx) {
            //     (&hir::AggregateKind::Record(..), _) => return typeval_record_aggregate(tyc, id, hir, tyctx),
            //     (&hir::AggregateKind::Array(..), _) => return typeval_array_aggregate(tyc, id, hir, tyctx),
            //     (&hir::AggregateKind::Both, Some(tyctx)) => {
            //         let tyctx_flat = tyc.ctx.deref_named_type(tyctx)?;
            //         match *tyctx_flat {
            //             Ty::Record(..) => return typeval_record_aggregate(tyc, id, hir, Some(tyctx)),
            //             Ty::Array(..) => return typeval_array_aggregate(tyc, id, hir, Some(tyctx)),
            //             _ => ()
            //         }
            //     }
            //     _ => ()
            // }

            // For now, directly determine the aggregate type from the context.
            // The above can be fleshed out and re-enabled later.
            if let Some(tyctx) = tyctx {
                let tyctx_flat = tyc.ctx.deref_named_type(tyctx)?;
                match *tyctx_flat {
                    Ty::Record(..) => return typeval_record_aggregate(tyc, id, hir, tyctx),
                    Ty::Array(..) => return typeval_array_aggregate(tyc, id, hir, tyctx),
                    _ => (),
                }
            }
            tyc.emit(
                DiagBuilder2::error(format!("type of aggregate `{}` cannot be inferred from context", hir.span.extract()))
                .span(hir.span)
            );
            debugln!("Aggregate kind is {:?}", hir.named);
            debugln!("Type context is {:?}", tyctx);
            Err(())
        }));
    }
}

/// Evaluate the type of an expression.
pub fn typeval_expr<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb>(
    tyc: &TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx>,
    expr_id: ExprRef,
    hir: &hir::Expr,
    tyctx: Option<&'ctx Ty>,
) -> Result<&'ctx Ty> {
    match hir.data {
        hir::ExprData::ConstName(id)  => tyc.ctx.lazy_typeval(id),
        hir::ExprData::SignalName(id) => tyc.ctx.ty(id),
        hir::ExprData::VarName(id)    => tyc.ctx.lazy_typeval(id),
        hir::ExprData::FileName(id)   => tyc.ctx.lazy_typeval(id),
        hir::ExprData::EnumName(ref defs) => {
            // Enums are generally overloaded. The type context is needed to
            // pick one of the available variants.
            assert!(!defs.is_empty());
            if defs.len() == 1 {
                Ok(tyc.ctx.intern_ty(EnumTy::new(defs[0].value.0)))
            } else {
                let filtered: Vec<_> = if let Some(tyctx) = tyctx {
                    let tyctx_flat = tyc.ctx.deref_named_type(tyctx)?;
                    match *tyctx_flat {
                        Ty::Enum(ref et) => defs
                            .iter()
                            .filter_map(|def|
                                if def.value.0 == et.decl {
                                    Some(def.value.0)
                                } else {
                                    None
                                }
                            ).collect(),
                        _ => vec![],
                    }
                } else {
                    vec![]
                };
                if filtered.len() != 1 {
                    tyc.emit(
                        DiagBuilder2::error(format!("`{}` is ambiguous", hir.span.extract()))
                        .span(hir.span)
                        // TODO: Show which definitions are available.
                    );
                    Err(())
                } else {
                    Ok(tyc.ctx.intern_ty(EnumTy::new(filtered[0])))
                }
            }
        }
        hir::ExprData::StringLiteral(ref defs) => {
            // String literals work pretty much the same as enums. This overload
            // resolution code can probably be shared, but I'm too lazy to do
            // that now.
            assert!(!defs.is_empty());
            if defs.len() == 1 {
                let index_ty = IntTy::new(Dir::To, 0.into(), (defs[0].1.len()-1).into()).into();
                let index = ArrayIndex::Constrained(Box::new(index_ty));
                Ok(tyc.ctx.intern_ty(ArrayTy::new(vec![index], Box::new(EnumTy::new(defs[0].0).into()))))
            } else {
                let (index_ty, filtered): (Option<_>, Vec<_>) = if let Some(tyctx) = tyctx {
                    let tyctx_flat = tyc.ctx.deref_named_type(tyctx)?;
                    match *tyctx_flat {
                        Ty::Array(ref at) if at.indices.len() == 1 => {
                            let index_ty = match *at.indices[0].ty() {
                                Ty::Int(ref it) => Some(it.clone()),
                                _ => None,
                            };
                            match *at.element.as_ref() {
                                Ty::Enum(ref et) => (index_ty, defs
                                    .iter()
                                    .filter_map(|def|
                                        if def.0 == et.decl {
                                            Some(def.0)
                                        } else {
                                            None
                                        }
                                    ).collect()),
                                _ => (index_ty, vec![]),
                            }
                        }
                        _ => (None, vec![]),
                    }
                } else {
                    (None, vec![])
                };
                let index_ty = index_ty.unwrap_or_else(||
                    IntTy::new(Dir::To, 0.into(), (defs[0].1.len()-1).into())).into();
                if filtered.len() != 1 {
                    tyc.emit(
                        DiagBuilder2::error(format!("`{}` is ambiguous", hir.span.extract()))
                        .span(hir.span)
                        // TODO: Show which definitions are available.
                    );
                    return Err(());
                } else {
                    let index = ArrayIndex::Constrained(Box::new(index_ty));
                    Ok(tyc.ctx.intern_ty(ArrayTy::new(vec![index], Box::new(EnumTy::new(filtered[0]).into()))))
                }
            }
        }
        hir::ExprData::IntegerLiteral(ref value) => {
            // Integer literals either have a type attached, or they inherit
            // their type from the context.
            if let Some(ref ty) = value.ty {
                return Ok(tyc.ctx.intern_ty(ty.clone()));
            }
            if let Some(ty) = tyctx {
                if let &Ty::Int(_) = tyc.ctx.deref_named_type(ty)? {
                    return Ok(ty);
                }
            }
            tyc.emit(
                DiagBuilder2::error(format!("type of expression `{}` cannot be inferred from context", hir.span.extract()))
                .span(hir.span)
            );
            Err(())
        }
        hir::ExprData::Qualified(ref tm, expr) => {
            let ty = tyc.ctx.intern_ty(Ty::Named(tm.span, tm.value));
            let _expr_ty = tyc.lazy_typeval(expr)?;
            // TODO: Check types.
            Ok(ty)
        }
        hir::ExprData::Allocator(ref tm, expr) => {
            let ty = tyc.ctx.intern_ty(Ty::Named(tm.span, tm.value));
            if let Some(expr) = expr {
                let _expr_ty = tyc.lazy_typeval(expr)?;
                // TODO: Check types.
            }
            Ok(ty)
        }
        hir::ExprData::Cast(ref tm, expr) => {
            let ty = tyc.ctx.intern_ty(Ty::Named(tm.span, tm.value));
            let _expr_ty = tyc.lazy_typeval(expr)?;
            // TODO: Check that the cast is actually possible.
            Ok(ty)
        }
        hir::ExprData::Aggregate(id) => {
            tyc.ctx.set_type_context(id, TypeCtx::Inherit(expr_id.into()));
            tyc.ctx.lazy_typeval(id)
        }
        _ => {
            tyc.emit(
                DiagBuilder2::bug(format!("typeval for expression `{}` not implemented", hir.span.extract()))
                .span(hir.span)
            );
            debugln!("It is a {:#?}", hir.data);
            Err(())
        }
    }
}

/// Evaluate the type of a record aggregate.
pub fn typeval_record_aggregate<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb>(
    tyc: &TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx>,
    id: AggregateRef,
    hir: &hir::Aggregate,
    tyctx: &'ctx Ty,
) -> Result<&'ctx Ty> {
    let tyctx_flat = tyc.ctx.deref_named_type(tyctx)?;
    let record_ty = if let Ty::Record(ref ty) = *tyctx_flat {
        ty
    } else {
        unreachable!();
    };

    // Make sure the aggregate does not have more fields than the record.
    if hir.positional.len() > record_ty.fields.len() {
        tyc.emit(
            DiagBuilder2::error(format!("aggregate `{}` has {} fields, but record `{}` only has {}", hir.span.extract(), hir.positional.len(), tyctx, record_ty.fields.len()))
            .span(hir.span)
        );
        return Err(());
    }

    // Build a correspondence map between the fields of the aggregate and the
    // fields of the record type.
    let mut had_fails = false;
    #[derive(Copy, Clone, Debug)]
    enum FieldIndex { Pos(usize), Named(usize), Others };
    let mut mapping = HashMap::<usize, FieldIndex>::new();
    let mut occupied = HashMap::<Name, Span>::new();
    for (index, &pos) in hir.positional.iter().enumerate() {
        mapping.insert(index, FieldIndex::Pos(index));
        occupied.insert(record_ty.fields[index].0, pos.span);
    }
    match hir.named {
        hir::AggregateKind::Both => (),
        hir::AggregateKind::Record(ref fields) => {
            for (agg_index, field) in fields.iter().enumerate() {
                for choice in &field.value.0 {
                    // Lookup the field name in the record type.
                    let type_index = match record_ty.lookup.get(&choice.value) {
                        Some(&i) => i,
                        None => {
                            tyc.emit(
                                DiagBuilder2::error(format!("`{}` is not a field of {}", choice.value, tyctx))
                                .span(choice.span)
                            );
                            had_fails = true;
                            continue;
                        }
                    };

                    // Make sure it has not been mapped yet.
                    if let Some(existing) = occupied.insert(choice.value, choice.span) {
                        tyc.emit(
                            DiagBuilder2::error(format!("`{}` assigned multiple times", choice.value))
                            .span(choice.span)
                            .add_note("Previous assignment was here:")
                            .span(existing)
                        );
                        had_fails = true;
                    }

                    // Keep track of the assignment.
                    mapping.insert(type_index, FieldIndex::Named(agg_index));
                }
            }
        },
        hir::AggregateKind::Array(..) => {
            tyc.emit(
                DiagBuilder2::error("expected a record aggregate, found an array aggregate")
                .span(hir.span)
            );
            return Err(());
        }
    }
    if let Some(others) = hir.others {
        let indices: Vec<_> = (0..record_ty.fields.len())
            .filter(|i| !mapping.contains_key(i))
            .collect();
        for type_index in indices {
            mapping.insert(type_index, FieldIndex::Others);
        }
    }
    debugln!("aggregate: record type mapping {:?}", mapping);

    // Forward the type context and check the type of elements.
    for (&type_index, &agg_index) in &mapping {
        match (||{
            let ty = record_ty.fields[type_index].1.as_ref();
            match agg_index {
                FieldIndex::Pos(index) => {
                    let id = hir.positional[index].value;
                    tyc.ctx.set_type_context(id, ty);
                    let _ty = tyc.lazy_typeval(id)?;
                    // TODO: Check type.
                }
                FieldIndex::Named(index) => {
                    let id = hir.named.get(index).value;
                    tyc.ctx.set_type_context(id, ty);
                    let _ty = tyc.lazy_typeval(id)?;
                    // TODO: Check type.
                }
                FieldIndex::Others => {
                    let id = hir.others.unwrap().value;
                    tyc.ctx.set_type_context(id, ty);
                    let _ty = tyc.lazy_typeval(id)?;
                    // TODO: Check type.
                }
            }
            Ok(())
        })() {
            Ok(()) => (),
            Err(()) => had_fails = true,
        }
    }

    if had_fails {
        Err(())
    } else {
        Ok(tyctx)
    }
}

/// Evaluate the type of an array aggregate.
pub fn typeval_array_aggregate<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb>(
    tyc: &TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx>,
    id: AggregateRef,
    hir: &hir::Aggregate,
    tyctx: &'ctx Ty,
) -> Result<&'ctx Ty> {
    let tyctx_flat = tyc.ctx.deref_named_type(tyctx)?;

    // Determine the index and element types from the context.
    let (index, element) = if let Ty::Array(ref ty) = *tyctx_flat {
        let index = ty.indices[0].ty();
        let element = if ty.indices.len() > 1 {
            tyc.ctx.intern_ty(ArrayTy::new(
                ty.indices.iter().skip(1).cloned().collect(),
                ty.element.clone()
            ))
        } else {
            ty.element.as_ref()
        };
        (index, element)
    } else {
        unreachable!();
    };

    // Forward the type context and check the index and element types.
    let mut had_fails = false;
    for &pos in &hir.positional {
        match (||{
            tyc.ctx.set_type_context(pos.value, element);
            let _ty = tyc.lazy_typeval(pos.value)?;
            // TODO: Check type.
            Ok(())
        })() {
            Ok(()) => (),
            Err(()) => had_fails = true,
        }
    }
    match hir.named {
        hir::AggregateKind::Both => (),
        hir::AggregateKind::Array(ref fields) => {
            for field in fields {
                match typeck_array_aggregate_element(tyc, field, index, element) {
                    Ok(()) => (),
                    Err(()) => had_fails = true,
                }
            }
        },
        hir::AggregateKind::Record(..) => {
            tyc.emit(
                DiagBuilder2::error("expected an array aggregate, found a record aggregate")
                .span(hir.span)
            );
            return Err(());
        }
    }
    if let Some(others) = hir.others {
        match (||{
            tyc.ctx.set_type_context(others.value, element);
            let ty = tyc.lazy_typeval(others.value)?;
            // TODO: Check type.
            Ok(())
        })() {
            Ok(()) => (),
            Err(()) => had_fails = true,
        }
    }
    if had_fails {
        Err(())
    } else {
        Ok(tyctx)
    }
}

/// Check the type of an array aggregate element.
pub fn typeck_array_aggregate_element<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb>(
    tyc: &TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx>,
    hir: &Spanned<(hir::ArrayChoices, Spanned<ExprRef>)>,
    index_ty: &'ctx Ty,
    element_ty: &'ctx Ty,
) -> Result<()> {
    let mut had_fails = false;
    for choice in &hir.value.0 {
        match typeck_array_aggregate_choice(tyc, choice, index_ty) {
            Ok(()) => (),
            Err(()) => had_fails = true,
        }
    }
    tyc.ctx.set_type_context(hir.value.1.value, element_ty);
    let _ty = tyc.lazy_typeval(hir.value.1.value)?;
    // TODO: Check type.
    if had_fails {
        Err(())
    } else {
        Ok(())
    }
}

/// Check the type of an array aggregate choice.
pub fn typeck_array_aggregate_choice<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb>(
    tyc: &TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx>,
    hir: &Spanned<hir::ArrayChoice>,
    index_ty: &'ctx Ty,
) -> Result<()> {
    match hir.value {
        hir::ArrayChoice::Expr(expr_id) => {
            tyc.ctx.set_type_context(expr_id, index_ty);
            let _ty = tyc.lazy_typeval(expr_id)?;
            // TODO: Check type.
        }
        hir::ArrayChoice::DiscreteRange(hir::DiscreteRange::Subtype(subtype_id)) => {
            let _ty = tyc.lazy_typeval(subtype_id)?;
            // TODO: Check type.
        }
        hir::ArrayChoice::DiscreteRange(hir::DiscreteRange::Range(ref range)) => {
            // TODO: Check type.
        }
    }
    Ok(())
}

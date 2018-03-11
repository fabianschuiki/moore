// Copyright (c) 2018 Fabian Schuiki

//! Overload resolution for subprograms and enum literals.

#![deny(missing_docs)]

use std::collections::HashMap;

use common::name::Name;
use common::errors::*;
use common::source::{Spanned, Span};
use common::score::Result;

use score::{ScoreContext, Def};
use ty::Ty;

/// A type requirement on an overloaded entity.
///
/// To perform overload resolution, an overload requirement is imposed on a set
/// of definitions. All definitions that match are returned.
#[derive(Debug)]
pub enum OverloadReq<'ctx> {
    /// Definitions must resolve to an enum of the given type.
    Enum(TypeReq<'ctx>),
    /// Definitions must resolve to a subprogram that satisfies the given
    /// signature.
    Subprog(SignatureReq<'ctx>),
}

/// A signature requirement on an overloaded entity.
#[derive(Debug)]
pub struct SignatureReq<'ctx> {
    /// The required return type.
    pub return_type: TypeReq<'ctx>,
    /// The required type of the positional arguments.
    pub positional: Vec<TypeReq<'ctx>>,
    /// The required type of the named arguments.
    pub named: HashMap<Name, TypeReq<'ctx>>,
}

/// A type requirement on an overloaded entity.
#[derive(Debug)]
pub enum TypeReq<'ctx> {
    /// Matches any type.
    Any,
    /// Matches one specific type.
    One(&'ctx Ty),
    /// Matches several specific types.
    Many(Vec<&'ctx Ty>),
}

impl<'ctx> Default for TypeReq<'ctx> {
    fn default() -> TypeReq<'ctx> {
        TypeReq::Any
    }
}

/// Reduce overloaded definitions.
pub fn reduce_overloads(ctx: &ScoreContext, defs: &[Spanned<Def>], req: &OverloadReq, span: Span) -> Result<Vec<Spanned<Def>>> {
    debugln!("resolving overloaded {:?} with requirement {:?}", defs, req);

    // Filter the definitions by kind such that only those remain which have any
    // chance of applying to the requirement.
    let filtered: Vec<_> = defs.iter().enumerate().filter(|&(_, def)| match (def.value, req) {
        (Def::Enum(..), &OverloadReq::Enum(..)) => true,
        (Def::BuiltinOp(..), &OverloadReq::Subprog(..)) => true,
        (Def::Subprog(..), &OverloadReq::Subprog(..)) => true,
        _ => false,
    }).collect();
    debugln!("reduced to matching kind {:?}", filtered);
    if filtered.is_empty() {
        return Ok(vec![]);
    }

    // Determine the type of the applicable definitions.
    let types = filtered
        .iter()
        .map(|&(i, def)| Ok((i, match def.value {
            Def::Enum(id)      => ctx.lazy_typeval(id)?,
            Def::BuiltinOp(id) => ctx.lazy_typeval(id)?,
            Def::Subprog(id)   => ctx.lazy_typeval(id)?,
            _ => unreachable!(),
        })))
        .collect::<Vec<Result<_>>>()
        .into_iter()
        .collect::<Result<Vec<_>>>()?;
    debugln!("type of definitions {:?}", types);

    // Match each of the types against the requirement.

    ctx.emit(
        DiagBuilder2::bug("overload resolution not implemented")
        .span(span)
    );
    Err(())
}

/// Resolve overloaded definitions to exactly one unambiguous definition.
pub fn resolve_overloads(ctx: &ScoreContext, defs: &[Spanned<Def>], req: &OverloadReq, span: Span) -> Result<Spanned<Def>> {
    let reduced = reduce_overloads(ctx, defs, req, span)?;
    if reduced.is_empty() {
        ctx.emit(
            DiagBuilder2::error("no overload applies")
            .span(span)
            // TODO: Show available implementations.
        );
        debugln!("available definitions: {:?}", defs);
        Err(())
    } else if reduced.len() > 1 {
        ctx.emit(
            DiagBuilder2::error(format!("`{}` is ambiguous", span.extract()))
            .span(span)
            // TODO: Show implementations that matched.
        );
        debugln!("matching definitions: {:?}", reduced);
        Err(())
    } else {
        Ok(reduced.into_iter().next().unwrap())
    }
}

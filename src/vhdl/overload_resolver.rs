// Copyright (c) 2018 Fabian Schuiki

//! Overload resolution for subprograms and enum literals.

#![deny(missing_docs)]

use std::collections::{HashMap, HashSet};

use crate::common::name::Name;
use crate::common::errors::*;
use crate::common::source::{Spanned, Span};
use crate::common::score::Result;

use crate::score::{ScoreContext, Def};
use crate::ty::Ty;

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

impl<'ctx> OverloadReq<'ctx> {
    /// Check if a type matches this requirement.
    pub fn matches(&self, ty: &Ty) -> bool {
        match *self {
            OverloadReq::Enum(ref req)    => req.matches(ty),
            OverloadReq::Subprog(ref req) => req.matches(ty),
        }
    }
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

impl<'ctx> SignatureReq<'ctx> {
    /// Check if a type matches this requirement.
    pub fn matches(&self, ty: &Ty) -> bool {
        if let Ty::Subprog(ref ty) = *ty {
            if !self.return_type.is_any() && !ty.ret.as_ref().map(|t| self.return_type.matches(t)).unwrap_or(false) {
                debugln!("return type mismatch: {} vs {:?}", ty, self);
                return false;
            }
            if self.positional.len() > ty.args.len() {
                debugln!("positional length mismatch: {} vs {:?}", ty, self);
                return false;
            }
            let mut arg_iter = ty.args.iter();
            for req in &self.positional {
                let arg = arg_iter.next().unwrap(); // never fails due to above check
                if !req.matches(&arg.ty) {
                    debugln!("positional mismatch: {} vs {:?} in {} vs {:?}", arg.ty, req, ty, self);
                    return false;
                }
            }
            let mut unhandled_names: HashSet<_> = self.named.keys().collect();
            for arg in arg_iter {
                let name = match arg.name {
                    Some(name) => name,
                    None => {
                        debugln!("unhandled positional arg: {} in {} vs {:?}", arg.ty, ty, self);
                        return false
                    },
                };
                let req = match self.named.get(&name) {
                    Some(req) => req,
                    None => {
                        debugln!("unknown named arg: {} in {} vs {:?}", name, ty, self);
                        return false
                    },
                };
                if !req.matches(&arg.ty) {
                    debugln!("named mismatch `{}`: {} vs {:?} in {} vs {:?}", name, arg.ty, req, ty, self);
                    return false;
                }
                unhandled_names.remove(&name);
            }
            unhandled_names.is_empty()
        } else {
            false
        }
    }
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

impl<'ctx> TypeReq<'ctx> {
    /// Check if this type requirement matches any type.
    pub fn is_any(&self) -> bool {
        match *self {
            TypeReq::Any => true,
            _ => false,
        }
    }

    /// Check if a type matches this requirement.
    pub fn matches(&self, ty: &Ty) -> bool {
        match *self {
            TypeReq::Any => true,
            TypeReq::One(req) => are_types_matching(req, ty),
            TypeReq::Many(ref reqs) => reqs.iter().any(|&req| are_types_matching(req, ty)),
        }
    }
}

impl<'ctx> Default for TypeReq<'ctx> {
    fn default() -> TypeReq<'ctx> {
        TypeReq::Any
    }
}

/// Check if two types match.
fn are_types_matching(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (&Ty::Named(_, ia), &Ty::Named(_, ib)) => ia == ib,
        (a, b) => a == b,
    }
}

/// Reduce overloaded definitions.
pub fn reduce_overloads(ctx: &ScoreContext, defs: &[Spanned<Def>], req: &OverloadReq, _span: Span) -> Result<Vec<Spanned<Def>>> {
    debugln!("resolving overloaded {:?} with requirement {:?}", defs, req);

    // Filter the definitions by kind such that only those remain which have any
    // chance of applying to the requirement.
    let filtered: Vec<_> = defs.iter().enumerate().filter(|&(_, def)| match (def.value, req) {
        (Def::Enum(..), &OverloadReq::Enum(..)) => true,
        (Def::BuiltinOp(..), &OverloadReq::Subprog(..)) => true,
        (Def::Subprog(..), &OverloadReq::Subprog(..)) => true,
        _ => false,
    }).collect();
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

    // Match each of the types against the requirement.
    let matched = types
        .into_iter()
        .filter_map(|(i, ty)| if req.matches(ty) { Some(defs[i]) } else { None })
        .collect();

    Ok(matched)
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
        debugln!("available definitions: {:#?}", defs);
        Err(())
    } else if reduced.len() > 1 {
        ctx.emit(
            DiagBuilder2::error(format!("`{}` is ambiguous", span.extract()))
            .span(span)
            // TODO: Show implementations that matched.
        );
        debugln!("matching definitions: {:#?}", reduced);
        Err(())
    } else {
        Ok(reduced.into_iter().next().unwrap())
    }
}

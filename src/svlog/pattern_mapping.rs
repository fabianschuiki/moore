// Copyright (c) 2016-2020 Fabian Schuiki

//! A mapping from a pattern expression's arguments to the underlying type's
//! fields.

use crate::crate_prelude::*;
use crate::{hir::HirNode, value::ValueKind};
use num::cast::ToPrimitive;
use std::{collections::HashMap, sync::Arc};

/// A mapping of the indices/members of a pattern's type to an expression.
#[derive(Clone, Debug)]
pub struct PatternMapping<'a> {
    /// The corresponding pattern expression.
    pub hir: &'a hir::Expr,
    /// The type the pattern maps to.
    pub ty: &'a ty::UnpackedType<'a>,
    /// The mapped expression for each field. The fields are in type order.
    /// Multiple fields may be assigned the same expression.
    pub fields: Vec<(PatternField<'a>, &'a hir::Expr)>,
}

/// A field correspondence in a mapped pattern.
///
/// This enum further details the kind of field an expression is mapped to. The
/// indices of the corresponding field are implied by the position of the
/// `PatternField` within the `fields` vector.
#[derive(Copy, Clone, Debug)]
pub enum PatternField<'a> {
    /// The expression is assigned to a single bit of the given type.
    Bit(ty::SbvType),
    /// The expression is assigned to an array element of the given type.
    Array(&'a ty::UnpackedType<'a>),
    /// The expression is assigned to the given struct member.
    Struct(&'a ty::StructMember<'a>),
}

impl<'a> PatternField<'a> {
    /// Determine the type of the underlying field.
    pub fn ty(&self, cx: &impl ty::TypeContext<'a>) -> &'a ty::UnpackedType<'a> {
        match self {
            Self::Bit(sbv) => sbv.to_unpacked(cx),
            Self::Array(ty) => ty,
            Self::Struct(m) => m.ty,
        }
    }
}

/// Determine the mapping of a named or positional `'{...}` pattern.
#[moore_derive::query]
pub(crate) fn map_pattern<'a>(
    cx: &impl Context<'a>,
    Ref(expr): Ref<'a, hir::Expr>,
    env: ParamEnv,
) -> Result<Arc<PatternMapping<'a>>> {
    // First determine the type the pattern will have.
    let ty = cx.need_type_context(expr.id, env);
    if ty.is_error() {
        return Err(());
    }
    let ty = ty.ty();

    // Then handle the different pattern styles.
    let fields = match expr.kind {
        hir::ExprKind::PositionalPattern(ref mapping) => {
            map_positional_pattern(cx, mapping, 1, ty, expr.span)?
        }
        hir::ExprKind::RepeatPattern(count, ref mapping) => {
            let const_count = cx.constant_int_value_of(count, env)?;
            let const_count = match const_count.to_usize() {
                Some(c) => c,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "repetition count {} is outside copable range",
                            const_count,
                        ))
                        .span(cx.span(count)),
                    );
                    return Err(());
                }
            };
            map_positional_pattern(cx, mapping, const_count, ty, expr.span)?
        }
        hir::ExprKind::NamedPattern(ref mapping) => {
            if let Some(dim) = ty.outermost_dim() {
                map_named_array_pattern(cx, mapping, ty, dim, expr.span, env)?
            } else if let Some(strukt) = ty.get_struct() {
                map_named_struct_pattern(cx, mapping, strukt, expr.span, env)?
            } else {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "cannot construct a value of type `{}` with `'{{...}}`",
                        ty
                    ))
                    .span(expr.span)
                    .add_note("Named patterns can only construct arrays or structs."),
                );
                return Err(());
            }
        }
        _ => bug_span!(expr.span, cx, "expression is not a pattern"),
    };

    // Assemble the full mapping information.
    Ok(Arc::new(PatternMapping {
        hir: expr,
        ty,
        fields,
    }))
}

/// Helper function to get the HIR expr associated with a node ID. This should
/// eventually go into the HIR module.
fn hir_of_expr<'a>(cx: &impl Context<'a>, node: NodeId) -> Result<&'a hir::Expr> {
    match cx.hir_of(node)? {
        HirNode::Expr(e) => Ok(e),
        x => unreachable!("expected HIR expression, got {:?}", x),
    }
}

/// Determine the mapping of a named `'{...}` array pattern.
fn map_named_array_pattern<'a>(
    cx: &impl Context<'a>,
    mapping: &[(hir::PatternMapping, NodeId)],
    ty: &'a ty::UnpackedType<'a>,
    dim: ty::Dim<'a>,
    span: Span,
    env: ParamEnv,
) -> Result<Vec<(PatternField<'a>, &'a hir::Expr)>> {
    // Determine the length of the array and the offset of the indexes.
    let (length, offset) = match dim
        .get_range()
        .map(|r| (r.size, r.offset))
        .or_else(|| dim.get_size().map(|s| (s, 0)))
    {
        Some(x) => x,
        None => bug_span!(
            span,
            cx,
            "array pattern with invalid input dimension `{}`",
            dim
        ),
    };

    // Determine the element type.
    let elem_ty = ty.pop_dim(cx).unwrap();

    // Map things.
    let mut failed = false;
    let mut default: Option<&hir::Expr> = None;
    let mut values = HashMap::<usize, (PatternField, &hir::Expr)>::new();

    for &(map, to) in mapping {
        let to = match hir_of_expr(cx, to) {
            Ok(h) => h,
            _ => {
                failed = true;
                continue;
            }
        };
        match map {
            hir::PatternMapping::Type(type_id) => {
                cx.emit(
                    DiagBuilder2::error("types cannot index into an array").span(cx.span(type_id)),
                );
                continue;
            }
            hir::PatternMapping::Member(member_id) => {
                // Determine the index for the mapping.
                let index = match || -> Result<usize> {
                    let index = cx.constant_value_of(member_id, env)?;
                    let index = match &index.kind {
                        ValueKind::Int(i, ..) => i - num::BigInt::from(offset),
                        _ => {
                            cx.emit(
                                DiagBuilder2::error("array index must be a constant integer")
                                    .span(cx.span(member_id)),
                            );
                            return Err(());
                        }
                    };
                    let index = match index.to_isize() {
                        Some(i) if i >= 0 && i < length as isize => i as usize,
                        _ => {
                            cx.emit(
                                DiagBuilder2::error(format!("index `{}` out of bounds", index))
                                    .span(cx.span(member_id)),
                            );
                            return Err(());
                        }
                    };
                    Ok(index)
                }() {
                    Ok(i) => i,
                    Err(_) => {
                        failed = true;
                        continue;
                    }
                };

                // Determine the value and insert into the mappings.
                let entry = (PatternField::Array(elem_ty), to);
                if let Some((_, prev)) = values.insert(index, entry) {
                    cx.emit(
                        DiagBuilder2::warning(format!(
                            "`{}` overwrites previous value `{}` at index {}",
                            to.span.extract(),
                            prev.span.extract(),
                            index
                        ))
                        .span(to.span)
                        .add_note("Previous value was here:")
                        .span(prev.span),
                    );
                }
            }
            hir::PatternMapping::Default => match default {
                Some(ref default) => {
                    cx.emit(
                        DiagBuilder2::error("pattern has multiple default mappings")
                            .span(to.span)
                            .add_note("Previous default mapping was here:")
                            .span(default.span),
                    );
                    failed = true;
                    continue;
                }
                None => {
                    default = Some(to);
                }
            },
        }
    }

    // In case the list of indices provided by the user is incomplete, use the
    // default to fill in the other elements.
    let values: Vec<_> = if values.len() != length {
        let default = if let Some(default) = default {
            default
        } else {
            cx.emit(
                DiagBuilder2::error("`default:` missing in non-exhaustive array pattern")
                    .span(span)
                    .add_note("Array patterns must assign a value to every index."),
            );
            return Err(());
        };
        (0..length)
            .map(|i| {
                values
                    .get(&i)
                    .copied()
                    .unwrap_or((PatternField::Array(elem_ty), default))
            })
            .collect()
    } else {
        (0..length).map(|i| values[&i]).collect()
    };

    if failed {
        Err(())
    } else {
        Ok(values)
    }
}

/// Determine the mapping of a named `'{...}` struct pattern.
fn map_named_struct_pattern<'a>(
    cx: &impl Context<'a>,
    mapping: &[(hir::PatternMapping, NodeId)],
    strukt: &'a ty::StructType<'a>,
    span: Span,
    env: ParamEnv,
) -> Result<Vec<(PatternField<'a>, &'a hir::Expr)>> {
    // Determine the field names and types for the struct to be assembled.
    let name_lookup: HashMap<Name, usize> = strukt
        .members
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.value, i))
        .collect();

    // Disassemble the user's mapping into actual field bindings and defaults.
    let mut failed = false;
    let mut default: Option<&hir::Expr> = None;
    let mut type_defaults = HashMap::<&ty::UnpackedType, &hir::Expr>::new();
    let mut values = HashMap::<usize, (PatternField, &hir::Expr)>::new();

    for &(map, to) in mapping {
        let to = match hir_of_expr(cx, to) {
            Ok(h) => h,
            _ => {
                failed = true;
                continue;
            }
        };
        match map {
            hir::PatternMapping::Type(type_id) => {
                let ty = cx.packed_type_from_ast(
                    Ref(cx.ast_for_id(type_id).as_all().get_type().unwrap()),
                    env,
                    None,
                );
                if ty.is_error() {
                    failed = true;
                    continue;
                }
                type_defaults.insert(ty.resolve_full(), to);
            }
            hir::PatternMapping::Member(member_id) => match cx.hir_of(member_id) {
                Ok(HirNode::Expr(&hir::Expr {
                    kind: hir::ExprKind::Ident(name),
                    ..
                })) => {
                    // Determine the index for the mapping.
                    let index = match name_lookup.get(&name.value) {
                        Some(&index) => index,
                        None => {
                            cx.emit(
                                DiagBuilder2::error(format!("`{}` member does not exist", name))
                                    .span(name.span)
                                    .add_note("Struct definition was here:")
                                    .span(strukt.ast.span()),
                            );
                            failed = true;
                            continue;
                        }
                    };

                    // Determine the value and insert into the mappings.
                    let entry = (PatternField::Struct(&strukt.members[index]), to);
                    if let Some((_, prev)) = values.insert(index, entry) {
                        cx.emit(
                            DiagBuilder2::warning(format!(
                                "`{}` overwrites previous value `{}` for member `{}`",
                                to.span.extract(),
                                prev.span.extract(),
                                name
                            ))
                            .span(to.span)
                            .add_note("Previous value was here:")
                            .span(prev.span),
                        );
                    }
                }
                Ok(_) => {
                    let span = cx.span(member_id);
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "`{}` is not a valid struct member name",
                            span.extract()
                        ))
                        .span(span),
                    );
                    failed = true;
                    continue;
                }
                Err(()) => {
                    failed = true;
                    continue;
                }
            },
            hir::PatternMapping::Default => match default {
                Some(default) => {
                    cx.emit(
                        DiagBuilder2::error("pattern has multiple default mappings")
                            .span(to.span)
                            .add_note("Previous mapping default mapping was here:")
                            .span(default.span),
                    );
                    failed = true;
                    continue;
                }
                None => {
                    default = Some(to);
                }
            },
        }
    }

    // In case the list of members provided by the user is incomplete, use the
    // defaults to fill in the other members.
    for (index, field) in strukt.members.iter().enumerate() {
        if values.contains_key(&index) {
            continue;
        }

        // Try the type-based defaults first.
        if let Some(default) = type_defaults.get(field.ty.resolve_full()) {
            trace!(
                "applying type default to member `{}`: {:?}",
                field.name,
                default
            );
            values.insert(index, (PatternField::Struct(field), default));
            continue;
        }

        // Try to assign a default value.
        let default = if let Some(default) = default {
            default
        } else {
            cx.emit(
                DiagBuilder2::error(format!("`{}` member missing in struct pattern", field.name))
                    .span(span)
                    .add_note("Struct patterns must assign a value to every member."),
            );
            failed = true;
            continue;
        };

        values.insert(index, (PatternField::Struct(field), default));
    }

    if failed {
        Err(())
    } else {
        Ok((0..values.len()).map(|i| values[&i]).collect())
    }
}

/// Determine the mapping of a positional `'{...}` pattern.
fn map_positional_pattern<'a>(
    cx: &impl Context<'a>,
    mapping: &[NodeId],
    repeat: usize,
    ty: &'a ty::UnpackedType<'a>,
    span: Span,
) -> Result<Vec<(PatternField<'a>, &'a hir::Expr)>> {
    // Lower each of the values to HIR, and abort on errors.
    let values: Result<Vec<_>> = mapping.iter().map(|&id| hir_of_expr(cx, id)).collect();
    let values = values?;
    let len = values.len() * repeat;
    let values: Vec<_> = values.into_iter().cycle().take(len).collect();

    // Find a mapping for the values.
    let (exp_len, result) = if ty.coalesces_to_llhd_scalar() {
        let sbv = ty.simple_bit_vector(cx, span);
        let bit = sbv.change_size(1);
        (
            sbv.size,
            values
                .into_iter()
                .rev()
                .map(|v| (PatternField::Bit(bit), v))
                .collect(),
        )
    } else if let Some(dim) = ty.outermost_dim() {
        let elem_ty = ty.pop_dim(cx).unwrap();
        match dim.get_size() {
            Some(size) => (
                size,
                values
                    .into_iter()
                    .map(|v| (PatternField::Array(elem_ty), v))
                    .collect(),
            ),
            None => {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "value of type `{}` cannot be constructed with a pattern; dimension `{}` \
                         has no fixed size",
                        ty, dim,
                    ))
                    .span(span),
                );
                return Err(());
            }
        }
    } else if let Some(strukt) = ty.get_struct() {
        (
            strukt.members.len(),
            values
                .into_iter()
                .enumerate()
                .flat_map(|(i, v)| match strukt.members.get(i) {
                    Some(f) => Some((PatternField::Struct(f), v)),
                    None => None,
                })
                .collect(),
        )
    } else {
        bug_span!(span, cx, "positional pattern with invalid type `{}`", ty)
    };

    // Ensure that the number of values matches the array/struct definition.
    if exp_len != len {
        cx.emit(
            DiagBuilder2::error(format!(
                "pattern has {} fields, but type `{}` requires {}",
                len, ty, exp_len
            ))
            .span(span),
        );
        return Err(());
    }

    Ok(result)
}

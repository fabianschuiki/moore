// Copyright (c) 2016-2021 Fabian Schuiki

//! Lvalue expressions
//!
//! An MIR representation for all expressions that may appear on the left-hand
//! side of an assignment.

use crate::crate_prelude::*;
use crate::{
    mir::{
        print::{Context, Print},
        rvalue::Rvalue,
        visit::{AcceptVisitor, Visitor, WalkVisitor},
    },
    ty::UnpackedType,
    ParamEnv,
};
use std::fmt::Write;

/// An lvalue expression.
#[moore_derive::visit_without_foreach]
#[derive(Clone, Eq, PartialEq)]
pub struct Lvalue<'a> {
    /// A unique id.
    pub id: NodeId,
    /// The expression node which spawned this lvalue.
    pub origin: NodeId,
    /// The environment within which the lvalue lives.
    pub env: ParamEnv,
    /// The span in the source file where the lvalue originates from.
    pub span: Span,
    /// The type of the expression.
    pub ty: &'a UnpackedType<'a>,
    /// The expression data.
    pub kind: LvalueKind<'a>,
}

impl<'a> Lvalue<'a> {
    /// Check whether the lvalue represents a lowering error tombstone.
    pub fn is_error(&self) -> bool {
        self.ty.is_error() || self.kind.is_error()
    }

    /// Get the `Intf` nested within `Index`, if one exists.
    pub fn get_intf(&self) -> Option<NodeId> {
        match self.kind {
            mir::LvalueKind::Index { value, .. } => value.get_intf(),
            mir::LvalueKind::Intf(intf) => Some(intf),
            _ => None,
        }
    }
}

impl<'a> std::fmt::Debug for Lvalue<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.print(f)
    }
}

impl<'a> Print for Lvalue<'a> {
    fn print_context(
        &self,
        outer: &mut impl Write,
        inner: &mut impl Write,
        ctx: &mut Context,
    ) -> std::fmt::Result {
        write!(inner, "Lvalue ")?;
        match self.kind {
            LvalueKind::Transmute(v) => write!(inner, "Transmute({})", ctx.print(outer, v))?,
            LvalueKind::DestructArray(ref args) => write!(
                inner,
                "DestructArray({})",
                ctx.print_comma_separated(outer, args),
            )?,
            LvalueKind::DestructStruct(ref args) => write!(
                inner,
                "DestructStruct({})",
                ctx.print_comma_separated(outer, args),
            )?,
            LvalueKind::Genvar(arg) => write!(inner, "Genvar({:?})", arg)?,
            LvalueKind::Var(arg) => write!(inner, "Var({:?})", arg)?,
            LvalueKind::Port(arg) => write!(inner, "Port({:?})", arg)?,
            LvalueKind::Arg(arg) => write!(inner, "Arg({:?})", arg)?,
            LvalueKind::Intf(arg) => write!(inner, "Intf({:?})", arg)?,
            LvalueKind::IntfSignal(arg, sig) => {
                write!(inner, "IntfSignal({}, {:?})", ctx.print(outer, arg), sig)?
            }
            LvalueKind::Index {
                value,
                base,
                length,
            } => {
                if length == 0 {
                    write!(
                        inner,
                        "{}[{}]",
                        ctx.print(outer, value),
                        ctx.print(outer, base),
                    )?
                } else {
                    write!(
                        inner,
                        "{}[{}+:{}]",
                        ctx.print(outer, value),
                        ctx.print(outer, base),
                        length,
                    )?
                }
            }
            LvalueKind::Member { value, field } => {
                write!(inner, "{}.{}", ctx.print(outer, value), field)?
            }
            LvalueKind::Concat(ref args) => {
                write!(inner, "Concat({})", ctx.print_comma_separated(outer, args))?
            }
            LvalueKind::Repeat(num, arg) => {
                write!(inner, "Repeat({} x {})", num, ctx.print(outer, arg))?
            }
            LvalueKind::Error => write!(inner, "<error>")?,
        }
        write!(inner, " : {}", self.ty)?;
        Ok(())
    }
}

/// The different forms an lvalue expression may take.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum LvalueKind<'a> {
    /// A type cast which does not incur any operation. For example, going from
    /// `bit [31:0]` to `int`, or vice versa.
    Transmute(&'a Lvalue<'a>),
    /// Destructor for an array.
    DestructArray(Vec<&'a Lvalue<'a>>),
    /// Destructor for a struct.
    DestructStruct(Vec<&'a Lvalue<'a>>),
    /// A reference to a genvar declaration.
    Genvar(NodeId),
    /// A reference to a variable declaration.
    Var(NodeId),
    /// A reference to a port declaration.
    Port(NodeId),
    /// A reference to a subroutine argument.
    Arg(NodeId),
    /// A reference to an interface.
    Intf(NodeId),
    /// A reference to an interface's signal.
    IntfSignal(&'a Lvalue<'a>, NodeId),
    /// A bit- or part-select.
    Index {
        value: &'a Lvalue<'a>,
        base: &'a Rvalue<'a>,
        length: usize,
    },
    /// A struct field access.
    Member { value: &'a Lvalue<'a>, field: usize },
    /// Concatenate multiple values.
    ///
    /// The values are cast to and treated as packed bit vectors, and the result
    /// is yet another packed bit vector. The lowest index corresponds to the
    /// left-most item in the concatenation, which is at the MSB end of the
    /// final packed bit vector.
    Concat(Vec<&'a Lvalue<'a>>),
    /// Repeat a value multiple times.
    ///
    /// The value is cast to and treated as a packed bit vector, and the result
    /// is yet another packed bit vector.
    Repeat(usize, &'a Lvalue<'a>),
    /// An error occurred during lowering.
    Error,
}

impl<'a> LvalueKind<'a> {
    /// Check whether the lvalue represents a lowering error tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            LvalueKind::Error => true,
            _ => false,
        }
    }
}

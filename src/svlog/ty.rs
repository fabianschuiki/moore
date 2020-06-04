// Copyright (c) 2016-2020 Fabian Schuiki

//! A generalized SystemVerilog type system.
//!
//! This module covers all types that may arise in a SystemVerilog source file,
//! plus some additional things like modules/interfaces to streamline the
//! handling of hierarchical names and interface signals/modports throughout the
//! compiler.
//!
//! ## Packed Types
//!
//! Packed types are the core types of SystemVerilog. They combine a core packed
//! type with an optional sign and zero or more packed dimensions. The core
//! packed types are:
//!
//! - Integer vector types: `bit`, `logic`, `reg`
//! - Integer atom types: `byte`, `shortint`, `int`, `longint`, `integer`,
//!   `time`
//! - Packed structs and unions
//! - Enums
//! - Packed named types
//! - Packed type references
//!
//! The packed dimensions can be:
//!
//! - Unsized (`[]`)
//! - Ranges (`[x:y]`)
//!
//! Packed types are implemented by the [`PackedType`](struct.PackedType.html)
//! struct.
//!
//! ## Unpacked Types
//!
//! Unpacked types are a second level of types in SystemVerilog. They extend a
//! core unpacked type with a variety of unpacked dimensions, depending on which
//! syntactic construct generated the type (variable or otherwise). The core
//! unpacked types are:
//!
//! - Packed types
//! - Non-integer types: `shortreal`, `real`, `realtime`
//! - Unpacked structs and unions
//! - `string`, `chandle`, `event`
//! - Virtual interfaces
//! - Class types
//! - Covergroups
//! - Unpacked named types
//! - Unpacked type references
//! - Modules and interfaces
//!
//! The unpacked dimensions are:
//!
//! - Unsized (`[]`)
//! - Arrays (`[x]`)
//! - Ranges (`[x:y]`)
//! - Associative (`[T]` or `[*]`)
//! - Queues (`[$]` or `[$:x]`)
//!
//! Unpacked types are implemented by the [`UnpackedType`](struct.UnpackedType.html)
//! struct.
//!
//! ## Simple Bit Vector Types
//!
//! Some packed types may be converted into an equivalent Simple Bit Vector Type
//! (SBVT), which has an identical bit pattern as the original type, but
//! consists only of an integer vector type with a single optional packed
//! dimension. An SBVT can be converted back into a packed type. SBVTs can be
//! range-cast, which changes the width of their single dimension.
//!
//! SBVTs track whether the original packed type explicitly had a dimension or
//! used an integer atom type, or was named. When converting back to a packed
//! type, the SBVT attempts to restore this information, depending on how many
//! changes were applied.
//!
//! ## Sign
//!
//! All packed types have an associated sign, indicating whether they are
//! *signed* or *unsigned*. The types have a default sign, which means that
//! the sign may have been omitted in the source file. Packed types can be
//! sign-cast, which changes only their sign.
//!
//! ## Domain
//!
//! All packed types consist of bits that can either carry two or four values.
//! An aggregate type is two-valued iff *all* its constituent types are
//! two-valued, otherwise it is four-valued. Packed types can be domain-cast,
//! which changes only their value domain.

use crate::crate_prelude::*;
use crate::{ast_map::AstNode, common::arenas::TypedArena, hir::HirNode, ParamEnv};
use once_cell::sync::Lazy;
use std::{
    cell::RefCell,
    collections::HashSet,
    fmt::{self, Display, Formatter},
};

/// A packed type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PackedType<'a> {
    /// The core packed type.
    pub core: PackedCore<'a>,
    /// The type sign.
    pub sign: Sign,
    /// Whether the sign was explicit in the source code.
    pub sign_explicit: bool,
    /// The packed dimensions.
    pub dims: Vec<PackedDim>,
    /// This type with one level of name/reference resolved.
    resolved: Option<&'a Self>,
    /// This type with all names/references recursively resolved.
    resolved_full: Option<&'a Self>,
}

/// A core packed type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PackedCore<'a> {
    /// An error occurred during type computation.
    Error,
    /// Void.
    Void,
    /// An integer vector type.
    IntVec(IntVecType),
    /// An integer atom type.
    IntAtom(IntAtomType),
    /// A packed struct.
    Struct(StructType<'a>),
    /// An enum.
    Enum(EnumType<'a>),
    /// A named type.
    Named {
        /// How the user originally called the type.
        name: Spanned<Name>,
        /// The type this name expands to.
        ty: &'a PackedType<'a>,
    },
    /// A type reference.
    Ref {
        /// Location of the `type(...)` in the source file.
        span: Span,
        /// The type that this reference expands to.
        ty: &'a PackedType<'a>,
    },
}

/// A packed dimension.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PackedDim {
    /// A range dimension, like `[a:b]`.
    Range(Range),
    /// A unsized dimension, like `[]`.
    Unsized,
}

/// An integer vector type.
///
/// These are the builtin single-bit integer types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntVecType {
    /// A `bit`.
    Bit,
    /// A `logic`.
    Logic,
    /// A `reg`.
    Reg,
}

/// An integer atom type.
///
/// These are the builtin multi-bit integer types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntAtomType {
    /// A `byte`.
    Byte,
    /// A `shortint`.
    ShortInt,
    /// An `int`.
    Int,
    /// A `longint`.
    LongInt,
    /// An `integer`.
    Integer,
    /// A `time`.
    Time,
}

/// An unpacked type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnpackedType<'a> {
    /// The core unpacked type.
    pub core: UnpackedCore<'a>,
    /// The unpacked dimensions.
    pub dims: Vec<UnpackedDim<'a>>,
    /// This type with one level of name/reference resolved.
    resolved: Option<&'a Self>,
    /// This type with all names/references recursively resolved.
    resolved_full: Option<&'a Self>,
}

/// A core unpacked type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnpackedCore<'a> {
    /// An error occurred during type computation.
    Error,
    /// A packed type.
    Packed(&'a PackedType<'a>),
    /// A real type.
    Real(RealType),
    /// A unpacked struct.
    Struct(StructType<'a>),
    /// A string.
    String,
    /// A chandle.
    Chandle,
    /// An event.
    Event,
    // TODO: Add virtual interfaces
    // TODO: Add class types
    // TODO: Add covergroups
    /// A named type.
    Named {
        /// How the user originally called the type.
        name: Spanned<Name>,
        /// The type this name expands to.
        ty: &'a UnpackedType<'a>,
    },
    /// A type reference.
    Ref {
        /// Location of the `type(...)` in the source file.
        span: Span,
        /// The type that this reference expands to.
        ty: &'a UnpackedType<'a>,
    },
    // TODO: Add modules
    // TODO: Add interfaces
}

/// An unpacked dimension.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnpackedDim<'a> {
    /// A unsized dimension, like `[]`.
    Unsized,
    /// An array dimension, like `[a]`.
    Array(usize),
    /// A range dimension, like `[a:b]`.
    Range(Range),
    /// An associative dimension, like `[T]` or `[*]`.
    Assoc(Option<&'a UnpackedType<'a>>),
    /// A queue dimension, like `[$]` or `[$:a]`.
    Queue(Option<usize>),
}

/// A real type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RealType {
    /// A `shortreal`.
    ShortReal,
    /// A `real`.
    Real,
    /// A `realtime`.
    RealTime,
}

/// A struct type.
///
/// This represents both packed and unpacked structs. Which one it is depends on
/// whether this struct is embedded in a `PackedType` or `UnpackedType`. For the
/// packed version the struct inherits its sign from its parent `PackedType`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructType<'a> {
    /// The corresponding AST node of this struct definition.
    pub ast: &'a ast::Struct<'a>,
    /// The AST node of the corresponding type.
    pub ast_type: &'a ast::Type<'a>,
    /// Whether this is a `struct`, `union` or `union tagged`.
    pub kind: ast::StructKind,
    /// The list of members.
    pub members: Vec<StructMember<'a>>,
    /// The param env where this struct was declared, to recover the legacy
    /// type.
    pub legacy_env: ParamEnv,
}

/// A member of a struct type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructMember<'a> {
    /// The name.
    pub name: Spanned<Name>,
    /// The type.
    pub ty: &'a UnpackedType<'a>,
    /// The AST node of the member declaration.
    pub ast_member: &'a ast::StructMember<'a>,
    /// The AST node of the member name.
    pub ast_name: &'a ast::VarDeclName<'a>,
}

/// An enum type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumType<'a> {
    /// The corresponding AST node of this enum definition.
    pub ast: &'a ast::Enum<'a>,
    /// The base type of this enum.
    pub base: &'a PackedType<'a>,
    /// Whether the base type was explicit in the source code.
    pub base_explicit: bool,
    /// The list of variants.
    pub variants: Vec<(Spanned<Name>, &'a ast::EnumName<'a>)>,
}

/// A simple bit vector type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SbvType {
    /// The domain, which dictates whether this is a `bit` or `logic` vector.
    pub domain: Domain,
    /// Whether the type used an integer atom like `int` in the source text.
    pub used_atom: bool,
    /// The sign.
    pub sign: Sign,
    /// Whether the sign was explicit in the source text.
    pub sign_explicit: bool,
    /// The size of the vector.
    pub size: usize,
    /// Whether the single-bit vector had an explicit range in the source text.
    /// Essentially whether it was `bit` or `bit[a:a]`.
    pub size_explicit: bool,
}

/// A packed or unpacked dimension.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dim<'a> {
    /// A packed dimension.
    Packed(PackedDim),
    /// An unpacked dimension.
    Unpacked(UnpackedDim<'a>),
}

impl<'a> PackedType<'a> {
    /// Create a new type with default sign and no packed dimensions.
    ///
    /// This creates the type on the stack. In general you will want to use the
    /// `make_*` functions to create a type that is interned into a context.
    pub fn new(core: impl Into<PackedCore<'a>>) -> Self {
        Self::with_dims(core, vec![])
    }

    /// Create a new type with default sign and packed dimensions.
    ///
    /// This creates the type on the stack. In general you will want to use the
    /// `make_*` functions to create a type that is interned into a context.
    pub fn with_dims(core: impl Into<PackedCore<'a>>, dims: Vec<PackedDim>) -> Self {
        let core = core.into();
        let sign = match &core {
            PackedCore::IntAtom(IntAtomType::Time)
            | PackedCore::IntVec(_)
            | PackedCore::Error
            | PackedCore::Void
            | PackedCore::Struct(_)
            | PackedCore::Enum(_)
            | PackedCore::Named { .. }
            | PackedCore::Ref { .. } => Sign::Unsigned,
            PackedCore::IntAtom(_) => Sign::Signed,
        };
        Self::with_sign_and_dims(core, sign, false, dims)
    }

    /// Create a new type with no packed dimensions.
    ///
    /// This creates the type on the stack. In general you will want to use the
    /// `make_*` functions to create a type that is interned into a context.
    pub fn with_sign(core: impl Into<PackedCore<'a>>, sign: Sign, sign_explicit: bool) -> Self {
        Self::with_sign_and_dims(core, sign, sign_explicit, vec![])
    }

    /// Create a new type with packed dimensions.
    ///
    /// This creates the type on the stack. In general you will want to use the
    /// `make_*` functions to create a type that is interned into a context.
    pub fn with_sign_and_dims(
        core: impl Into<PackedCore<'a>>,
        sign: Sign,
        sign_explicit: bool,
        dims: Vec<PackedDim>,
    ) -> Self {
        Self {
            core: core.into(),
            sign,
            sign_explicit,
            dims,
            resolved: None,
            resolved_full: None,
        }
    }

    /// Create a new type from an SBVT.
    pub fn with_simple_bit_vector(sbv: SbvType) -> Self {
        let atom = match (sbv.size, sbv.domain) {
            (8, Domain::TwoValued) => Some(IntAtomType::Byte),
            (16, Domain::TwoValued) => Some(IntAtomType::ShortInt),
            (32, Domain::TwoValued) => Some(IntAtomType::Int),
            (32, Domain::FourValued) => Some(IntAtomType::Integer),
            (64, Domain::TwoValued) => Some(IntAtomType::LongInt),
            _ => None,
        };
        match atom {
            Some(atom) if sbv.used_atom => Self::with_sign(atom, sbv.sign, sbv.sign_explicit),
            _ => Self::with_sign_and_dims(
                match sbv.domain {
                    Domain::TwoValued => IntVecType::Bit,
                    Domain::FourValued => IntVecType::Logic,
                },
                sbv.sign,
                sbv.sign_explicit,
                if sbv.size > 1 || sbv.size_explicit {
                    vec![PackedDim::Range(sbv.range())]
                } else {
                    vec![]
                },
            ),
        }
    }

    /// Create an interned type with default sign and no packed dimensions.
    pub fn make(cx: &impl TypeContext<'a>, core: impl Into<PackedCore<'a>>) -> &'a Self {
        Self::new(core).intern(cx)
    }

    /// Create an interned type with default sign and packed dimensions.
    pub fn make_dims(
        cx: &impl TypeContext<'a>,
        core: impl Into<PackedCore<'a>>,
        dims: Vec<PackedDim>,
    ) -> &'a Self {
        Self::with_dims(core, dims).intern(cx)
    }

    /// Create an interned type with no packed dimensions.
    pub fn make_sign(
        cx: &impl TypeContext<'a>,
        core: impl Into<PackedCore<'a>>,
        sign: Sign,
        sign_explicit: bool,
    ) -> &'a Self {
        Self::with_sign(core, sign, sign_explicit).intern(cx)
    }

    /// Create an interned type with packed dimensions.
    pub fn make_sign_and_dims(
        cx: &impl TypeContext<'a>,
        core: impl Into<PackedCore<'a>>,
        sign: Sign,
        sign_explicit: bool,
        dims: Vec<PackedDim>,
    ) -> &'a Self {
        Self::with_sign_and_dims(core, sign, sign_explicit, dims).intern(cx)
    }

    /// Create an interned type from an SBVT.
    pub fn make_simple_bit_vector(cx: &impl TypeContext<'a>, sbv: SbvType) -> &'a Self {
        Self::with_simple_bit_vector(sbv).intern(cx)
    }

    /// Create a tombstone.
    pub fn make_error() -> &'a Self {
        static TYPE: Lazy<PackedType> = Lazy::new(|| PackedType::new(PackedCore::Error));
        let ty: &PackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Create a `void` type.
    pub fn make_void() -> &'a Self {
        static TYPE: Lazy<PackedType> = Lazy::new(|| PackedType::new(PackedCore::Void));
        let ty: &PackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Create a `logic` type.
    pub fn make_logic() -> &'a Self {
        static TYPE: Lazy<PackedType> = Lazy::new(|| PackedType::new(IntVecType::Logic));
        let ty: &PackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Create a `time` type.
    pub fn make_time() -> &'a Self {
        static TYPE: Lazy<PackedType> = Lazy::new(|| PackedType::new(IntAtomType::Time));
        let ty: &PackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Internalize this type in a context and resolve it.
    pub fn intern(mut self, cx: &impl TypeContext<'a>) -> &'a Self {
        let inner = match self.core {
            PackedCore::Named { ty, .. } => Some(ty),
            PackedCore::Ref { ty, .. } => Some(ty),
            _ => None,
        };
        self.resolved = inner.map(|ty| self.apply_to_inner(cx, ty));
        self.resolved_full = inner.map(|ty| self.apply_to_inner(cx, ty.resolve_full()));
        if let Some(x) = self.resolved {
            trace!("Type `{}` resolves to `{}`", self, x);
        }
        if let Some(x) = self.resolved_full {
            trace!("Type `{}` fully resolves to `{}`", self, x);
        }
        cx.intern_packed(self)
    }

    /// Apply the sign and dimensions to a core type that expanded to another
    /// type.
    fn apply_to_inner(&self, cx: &impl TypeContext<'a>, inner: &'a Self) -> &'a Self {
        if self.dims.is_empty()
            && self.sign == inner.sign
            && self.sign_explicit == inner.sign_explicit
        {
            return inner;
        }
        let mut out = inner.clone();
        out.dims.extend(self.dims.iter().cloned());
        out.sign = self.sign;
        out.sign_explicit = self.sign_explicit;
        out.intern(cx)
    }

    /// Wrap this packed type up in an unpacked type.
    pub fn to_unpacked(&'a self, cx: &impl TypeContext<'a>) -> &'a UnpackedType<'a> {
        UnpackedType::make(cx, self)
    }

    /// Resolve one level of name or type reference indirection.
    ///
    /// For example, given `typedef int foo; typedef foo bar;`, resolves `bar`
    /// to `foo`.
    pub fn resolve(&self) -> &Self {
        self.resolved.unwrap_or(self)
    }

    /// Resolve all name or type reference indirections recursively.
    ///
    /// For example, given `typedef int foo; typedef foo bar;`, resolves `bar`
    /// to `int`.
    pub fn resolve_full(&self) -> &Self {
        self.resolved_full.unwrap_or(self)
    }

    /// Check if this is a tombstone.
    pub fn is_error(&self) -> bool {
        self.core.is_error()
    }

    /// Check if this type is equal to another one.
    ///
    /// Types which coalesce to `iN` in LLHD are checked for equality of their
    /// SBVT.
    pub fn is_identical(&self, other: &Self) -> bool {
        let a = self.resolve_full();
        let b = other.resolve_full();
        if a.coalesces_to_llhd_scalar() && b.coalesces_to_llhd_scalar() {
            a.get_simple_bit_vector().map(|x| x.forget())
                == b.get_simple_bit_vector().map(|x| x.forget())
        } else {
            a.is_strictly_identical(b)
        }
    }

    /// Check if this type is strictly equal to another one.
    pub fn is_strictly_identical(&self, other: &Self) -> bool {
        let a = self.resolve_full();
        let b = other.resolve_full();
        a.core.is_identical(&b.core) && a.sign == b.sign && a.dims == b.dims
    }

    /// Get the domain for this type.
    pub fn domain(&self) -> Domain {
        match &self.core {
            PackedCore::Error => Domain::TwoValued,
            PackedCore::Void => Domain::TwoValued,
            PackedCore::IntVec(x) => x.domain(),
            PackedCore::IntAtom(x) => x.domain(),
            PackedCore::Struct(x) => x.domain(),
            PackedCore::Enum(x) => x.base.domain(),
            PackedCore::Named { ty, .. } | PackedCore::Ref { ty, .. } => ty.domain(),
        }
    }

    /// Compute the size of this type in bits.
    ///
    /// Returns `None` if one of the type's dimensions is `[]`.
    pub fn get_bit_size(&self) -> Option<usize> {
        let ty = self.resolve_full();
        let mut size = match &ty.core {
            PackedCore::Error => 0,
            PackedCore::Void => 0,
            PackedCore::IntVec(..) => 1,
            PackedCore::IntAtom(x) => x.bit_size(),
            PackedCore::Struct(x) => x.get_bit_size()?,
            PackedCore::Enum(x) => x.base.get_bit_size()?,
            PackedCore::Named { ty, .. } | PackedCore::Ref { ty, .. } => ty.get_bit_size()?,
        };
        for &dim in &self.dims {
            match dim {
                PackedDim::Unsized => return None,
                PackedDim::Range(r) => size *= r.size,
            }
        }
        Some(size)
    }

    /// Check if this type is trivially a SBVT.
    pub fn is_simple_bit_vector(&self) -> bool {
        // NOTE: It's important that this does not use resolve_full(), since
        // otherwise the type casting breaks.
        match self.core {
            PackedCore::IntVec(..) => self.dims.len() == 1,
            _ => false,
        }
    }

    /// Check if this type is an integer atom type, like `int`.
    pub fn is_integer_atom(&self) -> bool {
        match self.resolve_full().core {
            PackedCore::IntAtom(..) => self.dims.len() == 0,
            _ => false,
        }
    }

    /// Check if this type is a single bit type, like `bit`.
    pub fn is_single_bit(&self) -> bool {
        match self.resolve_full().core {
            PackedCore::IntVec(..) => self.dims.len() == 0,
            _ => false,
        }
    }

    /// Check if this type is the `time` type.
    pub fn is_time(&self) -> bool {
        match self.resolve_full().core {
            PackedCore::IntAtom(IntAtomType::Time) => self.dims.len() == 0,
            _ => false,
        }
    }

    /// Check if this type will coalesce to a scalar type in LLHD, like `i42`.
    pub fn coalesces_to_llhd_scalar(&self) -> bool {
        !self.is_time()
            && (self.resolve_full().is_simple_bit_vector()
                || self.is_integer_atom()
                || self.is_single_bit())
    }

    /// Convert this type into an SBVT if possible.
    pub fn get_simple_bit_vector(&self) -> Option<SbvType> {
        let ty = self.resolve_full();
        Some(SbvType {
            domain: ty.domain(),
            used_atom: match self.core {
                PackedCore::IntAtom(..) => true,
                _ => false,
            },
            sign: ty.sign,
            sign_explicit: ty.sign_explicit,
            size: ty.get_bit_size()?,
            size_explicit: !ty.dims.is_empty(),
        })
    }

    /// Convert this type into an SBVT, or report a bug with the given span.
    pub fn simple_bit_vector(&self, cx: &impl DiagEmitter, span: Span) -> SbvType {
        match self.get_simple_bit_vector() {
            Some(sbv) => sbv,
            None => bug_span!(span, cx, "`{}` has no simple bit vector equivalent", self),
        }
    }

    /// Pop the outermost dimension off the type.
    ///
    /// For example, maps `bit [3:0][7:0]` to `bit [7:0]`.
    pub fn pop_dim(&self, cx: &impl TypeContext<'a>) -> Option<&'a Self> {
        let ty = self.resolve_full();
        if !ty.dims.is_empty() {
            let mut new = ty.clone();
            new.dims.remove(0);
            Some(new.intern(cx))
        } else {
            None
        }
    }

    /// Replace the outermost dimension of the type.
    ///
    /// Panics if the type has no dimensions.
    pub fn replace_dim(&self, cx: &impl TypeContext<'a>, dim: PackedDim) -> &'a Self {
        let ty = self.resolve_full();
        if !ty.dims.is_empty() {
            let mut new = ty.clone();
            new.dims[0] = dim;
            new.intern(cx)
        } else {
            panic!("no dimension in `{}` to substitute with `{}`", self, dim);
        }
    }

    /// Get the outermost dimension of the type.
    ///
    /// For example, yields the `[3:0]` in `bit [3:0][7:0]`.
    pub fn outermost_dim(&self) -> Option<PackedDim> {
        self.resolve_full().dims.iter().cloned().next()
    }

    /// Get the underlying struct, or `None` if the type is no struct.
    pub fn get_struct(&self) -> Option<&StructType<'a>> {
        match self.resolve_full().core {
            PackedCore::Struct(ref x) if self.resolve_full().dims.is_empty() => Some(x),
            _ => None,
        }
    }

    /// Convert a legacy `Type` into a `PackedType`.
    pub fn from_legacy(cx: &impl Context<'a>, other: Type<'a>) -> &'a Self {
        match *other {
            TypeKind::Error => PackedType::make_error(),
            TypeKind::Void => PackedType::make_void(),
            TypeKind::Time => PackedType::make(cx, IntAtomType::Time),
            TypeKind::Bit(domain) => PackedType::make(
                cx,
                match domain {
                    Domain::TwoValued => IntVecType::Bit,
                    Domain::FourValued => IntVecType::Logic,
                },
            ),
            TypeKind::Int(width, domain) => PackedType::make_dims(
                cx,
                match domain {
                    Domain::TwoValued => IntVecType::Bit,
                    Domain::FourValued => IntVecType::Logic,
                },
                vec![PackedDim::Range(Range {
                    size: width,
                    dir: RangeDir::Down,
                    offset: 0,
                })],
            ),
            TypeKind::Named(name, _, ty) => PackedType::make(
                cx,
                PackedCore::Named {
                    name: name,
                    ty: PackedType::from_legacy(cx, ty),
                },
            ),
            TypeKind::Struct(node_id) => {
                let def = match cx.struct_def(node_id.id()) {
                    Ok(x) => x,
                    _ => return Self::make_error(),
                };
                assert!(def.packed);
                let (ast, ast_type) = match cx.ast_of(node_id.id()).unwrap() {
                    AstNode::Type(ty) => match ty.kind.data {
                        ast::StructType(ref s) => (s, ty),
                        _ => unreachable!("type is not a struct"),
                    },
                    _ => unreachable!("invalid struct"),
                };
                let members = def
                    .fields
                    .iter()
                    .map(|field| {
                        let (ast_name, ast_member) = match cx.ast_of(field.field).unwrap() {
                            AstNode::StructMember(name, member, _) => (name, member),
                            _ => unreachable!("invalid struct member"),
                        };
                        StructMember {
                            name: field.name,
                            ty: UnpackedType::from_legacy(
                                cx,
                                cx.map_to_type(field.ty, node_id.env()).unwrap(),
                            ),
                            ast_name,
                            ast_member,
                        }
                    })
                    .collect();
                PackedType::make(
                    cx,
                    StructType {
                        ast,
                        ast_type,
                        kind: ast.kind,
                        members,
                        legacy_env: node_id.env(),
                    },
                )
            }
            TypeKind::PackedArray(size, ty) => {
                let mut packed = PackedType::from_legacy(cx, ty).clone();
                packed.dims.insert(
                    0,
                    PackedDim::Range(Range {
                        size: size,
                        dir: RangeDir::Down,
                        offset: 0,
                    }),
                );
                packed.intern(cx)
            }
            TypeKind::BitScalar { domain, sign } => PackedType::make_sign(
                cx,
                match domain {
                    Domain::TwoValued => IntVecType::Bit,
                    Domain::FourValued => IntVecType::Logic,
                },
                sign,
                sign != Sign::Unsigned,
            ),
            TypeKind::BitVector {
                domain,
                sign,
                range,
                dubbed,
            } => {
                let atom = match range.size {
                    8 if dubbed && domain == Domain::TwoValued => Some(IntAtomType::Byte),
                    16 if dubbed && domain == Domain::TwoValued => Some(IntAtomType::ShortInt),
                    32 if dubbed && domain == Domain::TwoValued => Some(IntAtomType::Int),
                    32 if dubbed && domain == Domain::FourValued => Some(IntAtomType::Integer),
                    64 if dubbed && domain == Domain::TwoValued => Some(IntAtomType::LongInt),
                    _ => None,
                };
                if let Some(atom) = atom {
                    PackedType::make_sign(cx, atom, sign, sign != Sign::Signed)
                } else {
                    PackedType::make_sign_and_dims(
                        cx,
                        match domain {
                            Domain::TwoValued => IntVecType::Bit,
                            Domain::FourValued => IntVecType::Logic,
                        },
                        sign,
                        sign != Sign::Unsigned,
                        vec![PackedDim::Range(range)],
                    )
                }
            }
        }
    }

    /// Convert a `PackedType` into a legacy `Type`.
    pub fn to_legacy(&self, cx: &impl Context<'a>) -> Type<'a> {
        let mut dims = self.dims.iter().rev().fuse();
        let mut core = match self.core {
            PackedCore::Error => return &ERROR_TYPE,
            PackedCore::Void => return &VOID_TYPE,
            PackedCore::IntVec(x) => {
                if let Some(dim) = dims.next() {
                    cx.intern_type(TypeKind::BitVector {
                        domain: x.domain(),
                        sign: self.sign,
                        range: match dim {
                            PackedDim::Range(r) => *r,
                            _ => panic!("cannot convert type with range `{}` to legacy type", dim),
                        },
                        dubbed: false,
                    })
                } else {
                    match x {
                        IntVecType::Bit => &BIT_TYPE,
                        IntVecType::Logic => &LOGIC_TYPE,
                        IntVecType::Reg => &LOGIC_TYPE,
                    }
                }
            }
            PackedCore::IntAtom(IntAtomType::Byte) => &BYTE_TYPE,
            PackedCore::IntAtom(IntAtomType::ShortInt) => &SHORTINT_TYPE,
            PackedCore::IntAtom(IntAtomType::Int) => &INT_TYPE,
            PackedCore::IntAtom(IntAtomType::LongInt) => &LONGINT_TYPE,
            PackedCore::IntAtom(IntAtomType::Integer) => &INTEGER_TYPE,
            PackedCore::IntAtom(IntAtomType::Time) => &TIME_TYPE,
            PackedCore::Struct(ref x) => {
                cx.intern_type(TypeKind::Struct(x.ast_type.id().env(x.legacy_env)))
            }
            PackedCore::Enum(ref x) => x.base.to_legacy(cx),
            PackedCore::Named { name, ty } => {
                cx.intern_type(TypeKind::Named(name, NodeId::from_u32(0), ty.to_legacy(cx)))
            }
            PackedCore::Ref { ty, .. } => ty.to_legacy(cx),
        };
        for dim in dims {
            let size = match dim {
                PackedDim::Range(r) => r.size,
                _ => panic!("cannot convert type with range `{}` to legacy type", dim),
            };
            core = cx.intern_type(TypeKind::PackedArray(size, core));
        }
        core
    }
}

impl Display for PackedType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.core.format(
            f,
            if self.sign != self.core.default_sign() || self.sign_explicit {
                Some(self.sign)
            } else {
                None
            },
        )?;
        if !self.dims.is_empty() {
            write!(f, " ")?;
            for dim in &self.dims {
                write!(f, "{}", dim)?;
            }
        }
        Ok(())
    }
}

impl<'a> PackedCore<'a> {
    /// Check if this is a tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            Self::Error => true,
            Self::Named { ty, .. } | Self::Ref { ty, .. } => ty.is_error(),
            _ => false,
        }
    }

    /// Get the default sign for this type.
    pub fn default_sign(&self) -> Sign {
        match self {
            Self::Error => Sign::Unsigned,
            Self::Void => Sign::Unsigned,
            Self::IntVec(_) => Sign::Unsigned,
            Self::IntAtom(x) => x.default_sign(),
            Self::Struct(_) => Sign::Unsigned,
            Self::Enum(_) => Sign::Unsigned,
            Self::Named { .. } => Sign::Unsigned,
            Self::Ref { .. } => Sign::Unsigned,
        }
    }

    /// Check if this type is identical to another one.
    pub fn is_identical(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Error, Self::Error) => true,
            (Self::Void, Self::Void) => true,
            (Self::IntVec(a), Self::IntVec(b)) => a == b,
            (Self::IntAtom(a), Self::IntAtom(b)) => a == b,
            (Self::Struct(a), Self::Struct(b)) => a == b,
            (Self::Enum(a), Self::Enum(b)) => a == b,
            (Self::Named { ty: a, .. }, Self::Named { ty: b, .. }) => a.is_identical(b),
            (Self::Ref { ty: a, .. }, Self::Ref { ty: b, .. }) => a.is_identical(b),
            _ => false,
        }
    }

    /// Helper function to format this core packed type.
    fn format(&self, f: &mut std::fmt::Formatter, sign: Option<Sign>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "<error>"),
            Self::Void => write!(f, "void"),
            Self::IntVec(x) => {
                write!(f, "{}", x)?;
                if let Some(sign) = sign {
                    write!(f, " {}", sign)?;
                }
                Ok(())
            }
            Self::IntAtom(x) => {
                write!(f, "{}", x)?;
                if let Some(sign) = sign {
                    write!(f, " {}", sign)?;
                }
                Ok(())
            }
            Self::Struct(x) => x.format(f, true, sign),
            Self::Enum(x) => write!(f, "{}", x),
            Self::Named { name, .. } => write!(f, "{}", name),
            Self::Ref { span, .. } => write!(f, "{}", span.extract()),
        }
    }
}

impl<'a> From<IntVecType> for PackedCore<'a> {
    fn from(inner: IntVecType) -> Self {
        PackedCore::IntVec(inner)
    }
}

impl<'a> From<IntAtomType> for PackedCore<'a> {
    fn from(inner: IntAtomType) -> Self {
        PackedCore::IntAtom(inner)
    }
}

impl<'a> From<StructType<'a>> for PackedCore<'a> {
    fn from(inner: StructType<'a>) -> Self {
        PackedCore::Struct(inner)
    }
}

impl<'a> From<EnumType<'a>> for PackedCore<'a> {
    fn from(inner: EnumType<'a>) -> Self {
        PackedCore::Enum(inner)
    }
}

impl Display for PackedCore<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format(f, None)
    }
}

impl PackedDim {
    /// Get the dimension's range, or `None` if it is unsized.
    pub fn get_range(&self) -> Option<Range> {
        match *self {
            Self::Range(x) => Some(x),
            Self::Unsized => None,
        }
    }

    /// Get the dimension's size, or `None` if it is unsized.
    pub fn get_size(&self) -> Option<usize> {
        self.get_range().map(|r| r.size)
    }
}

impl From<Range> for PackedDim {
    fn from(range: Range) -> Self {
        Self::Range(range)
    }
}

impl Display for PackedDim {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Range(x) => write!(f, "{}", x),
            Self::Unsized => write!(f, "[]"),
        }
    }
}

impl IntVecType {
    /// Get the domain for this type.
    pub fn domain(&self) -> Domain {
        match self {
            Self::Bit => Domain::TwoValued,
            Self::Logic => Domain::FourValued,
            Self::Reg => Domain::FourValued,
        }
    }
}

impl Display for IntVecType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Bit => write!(f, "bit"),
            Self::Logic => write!(f, "logic"),
            Self::Reg => write!(f, "reg"),
        }
    }
}

impl IntAtomType {
    /// Get the domain for this type.
    pub fn domain(&self) -> Domain {
        match self {
            Self::Byte => Domain::TwoValued,
            Self::ShortInt => Domain::TwoValued,
            Self::Int => Domain::TwoValued,
            Self::LongInt => Domain::TwoValued,
            Self::Integer => Domain::FourValued,
            Self::Time => Domain::TwoValued,
        }
    }

    /// Compute the size of this type.
    pub fn bit_size(&self) -> usize {
        match self {
            Self::Byte => 8,
            Self::ShortInt => 16,
            Self::Int => 32,
            Self::LongInt => 64,
            Self::Integer => 32,
            Self::Time => 64,
        }
    }
    /// Get the default sign for this type.
    pub fn default_sign(&self) -> Sign {
        match self {
            Self::Byte => Sign::Signed,
            Self::ShortInt => Sign::Signed,
            Self::Int => Sign::Signed,
            Self::LongInt => Sign::Signed,
            Self::Integer => Sign::Signed,
            Self::Time => Sign::Unsigned,
        }
    }
}

impl Display for IntAtomType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Byte => write!(f, "byte"),
            Self::ShortInt => write!(f, "shortint"),
            Self::Int => write!(f, "int"),
            Self::LongInt => write!(f, "longint"),
            Self::Integer => write!(f, "integer"),
            Self::Time => write!(f, "time"),
        }
    }
}

impl<'a> UnpackedType<'a> {
    /// Create a new type with no unpacked dimensions.
    ///
    /// This creates the type on the stack. In general you will want to use the
    /// `make_*` functions to create a type that is interned into a context.
    pub fn new(core: impl Into<UnpackedCore<'a>>) -> Self {
        Self::with_dims(core, vec![])
    }

    /// Create a new type with unpacked dimensions.
    ///
    /// This creates the type on the stack. In general you will want to use the
    /// `make_*` functions to create a type that is interned into a context.
    pub fn with_dims(core: impl Into<UnpackedCore<'a>>, dims: Vec<UnpackedDim<'a>>) -> Self {
        Self {
            core: core.into(),
            dims,
            resolved: None,
            resolved_full: None,
        }
    }

    /// Create an interned type with no unpacked dimensions.
    pub fn make(cx: &impl TypeContext<'a>, core: impl Into<UnpackedCore<'a>>) -> &'a Self {
        Self::make_dims(cx, core, vec![])
    }

    /// Create an interned type with unpacked dimensions.
    pub fn make_dims(
        cx: &impl TypeContext<'a>,
        core: impl Into<UnpackedCore<'a>>,
        dims: Vec<UnpackedDim<'a>>,
    ) -> &'a Self {
        Self::with_dims(core, dims).intern(cx)
    }

    /// Create a tombstone.
    pub fn make_error() -> &'a Self {
        static TYPE: Lazy<UnpackedType> = Lazy::new(|| UnpackedType::new(UnpackedCore::Error));
        let ty: &UnpackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Create a `void` type.
    pub fn make_void() -> &'a Self {
        static TYPE: Lazy<UnpackedType> = Lazy::new(|| UnpackedType::new(PackedType::make_void()));
        let ty: &UnpackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Create a `logic` type.
    pub fn make_logic() -> &'a Self {
        static TYPE: Lazy<UnpackedType> = Lazy::new(|| UnpackedType::new(PackedType::make_logic()));
        let ty: &UnpackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Create a `time` type.
    pub fn make_time() -> &'a Self {
        static TYPE: Lazy<UnpackedType> = Lazy::new(|| UnpackedType::new(PackedType::make_time()));
        let ty: &UnpackedType = &TYPE;
        // SAFETY: This is safe since the cell which causes 'a to need to
        // outlive 'static is actually never mutated after AST construction.
        unsafe { std::mem::transmute(ty) }
    }

    /// Internalize this type in a context and resolve it.
    pub fn intern(mut self, cx: &impl TypeContext<'a>) -> &'a Self {
        let inner = match self.core {
            UnpackedCore::Named { ty, .. } | UnpackedCore::Ref { ty, .. } => {
                (Some(ty), Some(ty.resolve_full()))
            }
            UnpackedCore::Packed(ty) => (
                ty.resolved.map(|p| p.to_unpacked(cx)),
                ty.resolved_full.map(|p| p.to_unpacked(cx)),
            ),
            _ => (None, None),
        };
        self.resolved = inner.0.map(|ty| self.apply_to_inner(cx, ty));
        self.resolved_full = inner.1.map(|ty| self.apply_to_inner(cx, ty));
        if let Some(x) = self.resolved {
            trace!("Type `{}` resolves to `{}`", self, x);
        }
        if let Some(x) = self.resolved_full {
            trace!("Type `{}` fully resolves to `{}`", self, x);
        }
        cx.intern_unpacked(self)
    }

    /// Apply the sign and dimensions to a core type that expanded to another
    /// type.
    fn apply_to_inner(&self, cx: &impl TypeContext<'a>, inner: &'a Self) -> &'a Self {
        if self.dims.is_empty() {
            return inner;
        }
        let mut out = inner.clone();
        out.dims.extend(self.dims.iter().cloned());
        out.intern(cx)
    }

    /// Resolve one level of name or type reference indirection.
    ///
    /// For example, given `typedef int foo; typedef foo bar;`, resolves `bar`
    /// to `foo`.
    pub fn resolve(&self) -> &Self {
        self.resolved.unwrap_or(self)
    }

    /// Resolve all name or type reference indirections recursively.
    ///
    /// For example, given `typedef int foo; typedef foo bar;`, resolves `bar`
    /// to `int`.
    pub fn resolve_full(&self) -> &Self {
        self.resolved_full.unwrap_or(self)
    }

    /// Check if this is a tombstone.
    pub fn is_error(&self) -> bool {
        self.core.is_error()
    }

    /// Check if this type is equal to another one.
    ///
    /// Types which coalesce to `iN` in LLHD are checked for equality of their
    /// SBVT.
    pub fn is_identical(&self, other: &Self) -> bool {
        let a = self.resolve_full();
        let b = other.resolve_full();
        a.core.is_identical(&b.core) && a.dims == b.dims
    }

    /// Check if this type is strictly equal to another one.
    pub fn is_strictly_identical(&self, other: &Self) -> bool {
        let a = self.resolve_full();
        let b = other.resolve_full();
        a.core.is_strictly_identical(&b.core) && a.dims == b.dims
    }

    /// Check if this type is strictly a packed type.
    pub fn is_packed(&self) -> bool {
        self.get_packed().is_some()
    }

    /// If this type is strictly a packed type, convert it.
    pub fn get_packed(&self) -> Option<&'a PackedType<'a>> {
        match self.core {
            UnpackedCore::Packed(inner) if self.dims.is_empty() => Some(inner),
            UnpackedCore::Named { ty, .. } | UnpackedCore::Ref { ty, .. }
                if self.dims.is_empty() =>
            {
                ty.get_packed()
            }
            _ => None,
        }
    }

    /// Get the domain for this type.
    pub fn domain(&self) -> Domain {
        match &self.core {
            UnpackedCore::Packed(x) => x.domain(),
            UnpackedCore::Struct(x) => x.domain(),
            UnpackedCore::Named { ty, .. } | UnpackedCore::Ref { ty, .. } => ty.domain(),
            UnpackedCore::Error
            | UnpackedCore::Real(_)
            | UnpackedCore::String
            | UnpackedCore::Chandle
            | UnpackedCore::Event => Domain::TwoValued,
        }
    }

    /// Compute the size of this type in bits.
    ///
    /// Returns `None` if one of the type's dimensions is unsized, associative,
    /// or a queue, or the core type has no known size.
    pub fn get_bit_size(&self) -> Option<usize> {
        let ty = self.resolve_full();
        let mut size = match &ty.core {
            UnpackedCore::Packed(x) => x.get_bit_size()?,
            UnpackedCore::Real(x) => x.bit_size(),
            UnpackedCore::Struct(x) => x.get_bit_size()?,
            UnpackedCore::Named { ty, .. } | UnpackedCore::Ref { ty, .. } => ty.get_bit_size()?,
            UnpackedCore::Error
            | UnpackedCore::String
            | UnpackedCore::Chandle
            | UnpackedCore::Event => return None,
        };
        for &dim in &self.dims {
            match dim {
                UnpackedDim::Array(r) => size *= r,
                UnpackedDim::Range(r) => size *= r.size,
                UnpackedDim::Unsized | UnpackedDim::Assoc(..) | UnpackedDim::Queue(..) => {
                    return None
                }
            }
        }
        Some(size)
    }

    /// Check if this type is trivially a SBVT.
    pub fn is_simple_bit_vector(&self) -> bool {
        self.get_packed()
            .map(|ty| ty.is_simple_bit_vector())
            .unwrap_or(false)
    }

    /// Check if this type is an integer atom type, like `int`.
    pub fn is_integer_atom(&self) -> bool {
        self.get_packed()
            .map(|ty| ty.is_integer_atom())
            .unwrap_or(false)
    }

    /// Check if this type is a single bit type, like `bit`.
    pub fn is_single_bit(&self) -> bool {
        self.get_packed()
            .map(|ty| ty.is_single_bit())
            .unwrap_or(false)
    }

    /// Check if this type will coalesce to a scalar type in LLHD, like `i42`.
    pub fn coalesces_to_llhd_scalar(&self) -> bool {
        self.get_packed()
            .map(|ty| ty.coalesces_to_llhd_scalar())
            .unwrap_or(false)
    }

    /// Convert this type into an SBVT if possible.
    pub fn get_simple_bit_vector(&self) -> Option<SbvType> {
        self.get_packed().and_then(|ty| ty.get_simple_bit_vector())
    }

    /// Convert this type into an SBVT, or report a bug with the given span.
    pub fn simple_bit_vector(&self, cx: &impl DiagEmitter, span: Span) -> SbvType {
        match self.get_simple_bit_vector() {
            Some(sbv) => sbv,
            None => bug_span!(span, cx, "`{}` has no simple bit vector equivalent", self),
        }
    }

    /// Convert a legacy `Type` into an `UnpackedType`.
    pub fn from_legacy(cx: &impl Context<'a>, other: Type<'a>) -> &'a Self {
        Self::make(cx, PackedType::from_legacy(cx, other))
    }

    /// Convert an `UnpackedType` into a legacy `Type`.
    pub fn to_legacy(&self, cx: &impl Context<'a>) -> Type<'a> {
        match self.core {
            UnpackedCore::Error => &ty::ERROR_TYPE,
            UnpackedCore::Packed(x) => x.to_legacy(cx),
            _ => panic!("cannot convert `{}` to legacy type", self),
        }
    }

    /// Get an iterator over the type's packed dimensions, slowest-varying
    /// first.
    ///
    /// For example, produces `[3:0], [7:0]` for `bit [3:0][7:0] $ [1][2]`.
    pub fn packed_dims(&self) -> impl Iterator<Item = PackedDim> + 'a {
        self.resolve_full()
            .get_packed()
            .into_iter()
            .flat_map(|p| p.dims.iter().cloned())
    }

    /// Get an iterator over the type's unpacked dimensions, slowest-varying
    /// first.
    ///
    /// For example, produces `[1], [2]` for `bit [3:0][7:0] $ [1][2]`.
    pub fn unpacked_dims<'s>(&'s self) -> impl Iterator<Item = UnpackedDim<'a>> + 's {
        self.resolve_full().dims.iter().cloned()
    }

    /// Get an iterator over the type's dimensions. slowest-varying first.
    ///
    /// For example, produces `[1], [2], [3:0], [7:0]` for `bit [3:0][7:0] $
    /// [1][2]`.
    pub fn dims<'s>(&'s self) -> impl Iterator<Item = Dim<'a>> + 's {
        self.unpacked_dims()
            .map(Dim::Unpacked)
            .chain(self.packed_dims().map(Dim::Packed))
    }

    /// Pop the outermost dimension off the type.
    ///
    /// For example, maps `bit $ [1][2]` to `bit $ [2]`. Pops off the packed
    /// type as well, mapping `bit [7:0] $` to `bit $`.
    pub fn pop_dim(&self, cx: &impl TypeContext<'a>) -> Option<&'a Self> {
        let ty = self.resolve_full();
        if !ty.dims.is_empty() {
            let mut new = ty.clone();
            new.dims.remove(0);
            Some(new.intern(cx))
        } else {
            self.get_packed()
                .and_then(|p| p.pop_dim(cx))
                .map(|p| p.to_unpacked(cx))
        }
    }

    /// Replace the outermost dimension of the type.
    ///
    /// Panics if the type has no dimensions, or a packed dimension is replaced
    /// with an unpacked dimension, or vice-versa.
    pub fn replace_dim(&self, cx: &impl TypeContext<'a>, dim: Dim<'a>) -> &'a Self {
        let ty = self.resolve_full();
        if !ty.dims.is_empty() {
            let mut new = ty.clone();
            let dim = match dim {
                Dim::Unpacked(d) => d,
                Dim::Packed(d) => panic!(
                    "substituting {:?} for type `{}` whose outermost dimension is unpacked",
                    d, self
                ),
            };
            new.dims[0] = dim;
            new.intern(cx)
        } else {
            let packed = match self.get_packed() {
                Some(packed) => packed,
                None => panic!("no dimension in `{}` to substitute with `{}`", self, dim),
            };
            let dim = match dim {
                Dim::Packed(d) => d,
                Dim::Unpacked(d) => panic!(
                    "substituting {:?} for type `{}` whose outermost dimension is packed",
                    d, self
                ),
            };
            packed.replace_dim(cx, dim).to_unpacked(cx)
        }
    }

    /// Get the outermost dimension of the type.
    ///
    /// For example, yields the `[1]` in `bit $ [1][2]`.
    pub fn outermost_dim(&self) -> Option<Dim<'a>> {
        self.dims().next()
    }

    /// Get the underlying struct, or `None` if the type is no struct.
    pub fn get_struct(&self) -> Option<&StructType<'a>> {
        match self.resolve_full().core {
            UnpackedCore::Packed(x) if self.dims.is_empty() => x.get_struct(),
            UnpackedCore::Struct(ref x) if self.dims.is_empty() => Some(x),
            _ => None,
        }
    }

    /// Helper function to format this type around a declaration name.
    fn format_around(
        &self,
        f: &mut std::fmt::Formatter,
        around: Option<impl Display>,
    ) -> std::fmt::Result {
        write!(f, "{}", self.core)?;
        if let Some(around) = around {
            write!(f, " {}", around)?;
        }
        if !self.dims.is_empty() {
            write!(f, " ")?;
            for dim in &self.dims {
                write!(f, "{}", dim)?;
            }
        }
        Ok(())
    }
}

impl Display for UnpackedType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format_around(
            f,
            if self.dims.is_empty() {
                None
            } else {
                Some("$")
            },
        )
    }
}

impl<'a> UnpackedCore<'a> {
    /// Check if this is a tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            Self::Error => true,
            Self::Packed(ty) => ty.is_error(),
            Self::Named { ty, .. } | Self::Ref { ty, .. } => ty.is_error(),
            _ => false,
        }
    }

    /// Check if this type is identical to another one.
    pub fn is_identical(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Error, Self::Error) => true,
            (Self::Packed(a), Self::Packed(b)) => a.is_identical(b),
            (Self::Real(a), Self::Real(b)) => a == b,
            (Self::Struct(a), Self::Struct(b)) => a == b,
            (Self::String, Self::String) => true,
            (Self::Chandle, Self::Chandle) => true,
            (Self::Event, Self::Event) => true,
            (Self::Named { ty: a, .. }, Self::Named { ty: b, .. }) => a.is_identical(b),
            (Self::Ref { ty: a, .. }, Self::Ref { ty: b, .. }) => a.is_identical(b),
            _ => false,
        }
    }

    /// Check if this type is strictly identical to another one.
    pub fn is_strictly_identical(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Error, Self::Error) => true,
            (Self::Packed(a), Self::Packed(b)) => a.is_strictly_identical(b),
            (Self::Real(a), Self::Real(b)) => a == b,
            (Self::Struct(a), Self::Struct(b)) => a == b,
            (Self::String, Self::String) => true,
            (Self::Chandle, Self::Chandle) => true,
            (Self::Event, Self::Event) => true,
            (Self::Named { ty: a, .. }, Self::Named { ty: b, .. }) => a.is_strictly_identical(b),
            (Self::Ref { ty: a, .. }, Self::Ref { ty: b, .. }) => a.is_strictly_identical(b),
            _ => false,
        }
    }
}

impl<'a> From<&'a PackedType<'a>> for UnpackedCore<'a> {
    fn from(inner: &'a PackedType<'a>) -> Self {
        Self::Packed(inner)
    }
}

impl<'a> From<RealType> for UnpackedCore<'a> {
    fn from(inner: RealType) -> Self {
        Self::Real(inner)
    }
}

impl<'a> From<StructType<'a>> for UnpackedCore<'a> {
    fn from(inner: StructType<'a>) -> Self {
        Self::Struct(inner)
    }
}

impl Display for UnpackedCore<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "<error>"),
            Self::Packed(x) => write!(f, "{}", x),
            Self::Real(x) => write!(f, "{}", x),
            Self::Struct(x) => x.format(f, false, None),
            Self::String => write!(f, "string"),
            Self::Chandle => write!(f, "chandle"),
            Self::Event => write!(f, "event"),
            Self::Named { name, .. } => write!(f, "{}", name),
            Self::Ref { span, .. } => write!(f, "{}", span.extract()),
        }
    }
}

impl UnpackedDim<'_> {
    /// Get the dimension's range, or `None` if it is unsized.
    pub fn get_range(&self) -> Option<Range> {
        match *self {
            Self::Range(x) => Some(x),
            _ => None,
        }
    }

    /// Get the dimension's size, or `None` if it is unsized.
    pub fn get_size(&self) -> Option<usize> {
        match *self {
            Self::Array(x) => Some(x),
            Self::Range(x) => Some(x.size),
            _ => None,
        }
    }
}

impl From<usize> for UnpackedDim<'_> {
    fn from(size: usize) -> Self {
        Self::Array(size)
    }
}
impl From<Range> for UnpackedDim<'_> {
    fn from(range: Range) -> Self {
        Self::Range(range)
    }
}

impl Display for UnpackedDim<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Unsized => write!(f, "[]"),
            Self::Array(x) => write!(f, "{}", x),
            Self::Range(x) => write!(f, "{}", x),
            Self::Assoc(Some(x)) => write!(f, "[{}]", x),
            Self::Assoc(None) => write!(f, "[*]"),
            Self::Queue(Some(x)) => write!(f, "[$:{}]", x),
            Self::Queue(None) => write!(f, "[$]"),
        }
    }
}

impl RealType {
    /// Compute the size of this type.
    pub fn bit_size(&self) -> usize {
        match self {
            Self::ShortReal => 32,
            Self::Real => 64,
            Self::RealTime => 64,
        }
    }
}

impl Display for RealType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ShortReal => write!(f, "shortreal"),
            Self::Real => write!(f, "real"),
            Self::RealTime => write!(f, "realtime"),
        }
    }
}

impl<'a> StructType<'a> {
    /// Get the domain for this struct.
    pub fn domain(&self) -> Domain {
        let any_four_valued = self
            .members
            .iter()
            .any(|m| m.ty.domain() == Domain::FourValued);
        match any_four_valued {
            true => Domain::FourValued,
            false => Domain::TwoValued,
        }
    }

    /// Compute the size of this struct in bits.
    ///
    /// Returns `None` if any member of the type has a `[]` dimension.
    pub fn get_bit_size(&self) -> Option<usize> {
        let mut size = 0;
        for m in &self.members {
            size += m.ty.get_bit_size()?;
        }
        Some(size)
    }

    /// Helper function to format this struct.
    fn format(
        &self,
        f: &mut std::fmt::Formatter,
        packed: bool,
        sign: Option<Sign>,
    ) -> std::fmt::Result {
        write!(f, "{}", self.kind)?;
        if packed {
            write!(f, " packed")?;
            if let Some(sign) = sign {
                write!(f, " {}", sign)?;
            }
        }
        write!(f, " {{ ")?;
        for member in &self.members {
            write!(f, "{}; ", member)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl Display for StructType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format(f, false, None)
    }
}

impl Display for StructMember<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.ty.format_around(f, Some(self.name))
    }
}

impl Display for EnumType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "enum")?;
        if self.base_explicit {
            write!(f, " {}", self.base)?;
        }
        write!(f, "{{")?;
        let mut first = true;
        for (name, _) in &self.variants {
            if !first {
                write!(f, ",")?;
            }
            write!(f, " ")?;
            first = false;
            write!(f, "{}", name)?;
        }
        write!(f, " }}")?;
        Ok(())
    }
}

impl SbvType {
    /// Create a new SBVT which expands exactly to `<domain> <sign>
    /// [<size>-1:0]`.
    pub fn new(domain: Domain, sign: Sign, size: usize) -> Self {
        Self {
            domain,
            used_atom: false,
            sign,
            sign_explicit: false,
            size,
            size_explicit: true,
        }
    }

    /// Create a new SBVT which expands to most terse representation possible.
    ///
    /// For example, creating a signed, two-value, 32 bit SBVT will expand to
    /// `int`.
    pub fn nice(domain: Domain, sign: Sign, size: usize) -> Self {
        Self {
            domain,
            used_atom: true,
            sign,
            sign_explicit: false,
            size,
            size_explicit: false,
        }
    }

    /// Convert the SBVT to a packed type.
    pub fn to_packed<'a>(&self, cx: &impl TypeContext<'a>) -> &'a PackedType<'a> {
        PackedType::make_simple_bit_vector(cx, *self)
    }

    /// Convert the SBVT to an unpacked type.
    pub fn to_unpacked<'a>(&self, cx: &impl TypeContext<'a>) -> &'a UnpackedType<'a> {
        self.to_packed(cx).to_unpacked(cx)
    }

    /// Check whether the type is unsigned.
    pub fn is_unsigned(&self) -> bool {
        self.sign == Sign::Unsigned
    }

    /// Check whether the type is signed.
    pub fn is_signed(&self) -> bool {
        self.sign == Sign::Signed
    }

    /// Get the range of the type.
    pub fn range(&self) -> Range {
        Range {
            size: self.size,
            dir: RangeDir::Down,
            offset: 0,
        }
    }

    /// Change the size of the type.
    pub fn change_size(&self, size: usize) -> SbvType {
        SbvType {
            used_atom: self.used_atom && self.size == size,
            size: size,
            ..*self
        }
    }

    /// Change the domain of the type.
    pub fn change_domain(&self, domain: Domain) -> SbvType {
        SbvType { domain, ..*self }
    }

    /// Change the sign of the type.
    pub fn change_sign(&self, sign: Sign) -> SbvType {
        SbvType {
            sign,
            sign_explicit: self.sign_explicit || self.sign != sign,
            ..*self
        }
    }

    /// Check whether this type is identical to another one.
    pub fn is_identical(&self, other: &Self) -> bool {
        self.domain == other.domain && self.sign == other.sign && self.size == other.size
    }

    /// Return a new SBVT that strictly converts to an IntVecType with one
    /// dimension.
    pub fn forget(&self) -> SbvType {
        SbvType {
            used_atom: false,
            sign_explicit: false,
            size_explicit: true,
            ..*self
        }
    }
}

impl Display for SbvType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.domain {
            Domain::TwoValued => write!(f, "bit")?,
            Domain::FourValued => write!(f, "logic")?,
        }
        if self.sign != Sign::Unsigned || self.sign_explicit {
            write!(f, " {}", self.sign)?;
        }
        if self.size > 1 || self.size_explicit {
            write!(f, " {}", self.range())?;
        }
        Ok(())
    }
}

impl Dim<'_> {
    /// Get the dimension's range, or `None` if it has no range.
    pub fn get_range(&self) -> Option<Range> {
        match self {
            Self::Packed(x) => x.get_range(),
            Self::Unpacked(x) => x.get_range(),
        }
    }

    /// Get the dimension's size, or `None` if it has no size.
    pub fn get_size(&self) -> Option<usize> {
        match self {
            Self::Packed(x) => x.get_size(),
            Self::Unpacked(x) => x.get_size(),
        }
    }
}

impl Display for Dim<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Packed(x) => write!(f, "{}", x),
            Self::Unpacked(x) => write!(f, "{}", x),
        }
    }
}

/// A container for type operations.
pub trait TypeContext<'a> {
    /// Internalize a packed type.
    fn intern_packed(&self, ty: PackedType<'a>) -> &'a PackedType<'a>;

    /// Internalize an unpacked type.
    fn intern_unpacked(&self, ty: UnpackedType<'a>) -> &'a UnpackedType<'a>;
}

/// An arena that can internalize type data.
#[derive(Default)]
pub struct TypeStorage<'a> {
    packed: TypedArena<PackedType<'a>>,
    unpacked: TypedArena<UnpackedType<'a>>,
    cached_packed: RefCell<HashSet<&'a PackedType<'a>>>,
    cached_unpacked: RefCell<HashSet<&'a UnpackedType<'a>>>,
}

/// An object that has type storage.
pub trait HasTypeStorage<'a> {
    /// Get the type storage.
    fn type_storage(&self) -> &'a TypeStorage<'a>;
}

impl<'a, T> TypeContext<'a> for T
where
    T: HasTypeStorage<'a>,
{
    fn intern_packed(&self, ty: PackedType<'a>) -> &'a PackedType<'a> {
        let st = self.type_storage();
        if let Some(x) = st.cached_packed.borrow().get(&ty) {
            return x;
        }
        let ty = st.packed.alloc(ty);
        st.cached_packed.borrow_mut().insert(ty);
        ty
    }

    fn intern_unpacked(&self, ty: UnpackedType<'a>) -> &'a UnpackedType<'a> {
        let st = self.type_storage();
        if let Some(x) = st.cached_unpacked.borrow().get(&ty) {
            return x;
        }
        let ty = st.unpacked.alloc(ty);
        st.cached_unpacked.borrow_mut().insert(ty);
        ty
    }
}

impl<'a> HasTypeStorage<'a> for &'a TypeStorage<'a> {
    fn type_storage(&self) -> &'a TypeStorage<'a> {
        *self
    }
}

/// A verilog type.
pub type Type<'t> = &'t TypeKind<'t>;

/// Type data.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TypeKind<'t> {
    /// An error occurred during type computation.
    Error,
    /// The `void` type.
    Void,
    /// The `time` type.
    Time,
    /// A single bit type.
    Bit(Domain),
    /// An integer type.
    Int(usize, Domain),
    /// A named type.
    ///
    /// The first field represents how the type was originally named by the
    /// user. The second field represents the binding of the resolved name. The
    /// third field represents the actual type.
    Named(Spanned<Name>, NodeId, Type<'t>),
    /// A struct type.
    Struct(NodeEnvId),
    /// A packed array type.
    PackedArray(usize, Type<'t>),
    /// A single bit type.
    BitScalar { domain: Domain, sign: Sign },
    /// A simple bit vector type (SBVT).
    ///
    /// The innermost dimension of a multi-dimensional bit vector type is always
    /// represented as a SBVT.
    BitVector {
        domain: Domain,
        sign: Sign,
        range: Range,
        dubbed: bool,
    },
}

/// The number of values each bit of a type can assume.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Domain {
    /// Two-valued types such as `bit` or `int`.
    TwoValued,
    /// Four-valued types such as `logic` or `integer`.
    FourValued,
}

/// Whether a type is signed or unsigned.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum Sign {
    Signed,
    Unsigned,
}

/// The `[a:b]` part in a vector/array type such as `logic [a:b]`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Range {
    /// The total number of bits, given as `|a-b|+1`.
    pub size: usize,
    /// The direction of the vector, i.e. whether `a > b` or `a < b`.
    pub dir: RangeDir,
    /// The starting offset of the range.
    pub offset: isize,
}

/// Which side is greater in a range `[a:b]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RangeDir {
    /// `a < b`
    Up,
    /// `a > b`
    Down,
}

impl Range {
    /// Create a new `[<size>-1:0]` range.
    pub fn with_size(size: usize) -> Self {
        Self {
            size,
            dir: RangeDir::Down,
            offset: 0,
        }
    }
}

impl std::fmt::Debug for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'t> TypeKind<'t> {
    /// Check if this is the error type.
    pub fn is_error(&self) -> bool {
        match *self.resolve_name() {
            TypeKind::Error => true,
            _ => false,
        }
    }

    /// Check if this is the void type.
    pub fn is_void(&self) -> bool {
        match *self.resolve_name() {
            TypeKind::Void => true,
            _ => false,
        }
    }

    /// Check if this is a struct type.
    pub fn is_struct(&self) -> bool {
        match *self.resolve_name() {
            TypeKind::Struct(..) => true,
            _ => false,
        }
    }

    /// Check if this is an array type.
    pub fn is_array(&self) -> bool {
        match *self.resolve_name() {
            TypeKind::PackedArray(..) => true,
            _ => false,
        }
    }

    /// Get the definition of a struct.
    pub fn get_struct_def(&self) -> Option<NodeEnvId> {
        match *self.resolve_name() {
            TypeKind::Struct(id) => Some(id),
            _ => None,
        }
    }

    /// Get the element type of an array.
    pub fn get_array_element(&self) -> Option<Type<'t>> {
        match *self.resolve_name() {
            TypeKind::PackedArray(_, e) => Some(e),
            _ => None,
        }
    }

    /// Get the length of an array.
    pub fn get_array_length(&self) -> Option<usize> {
        match *self.resolve_name() {
            TypeKind::PackedArray(l, _) => Some(l),
            _ => None,
        }
    }

    /// Get the width of the type.
    ///
    /// Panics if the type is not an integer.
    pub fn width(&self) -> usize {
        match *self.resolve_name() {
            TypeKind::Bit(_) => 1,
            TypeKind::Int(w, _) => w,
            TypeKind::BitScalar { .. } => 1,
            TypeKind::BitVector { range, .. } => range.size,
            _ => panic!("{:?} has no width", self),
        }
    }

    /// Check if this is a bit vector type.
    pub fn is_bit_vector(&self) -> bool {
        match *self.resolve_name() {
            TypeKind::BitVector { .. } => true,
            _ => false,
        }
    }

    /// Check if this is a bit scalar type.
    pub fn is_bit_scalar(&self) -> bool {
        match *self.resolve_name() {
            TypeKind::BitScalar { .. } => true,
            _ => false,
        }
    }

    /// Check if this type uses a predefined type alias as name.
    pub fn is_dubbed(&self) -> bool {
        match *self.resolve_name() {
            TypeKind::BitScalar { .. } => true,
            TypeKind::BitVector { dubbed, .. } => dubbed,
            _ => false,
        }
    }

    /// Check if this type is a valid boolean.
    pub fn is_bool(&self) -> bool {
        ty::identical(self, &ty::BIT_TYPE) || ty::identical(self, &ty::LOGIC_TYPE)
    }

    /// Remove all typedefs and reveal the concrete fundamental type.
    pub fn resolve_name(&self) -> &Self {
        match self {
            TypeKind::Named(_, _, ty) => ty.resolve_name(),
            _ => self,
        }
    }

    /// Return the domain of the type, if it has one.
    pub fn get_value_domain(&self) -> Option<Domain> {
        match *self.resolve_name() {
            TypeKind::Bit(d) => Some(d),
            TypeKind::Int(_, d) => Some(d),
            TypeKind::BitScalar { domain, .. } => Some(domain),
            TypeKind::BitVector { domain, .. } => Some(domain),
            TypeKind::PackedArray(_, ty) => ty.get_value_domain(),
            _ => None,
        }
    }

    /// Return the sign of the type, if it has one.
    pub fn get_sign(&self) -> Option<Sign> {
        match *self.resolve_name() {
            TypeKind::Bit(..) => Some(Sign::Unsigned),
            TypeKind::Int(..) => Some(Sign::Unsigned),
            TypeKind::BitScalar { sign, .. } => Some(sign),
            TypeKind::BitVector { sign, .. } => Some(sign),
            TypeKind::PackedArray(_, ty) => ty.get_sign(),
            _ => None,
        }
    }

    /// Return the range of the type, if it has one.
    pub fn get_range(&self) -> Option<Range> {
        match self.resolve_name() {
            TypeKind::Bit(..) => Some(Range {
                size: 1,
                dir: RangeDir::Down,
                offset: 0isize,
            }),
            TypeKind::Int(..) => Some(Range {
                size: 32,
                dir: RangeDir::Down,
                offset: 0isize,
            }),
            TypeKind::BitScalar { .. } => Some(Range {
                size: 1,
                dir: RangeDir::Down,
                offset: 0isize,
            }),
            TypeKind::BitVector { range, .. } => Some(*range),
            _ => None,
        }
    }

    /// Check whether the type is unsigned.
    ///
    /// Returns false for types which have no sign.
    pub fn is_unsigned(&self) -> bool {
        self.get_sign() == Some(Sign::Unsigned)
    }

    /// Check whether the type is signed.
    ///
    /// Returns false for types which have no sign.
    pub fn is_signed(&self) -> bool {
        self.get_sign() == Some(Sign::Signed)
    }

    /// Change the value domain of a type.
    pub fn change_value_domain<'gcx>(
        &'gcx self,
        cx: &impl Context<'gcx>,
        domain: Domain,
    ) -> Type<'gcx> {
        if self.get_value_domain() == Some(domain) {
            return self;
        }
        match *self.resolve_name() {
            TypeKind::Bit(_) => cx.intern_type(TypeKind::BitScalar {
                domain,
                sign: Sign::Unsigned,
            }),
            TypeKind::Int(size, _) => cx.intern_type(TypeKind::BitVector {
                domain,
                sign: Sign::Signed,
                range: Range {
                    size,
                    dir: RangeDir::Down,
                    offset: 0isize,
                },
                dubbed: true,
            }),
            TypeKind::BitScalar { sign, .. } => {
                cx.intern_type(TypeKind::BitScalar { domain, sign })
            }
            TypeKind::BitVector {
                sign,
                range,
                dubbed,
                ..
            } => cx.intern_type(TypeKind::BitVector {
                domain,
                sign,
                range,
                dubbed,
            }),
            _ => self,
        }
    }

    /// Change the sign of a simple bit type.
    pub fn change_sign<'gcx>(&'gcx self, cx: &impl Context<'gcx>, sign: Sign) -> Type<'gcx> {
        if self.get_sign() == Some(sign) {
            return self;
        }
        match *self.resolve_name() {
            TypeKind::BitScalar { domain, .. } => {
                cx.intern_type(TypeKind::BitScalar { domain, sign })
            }
            TypeKind::BitVector {
                domain,
                range,
                dubbed,
                ..
            } => cx.intern_type(TypeKind::BitVector {
                domain,
                sign,
                range,
                dubbed,
            }),
            _ => self,
        }
    }

    /// Change the range of a simple bit type.
    pub fn change_range<'gcx>(&'gcx self, cx: &impl Context<'gcx>, range: Range) -> Type<'gcx> {
        if self.get_range() == Some(range) {
            return self;
        }
        match *self.resolve_name() {
            TypeKind::Bit(domain) => cx.intern_type(TypeKind::BitVector {
                domain,
                sign: Sign::Unsigned,
                range,
                dubbed: false,
            }),
            TypeKind::Int(_, domain) => cx.intern_type(TypeKind::BitVector {
                domain,
                sign: Sign::Signed,
                range,
                dubbed: false,
            }),
            TypeKind::BitScalar { domain, sign } => cx.intern_type(TypeKind::BitVector {
                domain,
                sign,
                range,
                dubbed: false,
            }),
            TypeKind::BitVector {
                domain,
                sign,
                dubbed,
                ..
            } => cx.intern_type(TypeKind::BitVector {
                domain,
                sign,
                range,
                dubbed,
            }),
            _ => self,
        }
    }

    /// Check if this type has a simple bit vector equivalent.
    pub fn has_simple_bit_vector(&self) -> bool {
        match self.resolve_name() {
            TypeKind::Error | TypeKind::Void | TypeKind::Time => false,
            TypeKind::BitVector { .. } | TypeKind::BitScalar { .. } => true,
            TypeKind::Bit(..)
            | TypeKind::Int(..)
            | TypeKind::Struct(..)
            | TypeKind::PackedArray(..) => true,
            TypeKind::Named(..) => unreachable!("handled by resolve_name()"),
        }
    }

    /// Check if this type is a simple bit vector type.
    pub fn is_simple_bit_vector(&self) -> bool {
        match self.resolve_name() {
            TypeKind::Error | TypeKind::Void | TypeKind::Time => false,
            TypeKind::BitVector { .. } | TypeKind::BitScalar { .. } => true,
            TypeKind::Bit(..) => true,
            TypeKind::Int(..) => true,
            TypeKind::Struct(..) | TypeKind::PackedArray(..) => false,
            TypeKind::Named(..) => unreachable!("handled by resolve_name()"),
        }
    }

    /// Try to convert to an equivalent simple bit vector type.
    ///
    /// All *integral* data types have an equivalent *simple bit vector type*.
    /// These include the following:
    ///
    /// - all basic integers
    /// - packed arrays
    /// - packed structures
    /// - packed unions
    /// - enums
    /// - time (excluded in this implementation)
    ///
    /// If `force_vector` is `true`, the returned type has range `[0:0]` if it
    /// would otherwise be a single bit.
    pub fn get_simple_bit_vector<'gcx>(
        &'gcx self,
        cx: &impl Context<'gcx>,
        env: ParamEnv,
        force_vector: bool,
    ) -> Option<Type<'gcx>> {
        let bits = match *self.resolve_name() {
            TypeKind::Error | TypeKind::Void | TypeKind::Time => return None,
            TypeKind::BitVector { .. } => return Some(self),
            TypeKind::BitScalar { .. } if force_vector => 1,
            TypeKind::BitScalar { .. } => return Some(self),
            TypeKind::Bit(..)
            | TypeKind::Int(..)
            | TypeKind::Struct(..)
            | TypeKind::PackedArray(..) => bit_size_of_type(cx, self, env).ok()?,
            TypeKind::Named(..) => unreachable!("handled by resolve_name()"),
        };
        Some(cx.intern_type(TypeKind::BitVector {
            domain: ty::Domain::FourValued, // TODO(fschuiki): check if this is correct
            sign: ty::Sign::Unsigned,
            range: ty::Range {
                size: bits,
                dir: ty::RangeDir::Down,
                offset: 0isize,
            },
            dubbed: false,
        }))
    }

    /// Compute the size of the type in bits.
    pub fn try_bit_size<'gcx>(&'gcx self, cx: &impl Context<'gcx>, env: ParamEnv) -> Result<usize> {
        match *self {
            TypeKind::Error | TypeKind::Void => Ok(0),
            TypeKind::Time => panic!("time value has no bit size"),
            TypeKind::Bit(_) => Ok(1),
            TypeKind::Int(width, _) => Ok(width),
            TypeKind::Named(_, _, ty) => bit_size_of_type(cx, ty, env),
            TypeKind::Struct(struct_id) => {
                let fields = match cx.hir_of(struct_id.id())? {
                    HirNode::Type(hir::Type {
                        kind: hir::TypeKind::Struct(ref fields),
                        ..
                    }) => fields,
                    _ => unreachable!(),
                };
                let mut size = 0;
                for &field in fields {
                    size +=
                        bit_size_of_type(cx, cx.type_of(field, struct_id.env())?, struct_id.env())?;
                }
                Ok(size)
            }
            TypeKind::PackedArray(elements, ty) => Ok(elements * bit_size_of_type(cx, ty, env)?),
            TypeKind::BitScalar { .. } => Ok(1),
            TypeKind::BitVector {
                range: Range { size, .. },
                ..
            } => Ok(size),
        }
    }
}

impl<'t> Display for TypeKind<'t> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            TypeKind::Error => write!(f, "<error>"),
            TypeKind::Void => write!(f, "void"),
            TypeKind::Time => write!(f, "time"),
            TypeKind::Bit(Domain::TwoValued) => write!(f, "bit"),
            TypeKind::Bit(Domain::FourValued) => write!(f, "logic"),
            TypeKind::Int(32, Domain::TwoValued) => write!(f, "int"),
            TypeKind::Int(32, Domain::FourValued) => write!(f, "integer"),
            TypeKind::Int(width, Domain::TwoValued) => write!(f, "int<{}>", width),
            TypeKind::Int(width, Domain::FourValued) => write!(f, "integer<{}>", width),
            TypeKind::Named(name, ..) => write!(f, "{}", name.value),
            TypeKind::Struct(_) => write!(f, "struct"),
            TypeKind::PackedArray(length, ty) => write!(f, "{} [{}:0]", ty, length - 1),
            TypeKind::BitScalar { domain, sign } => {
                write!(f, "{}", domain.bit_name())?;
                if sign == Sign::Signed {
                    write!(f, " signed")?;
                }
                Ok(())
            }
            TypeKind::BitVector {
                domain,
                sign,
                range,
                dubbed,
            } => {
                // Use the builtin name if called such by the user.
                if dubbed {
                    let dub = match range.size {
                        8 if domain == Domain::TwoValued => Some("byte"),
                        16 if domain == Domain::TwoValued => Some("shortint"),
                        32 if domain == Domain::TwoValued => Some("int"),
                        32 if domain == Domain::FourValued => Some("integer"),
                        64 if domain == Domain::TwoValued => Some("longint"),
                        _ => None,
                    };
                    if let Some(dub) = dub {
                        write!(f, "{}", dub)?;
                        if sign != Sign::Signed {
                            write!(f, " {}", sign)?;
                        }
                        return Ok(());
                    }
                }

                // Otherwise use the regular bit name with vector range.
                write!(f, "{}", domain.bit_name())?;
                if sign != Sign::Unsigned {
                    write!(f, " {}", sign)?;
                }
                write!(f, " {}", range)
            }
        }
    }
}

impl Domain {
    /// Return the single-bit name for this domain (`bit` or `logic`).
    pub fn bit_name(&self) -> &'static str {
        match self {
            Domain::TwoValued => "bit",
            Domain::FourValued => "logic",
        }
    }

    /// Return the single-bit type for this domain (`bit` or `logic`).
    pub fn bit_type(&self) -> &'static TypeKind<'static> {
        match self {
            Domain::TwoValued => &BIT_TYPE,
            Domain::FourValued => &LOGIC_TYPE,
        }
    }
}

impl Sign {
    /// Check whether the type is unsigned.
    ///
    /// Returns false for types which have no sign.
    pub fn is_unsigned(&self) -> bool {
        *self == Sign::Unsigned
    }

    /// Check whether the type is signed.
    ///
    /// Returns false for types which have no sign.
    pub fn is_signed(&self) -> bool {
        *self == Sign::Signed
    }
}

impl Display for Sign {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Sign::Signed => write!(f, "signed"),
            Sign::Unsigned => write!(f, "unsigned"),
        }
    }
}

impl Display for Range {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let lo = self.offset;
        let hi = lo + self.size as isize - 1;
        let (lhs, rhs) = match self.dir {
            RangeDir::Up => (lo, hi),
            RangeDir::Down => (hi, lo),
        };
        write!(f, "[{}:{}]", lhs, rhs)
    }
}

/// The `<error>` type.
pub static ERROR_TYPE: TypeKind<'static> = TypeKind::Error;

/// The `void` type.
pub static VOID_TYPE: TypeKind<'static> = TypeKind::Void;

/// The `time` type.
pub static TIME_TYPE: TypeKind<'static> = TypeKind::Time;

/// The `bit` type.
pub static BIT_TYPE: TypeKind<'static> = TypeKind::BitScalar {
    domain: ty::Domain::TwoValued,
    sign: Sign::Unsigned,
};

/// The `logic` type.
pub static LOGIC_TYPE: TypeKind<'static> = TypeKind::BitScalar {
    domain: ty::Domain::FourValued,
    sign: Sign::Unsigned,
};

/// The `byte` type.
pub static BYTE_TYPE: TypeKind<'static> = TypeKind::BitVector {
    domain: Domain::TwoValued,
    sign: Sign::Signed,
    range: Range {
        size: 8,
        dir: RangeDir::Down,
        offset: 0isize,
    },
    dubbed: true,
};

/// The `shortint` type.
pub static SHORTINT_TYPE: TypeKind<'static> = TypeKind::BitVector {
    domain: Domain::TwoValued,
    sign: Sign::Signed,
    range: Range {
        size: 16,
        dir: RangeDir::Down,
        offset: 0isize,
    },
    dubbed: true,
};

/// The `int` type.
pub static INT_TYPE: TypeKind<'static> = TypeKind::BitVector {
    domain: Domain::TwoValued,
    sign: Sign::Signed,
    range: Range {
        size: 32,
        dir: RangeDir::Down,
        offset: 0isize,
    },
    dubbed: true,
};

/// The `integer` type.
pub static INTEGER_TYPE: TypeKind<'static> = TypeKind::BitVector {
    domain: Domain::FourValued,
    sign: Sign::Signed,
    range: Range {
        size: 32,
        dir: RangeDir::Down,
        offset: 0isize,
    },
    dubbed: true,
};

/// The `longint` type.
pub static LONGINT_TYPE: TypeKind<'static> = TypeKind::BitVector {
    domain: Domain::TwoValued,
    sign: Sign::Signed,
    range: Range {
        size: 64,
        dir: RangeDir::Down,
        offset: 0isize,
    },
    dubbed: true,
};

// Compute the size of a type in bits.
pub fn bit_size_of_type<'gcx>(
    cx: &impl Context<'gcx>,
    ty: Type<'gcx>,
    env: ParamEnv,
) -> Result<usize> {
    ty.try_bit_size(cx, env)
}

/// Check if two types are identical.
///
/// This is not the same as a check for equality, since the types may contain
/// names and spans in the source code which are different, yet still refer to
/// the same type.
pub fn identical(a: Type, b: Type) -> bool {
    let a = a.resolve_name();
    let b = b.resolve_name();
    match (a, b) {
        (
            TypeKind::BitVector {
                domain: da,
                sign: sa,
                range: ra,
                ..
            },
            TypeKind::BitVector {
                domain: db,
                sign: sb,
                range: rb,
                ..
            },
        ) => da == db && sa == sb && ra == rb,

        (TypeKind::PackedArray(sa, ta), TypeKind::PackedArray(sb, tb)) => {
            sa == sb && identical(ta, tb)
        }

        _ => a == b,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_type_names() {
        // Check the builtint dubbed types.
        assert_eq!(format!("{}", BYTE_TYPE), "byte");
        assert_eq!(format!("{}", SHORTINT_TYPE), "shortint");
        assert_eq!(format!("{}", INT_TYPE), "int");
        assert_eq!(format!("{}", INTEGER_TYPE), "integer");
        assert_eq!(format!("{}", LONGINT_TYPE), "longint");

        // Check the direction and offset.
        assert_eq!(
            format!(
                "{}",
                TypeKind::BitVector {
                    domain: Domain::TwoValued,
                    sign: Sign::Unsigned,
                    range: Range {
                        size: 42,
                        dir: RangeDir::Up,
                        offset: 0isize,
                    },
                    dubbed: false,
                }
            ),
            "bit [0:41]"
        );
        assert_eq!(
            format!(
                "{}",
                TypeKind::BitVector {
                    domain: Domain::TwoValued,
                    sign: Sign::Unsigned,
                    range: Range {
                        size: 42,
                        dir: RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                }
            ),
            "bit [41:0]"
        );
        assert_eq!(
            format!(
                "{}",
                TypeKind::BitVector {
                    domain: Domain::TwoValued,
                    sign: Sign::Unsigned,
                    range: Range {
                        size: 42,
                        dir: RangeDir::Down,
                        offset: -2isize,
                    },
                    dubbed: false,
                }
            ),
            "bit [39:-2]"
        );
        assert_eq!(
            format!(
                "{}",
                TypeKind::BitVector {
                    domain: Domain::TwoValued,
                    sign: Sign::Unsigned,
                    range: Range {
                        size: 42,
                        dir: RangeDir::Down,
                        offset: 3isize,
                    },
                    dubbed: false,
                }
            ),
            "bit [44:3]"
        );

        // Check the domain.
        assert_eq!(
            format!(
                "{}",
                TypeKind::BitVector {
                    domain: Domain::FourValued,
                    sign: Sign::Unsigned,
                    range: Range {
                        size: 42,
                        dir: RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                }
            ),
            "logic [41:0]"
        );

        // Check the sign.
        assert_eq!(
            format!(
                "{}",
                TypeKind::BitVector {
                    domain: Domain::FourValued,
                    sign: Sign::Signed,
                    range: Range {
                        size: 42,
                        dir: RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                }
            ),
            "logic signed [41:0]"
        );
    }
}

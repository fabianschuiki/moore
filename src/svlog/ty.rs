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
use crate::{common::arenas::TypedArena, ParamEnv};
use once_cell::sync::Lazy;
use std::{
    cell::RefCell,
    collections::HashSet,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
};

/// A packed type.
#[derive(Debug, Clone)]
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

/// The number of values each bit of a type can assume.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Domain {
    /// Two-valued types such as `bit` or `int`.
    TwoValued,
    /// Four-valued types such as `logic` or `integer`.
    FourValued,
}

/// Whether a type is signed or unsigned.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    /// A `signed` type.
    Signed,
    /// An `unsigned` type.
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

/// An unpacked type.
#[derive(Debug, Clone)]
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
        if let Some(enm) = self.get_enum() {
            enm.base.coalesces_to_llhd_scalar()
        } else {
            !self.is_time()
                && (self.resolve_full().is_simple_bit_vector()
                    || self.is_integer_atom()
                    || self.is_single_bit())
        }
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

    /// Get the underlying enum, or `None` if the type is no enum.
    pub fn get_enum(&self) -> Option<&EnumType<'a>> {
        match self.resolve_full().core {
            PackedCore::Enum(ref x) if self.resolve_full().dims.is_empty() => Some(x),
            _ => None,
        }
    }
}

// Compare and hash `PackedType` by reference.
impl Eq for PackedType<'_> {}
impl PartialEq for PackedType<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Hash for PackedType<'_> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        std::ptr::hash(self, h)
    }
}

// Compare and hash `Intern<PackedType>` by value.
impl Eq for Intern<PackedType<'_>> {}
impl PartialEq for Intern<PackedType<'_>> {
    fn eq(&self, other: &Self) -> bool {
        self.0.core == other.0.core
            && self.0.sign == other.0.sign
            && self.0.sign_explicit == other.0.sign_explicit
            && self.0.dims == other.0.dims
            && self.0.resolved == other.0.resolved
            && self.0.resolved_full == other.0.resolved_full
    }
}
impl Hash for Intern<PackedType<'_>> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.0.core.hash(h);
        self.0.sign.hash(h);
        self.0.sign_explicit.hash(h);
        self.0.dims.hash(h);
        self.0.resolved.hash(h);
        self.0.resolved_full.hash(h);
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
impl Domain {
    /// Return the single-bit type for this domain (`bit` or `logic`).
    pub fn bit_type(&self) -> IntVecType {
        match self {
            Domain::TwoValued => IntVecType::Bit,
            Domain::FourValued => IntVecType::Logic,
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
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Sign::Signed => write!(f, "signed"),
            Sign::Unsigned => write!(f, "unsigned"),
        }
    }
}

impl Debug for Sign {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(self, f)
    }
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

impl Display for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let lo = self.offset;
        let hi = lo + self.size as isize - 1;
        let (lhs, rhs) = match self.dir {
            RangeDir::Up => (lo, hi),
            RangeDir::Down => (hi, lo),
        };
        write!(f, "[{}:{}]", lhs, rhs)
    }
}

impl Debug for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(self, f)
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

    /// Get the underlying enum, or `None` if the type is no enum.
    pub fn get_enum(&self) -> Option<&EnumType<'a>> {
        self.get_packed().and_then(|packed| packed.get_enum())
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

// Compare and hash `UnpackedType` by reference.
impl Eq for UnpackedType<'_> {}
impl PartialEq for UnpackedType<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Hash for UnpackedType<'_> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        std::ptr::hash(self, h)
    }
}

// Compare and hash `Intern<UnpackedType>` by value.
impl Eq for Intern<UnpackedType<'_>> {}
impl PartialEq for Intern<UnpackedType<'_>> {
    fn eq(&self, other: &Self) -> bool {
        self.0.core == other.0.core
            && self.0.dims == other.0.dims
            && self.0.resolved == other.0.resolved
            && self.0.resolved_full == other.0.resolved_full
    }
}
impl Hash for Intern<UnpackedType<'_>> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.0.core.hash(h);
        self.0.dims.hash(h);
        self.0.resolved.hash(h);
        self.0.resolved_full.hash(h);
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
            Self::Array(x) => write!(f, "[{}]", x),
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
        write!(f, " {{")?;
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
    packed: TypedArena<Intern<PackedType<'a>>>,
    unpacked: TypedArena<Intern<UnpackedType<'a>>>,
    cached_packed: RefCell<HashSet<&'a Intern<PackedType<'a>>>>,
    cached_unpacked: RefCell<HashSet<&'a Intern<UnpackedType<'a>>>>,
}

/// An object that has type storage.
pub trait HasTypeStorage<'a> {
    /// Get the type storage.
    fn type_storage(&self) -> &'a TypeStorage<'a>;
}

/// An wrapper around types that hash/compare by pointer, but must hash/compare
/// by value for interning.
struct Intern<T>(T);

impl<'a, T> TypeContext<'a> for T
where
    T: HasTypeStorage<'a>,
{
    fn intern_packed(&self, ty: PackedType<'a>) -> &'a PackedType<'a> {
        let ty = Intern(ty);
        let st = self.type_storage();
        if let Some(x) = st.cached_packed.borrow().get(&ty) {
            return &x.0;
        }
        let ty = st.packed.alloc(ty);
        st.cached_packed.borrow_mut().insert(ty);
        &ty.0
    }

    fn intern_unpacked(&self, ty: UnpackedType<'a>) -> &'a UnpackedType<'a> {
        let ty = Intern(ty);
        let st = self.type_storage();
        if let Some(x) = st.cached_unpacked.borrow().get(&ty) {
            return &x.0;
        }
        let ty = st.unpacked.alloc(ty);
        st.cached_unpacked.borrow_mut().insert(ty);
        &ty.0
    }
}

impl<'a> HasTypeStorage<'a> for &'a TypeStorage<'a> {
    fn type_storage(&self) -> &'a TypeStorage<'a> {
        *self
    }
}

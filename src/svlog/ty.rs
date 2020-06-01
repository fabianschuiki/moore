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
//! ## Signing
//!
//! All packed types have an associated signing, indicating whether they are
//! *signed* or *unsigned*. The types have a default signing, which means that
//! the signing may have been omitted in the source file. Packed types can be
//! sign-cast, which changes only their signing.
//!
//! ## Domain
//!
//! All packed types consist of bits that can either carry two or four values.
//! An aggregate type is two-valued iff *all* its constituent types are
//! two-valued, otherwise it is four-valued. Packed types can be domain-cast,
//! which changes only their value domain.

use crate::{crate_prelude::*, hir::HirNode, ParamEnv};
use std::fmt::{self, Display, Formatter};

/// A packed type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PackedType<'a> {
    /// The core packed type.
    pub core: PackedCore<'a>,
    /// The type signing.
    pub signing: Sign,
    /// Whether the signing was explicit in the source code.
    pub signing_explicit: bool,
    /// The packed dimensions.
    pub dims: Vec<PackedDim>,
}

/// A core packed type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PackedCore<'a> {
    /// An error occurred during type computation.
    Error,
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
/// packed version the struct inherits its signing from its parent `PackedType`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructType<'a> {
    /// The corresponding AST node of this struct definition.
    pub ast: &'a ast::Struct<'a>,
    /// Whether this is a `struct`, `union` or `union tagged`.
    pub kind: ast::StructKind,
    /// The list of members.
    pub members: Vec<StructMember<'a>>,
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

impl Display for PackedType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.core.format(
            f,
            if self.signing_explicit {
                Some(self.signing)
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
    /// Helper function to format this core packed type.
    fn format(&self, f: &mut std::fmt::Formatter, signing: Option<Sign>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "<error>"),
            Self::IntVec(x) => {
                write!(f, "{}", x)?;
                if let Some(signing) = signing {
                    write!(f, " {}", signing)?;
                }
                Ok(())
            }
            Self::IntAtom(x) => {
                write!(f, "{}", x)?;
                if let Some(signing) = signing {
                    write!(f, " {}", signing)?;
                }
                Ok(())
            }
            Self::Struct(x) => x.format(f, true, signing),
            Self::Enum(x) => write!(f, "{}", x),
            Self::Named { name, .. } => write!(f, "{}", name),
            Self::Ref { span, .. } => write!(f, "{}", span.extract()),
        }
    }
}

impl Display for PackedCore<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format(f, None)
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

impl Display for IntVecType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Bit => write!(f, "bit"),
            Self::Logic => write!(f, "logic"),
            Self::Reg => write!(f, "reg"),
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
    /// Check if this is a tombstone.
    pub fn is_error(&self) -> bool {
        self.core.is_error()
    }

    /// Resolve any references or names and return the fundamental type.
    pub fn resolve(&self) -> &Self {
        // TODO: This may require allocating additional types, since resolving
        // may create a new type that combines the core's resolved type's dims
        // with ours.
        unimplemented!()
    }

    /// Helper function to format this type around a declaration name.
    fn format_around(&self, f: &mut std::fmt::Formatter, around: impl Display) -> std::fmt::Result {
        write!(f, "{} {}", self.core, around)?;
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
        self.format_around(f, "$")
    }
}

impl<'a> UnpackedCore<'a> {
    /// Check if this is a tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            Self::Error => true,
            Self::Named { ty, .. } | Self::Ref { ty, .. } => ty.is_error(),
            _ => false,
        }
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
    /// Helper function to format this struct.
    fn format(
        &self,
        f: &mut std::fmt::Formatter,
        packed: bool,
        signing: Option<Sign>,
    ) -> std::fmt::Result {
        write!(f, "{}", self.kind)?;
        if packed {
            write!(f, " packed")?;
            if let Some(signing) = signing {
                write!(f, " {}", signing)?;
            }
        }
        write!(f, "{{ ")?;
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
        self.ty.format_around(f, self.name)
    }
}

impl Display for EnumType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "struct")?;
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

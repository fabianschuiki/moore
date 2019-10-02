// Copyright (c) 2016-2019 Fabian Schuiki

//! An implementation of the verilog type system.

use crate::{crate_prelude::*, hir::HirNode, ParamEnv};

/// A verilog type.
pub type Type<'t> = &'t TypeKind<'t>;

/// Type data.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TypeKind<'t> {
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
    Struct(NodeId),
    /// A packed array type.
    PackedArray(usize, Type<'t>),
}

impl<'t> TypeKind<'t> {
    /// Check if this is the void type.
    pub fn is_void(&self) -> bool {
        match *self {
            TypeKind::Named(_, _, ty) => ty.is_void(),
            TypeKind::Void => true,
            _ => false,
        }
    }

    /// Check if this is a struct type.
    pub fn is_struct(&self) -> bool {
        match *self {
            TypeKind::Named(_, _, ty) => ty.is_struct(),
            TypeKind::Struct(..) => true,
            _ => false,
        }
    }

    /// Check if this is an array type.
    pub fn is_array(&self) -> bool {
        match *self {
            TypeKind::Named(_, _, ty) => ty.is_array(),
            TypeKind::PackedArray(..) => true,
            _ => false,
        }
    }

    /// Get the element type of an array.
    pub fn get_array_element(&self) -> Option<Type<'t>> {
        match *self {
            TypeKind::Named(_, _, ty) => ty.get_array_element(),
            TypeKind::PackedArray(_, e) => Some(e),
            _ => None,
        }
    }

    /// Get the length of an array.
    pub fn get_array_length(&self) -> Option<usize> {
        match *self {
            TypeKind::Named(_, _, ty) => ty.get_array_length(),
            TypeKind::PackedArray(l, _) => Some(l),
            _ => None,
        }
    }

    /// Get the width of the type.
    ///
    /// Panics if the type is not an integer.
    pub fn width(&self) -> usize {
        match *self {
            TypeKind::Bit(_) => 1,
            TypeKind::Int(w, _) => w,
            TypeKind::Named(_, _, ty) => ty.width(),
            _ => panic!("{:?} has no width", self),
        }
    }

    /// Remove all typedefs and reveal the concrete fundamental type.
    pub fn resolve_name(&'t self) -> Type<'t> {
        match *self {
            TypeKind::Named(_, _, ty) => ty.resolve_name(),
            _ => self,
        }
    }
}

impl<'t> std::fmt::Display for TypeKind<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
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
        }
    }
}

/// The number of values each bit of a type can assume.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Domain {
    /// Two-valued types such as `bit` or `int`.
    TwoValued,
    /// Four-valued types such as `logic` or `integer`.
    FourValued,
}

/// The `void` type.
pub static VOID_TYPE: TypeKind<'static> = TypeKind::Void;
/// The `time` type.
pub static TIME_TYPE: TypeKind<'static> = TypeKind::Time;
/// The `bit` type.
pub static BIT_TYPE: TypeKind<'static> = TypeKind::Bit(ty::Domain::TwoValued);
/// The `logic` type.
pub static LOGIC_TYPE: TypeKind<'static> = TypeKind::Bit(ty::Domain::FourValued);

// Compute the size of a type in bits.
pub fn bit_size_of_type<'gcx>(
    cx: &impl Context<'gcx>,
    ty: Type<'gcx>,
    env: ParamEnv,
) -> Result<usize> {
    match *ty {
        TypeKind::Void => Ok(0),
        TypeKind::Time => panic!("time value has no bit size"),
        TypeKind::Bit(_) => Ok(1),
        TypeKind::Int(width, _) => Ok(width),
        TypeKind::Named(_, _, ty) => bit_size_of_type(cx, ty, env),
        TypeKind::Struct(struct_id) => {
            let fields = match cx.hir_of(struct_id)? {
                HirNode::Type(hir::Type {
                    kind: hir::TypeKind::Struct(ref fields),
                    ..
                }) => fields,
                _ => unreachable!(),
            };
            let mut size = 0;
            for &field in fields {
                size += bit_size_of_type(cx, cx.type_of(field, env)?, env)?;
            }
            Ok(size)
        }
        TypeKind::PackedArray(elements, ty) => Ok(elements * bit_size_of_type(cx, ty, env)?),
    }
}

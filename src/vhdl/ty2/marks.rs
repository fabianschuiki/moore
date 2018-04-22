// Copyright (c) 2017-2018 Fabian Schuiki

//! Type declarations and references to them.

use std::fmt::{self, Debug, Display};

use common::name::Name;
use common::source::Span;

use ty2::{AnyType, Subtype, Type};

/// A type name.
///
/// Types can be declared by the user or be provided as a builtin. In the case
/// of a user-defined type we would like to keep track of its `Span` for good
/// error messages. Builtin types have no location we can refer to however, and
/// we must rather keep track of the name directly.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeName {
    /// The name is defined through an internalized name.
    Name(Name),
    /// The name is defined through a span.
    Span(Span),
}

impl From<Name> for TypeName {
    fn from(name: Name) -> TypeName {
        TypeName::Name(name)
    }
}

impl From<Span> for TypeName {
    fn from(span: Span) -> TypeName {
        TypeName::Span(span)
    }
}

impl TypeName {
    /// Get the type name as a string.
    pub fn to_string(self) -> String {
        match self {
            TypeName::Name(name) => name.into(),
            TypeName::Span(span) => span.extract(),
        }
    }

    /// Get the type name as a `Name`.
    ///
    /// Returns `None` if the type name is given through a `Span`.
    pub fn as_name(self) -> Option<Name> {
        match self {
            TypeName::Name(name) => Some(name),
            _ => None,
        }
    }

    /// Get the type name as a `Span`.
    ///
    /// Returns `None` if the type name is given as a `Name`.
    pub fn as_span(self) -> Option<Span> {
        match self {
            TypeName::Span(span) => Some(span),
            _ => None,
        }
    }
}

impl Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeName::Name(name) => write!(f, "{}", name),
            TypeName::Span(span) => write!(f, "{}", span.extract()),
        }
    }
}

impl Debug for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

/// A type declaration.
///
/// A `TypeDecl` associates a name with a type. It is useful as a tracker of how
/// a type was called upon its definition, and where it was defined.
///
/// # Examples
///
/// ```
/// use moore_vhdl::ty2::{Type, TypeDecl, IntegerBasetype, Range};
/// use moore_vhdl::common::name::get_name_table;
///
/// let ta = IntegerBasetype::new(Range::descending(31, 0));
/// let a = TypeDecl::new(
///     get_name_table().intern("DATA", false),
///     &ta,
/// );
///
/// assert_eq!(format!("{}", a), "type DATA is 31 downto 0");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeDecl<'t> {
    name: TypeName,
    ty: &'t Type,
}

impl<'t> TypeDecl<'t> {
    /// Create a new type declaration from a name and a type.
    pub fn new<N: Into<TypeName>>(name: N, ty: &'t Type) -> TypeDecl<'t> {
        TypeDecl {
            name: name.into(),
            ty: ty,
        }
    }

    /// Get the name of the declared type.
    pub fn name(&self) -> TypeName {
        self.name
    }

    /// Get the declared type.
    pub fn ty(&self) -> &'t Type {
        self.ty
    }
}

impl<'t> Type for TypeDecl<'t> {
    fn is_scalar(&self) -> bool {
        self.ty.is_scalar()
    }
    fn is_discrete(&self) -> bool {
        self.ty.is_discrete()
    }
    fn is_numeric(&self) -> bool {
        self.ty.is_numeric()
    }
    fn is_composite(&self) -> bool {
        self.ty.is_composite()
    }
    fn as_any(&self) -> AnyType {
        self.ty.as_any()
    }
}

impl<'t> Display for TypeDecl<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "type {} is {}", self.name, self.ty)
    }
}

/// A subtype declaration.
///
/// A `SubtypeDecl` associates a name with a subtype. It is useful as a tracker
/// of how a subtype was called upon its definition, and where it was defined.
#[derive(Clone, Copy, Debug)]
pub struct SubtypeDecl<'t> {
    name: TypeName,
    ty: &'t Subtype, // TODO: Actually make this a subtype indication.
}

/// A type mark.
///
/// A `TypeMark` associates a name with a type or subtype, but in a different
/// manner than `TypeDecl` and `SubtypeDecl`. It is useful as a tracker of how a
/// type was referred to in the source code. A `TypeMark` represents a way of
/// naming a type that is familiar to the user and can be presented as is in a
/// diagnostic message.
///
/// # Examples
///
/// ```
/// use moore_vhdl::ty2::{Type, TypeMark, NullType};
/// use moore_vhdl::common::name::get_name_table;
///
/// let ta = NullType;
/// let a = TypeMark::new(
///     get_name_table().intern("DATA", false),
///     &ta,
/// );
///
/// assert_eq!(format!("{}", a), "DATA");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeMark<'t> {
    name: TypeName,
    ty: &'t Type,
}

impl<'t> TypeMark<'t> {
    /// Create a new type mark from a name and a type.
    pub fn new<N: Into<TypeName>>(name: N, ty: &'t Type) -> TypeMark<'t> {
        TypeMark {
            name: name.into(),
            ty: ty,
        }
    }

    /// Get the name of the mark.
    pub fn name(&self) -> TypeName {
        self.name
    }

    /// Get the type of the mark.
    pub fn ty(&self) -> &'t Type {
        self.ty
    }
}

impl<'t> Type for TypeMark<'t> {
    fn is_scalar(&self) -> bool {
        self.ty.is_scalar()
    }
    fn is_discrete(&self) -> bool {
        self.ty.is_discrete()
    }
    fn is_numeric(&self) -> bool {
        self.ty.is_numeric()
    }
    fn is_composite(&self) -> bool {
        self.ty.is_composite()
    }
    fn as_any(&self) -> AnyType {
        self.ty.as_any()
    }
}

impl<'t> Display for TypeMark<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

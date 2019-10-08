// Copyright (c) 2016-2019 Fabian Schuiki

//! An implementation of the verilog type system.

use crate::{crate_prelude::*, hir::HirNode, ParamEnv};
use std::fmt::{self, Display, Formatter};

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
            TypeKind::BitScalar { .. } => 1,
            TypeKind::BitVector { range, .. } => range.size,
            _ => panic!("{:?} has no width", self),
        }
    }

    /// Check if this is a bit vector type.
    pub fn is_bit_vector(&self) -> bool {
        match *self {
            TypeKind::Named(_, _, ty) => ty.is_bit_vector(),
            TypeKind::BitVector { .. } => true,
            _ => false,
        }
    }

    /// Check if this is a bit scalar type.
    pub fn is_bit_scalar(&self) -> bool {
        match *self {
            TypeKind::Named(_, _, ty) => ty.is_bit_scalar(),
            TypeKind::BitScalar { .. } => true,
            _ => false,
        }
    }

    /// Remove all typedefs and reveal the concrete fundamental type.
    pub fn resolve_name(&'t self) -> Type<'t> {
        match *self {
            TypeKind::Named(_, _, ty) => ty.resolve_name(),
            _ => self,
        }
    }

    /// Return the domain of the type, if it has one.
    pub fn get_value_domain(&self) -> Option<Domain> {
        match *self {
            TypeKind::Bit(d) => Some(d),
            TypeKind::Int(_, d) => Some(d),
            TypeKind::BitScalar { domain, .. } => Some(domain),
            TypeKind::BitVector { domain, .. } => Some(domain),
            _ => None,
        }
    }

    /// Return the sign of the type, if it has one.
    pub fn get_sign(&self) -> Option<Sign> {
        match *self {
            TypeKind::Bit(..) => Some(Sign::Unsigned),
            TypeKind::Int(..) => Some(Sign::Unsigned),
            TypeKind::BitScalar { sign, .. } => Some(sign),
            TypeKind::BitVector { sign, .. } => Some(sign),
            _ => None,
        }
    }
}

impl<'t> Display for TypeKind<'t> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
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
        TypeKind::BitScalar { .. } => Ok(1),
        TypeKind::BitVector {
            range: Range { size, .. },
            ..
        } => Ok(size),
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
            "bit [38:-2]"
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

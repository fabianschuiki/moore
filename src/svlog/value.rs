// Copyright (c) 2016-2021 Fabian Schuiki

//! Representation of constant values and their operations
//!
//! This module implements a representation for values that may arise within a
//! SystemVerilog source text and provides ways of executing common operations
//! such as addition and multiplication. It also provides the ability to
//! evaluate the constant value of nodes in a context.
//!
//! The operations in this module are intended to panic if invalid combinations
//! of values are used. The compiler's type system should catch and prevent such
//! uses.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{SbvType, UnpackedType},
    ParamEnv, ParamEnvBinding,
};
use bit_vec::BitVec;
use itertools::Itertools;
use num::{BigInt, BigRational, Integer, One, ToPrimitive, Zero};

/// A verilog value.
pub type Value<'t> = &'t ValueData<'t>;

/// The data associated with a value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueData<'t> {
    /// The type of the value.
    pub ty: &'t UnpackedType<'t>,
    /// The actual value.
    pub kind: ValueKind<'t>,
}

impl<'t> ValueData<'t> {
    /// Check if the value represents a computation error tombstone.
    pub fn is_error(&self) -> bool {
        self.ty.is_error() || self.kind.is_error()
    }

    /// Check if this value evaluates to true.
    pub fn is_true(&self) -> bool {
        !self.is_false()
    }

    /// Check if this value evaluates to false.
    pub fn is_false(&self) -> bool {
        match self.kind {
            ValueKind::Void => true,
            ValueKind::Int(ref v, ..) => v.is_zero(),
            ValueKind::Time(ref v) => v.is_zero(),
            ValueKind::StructOrArray(_) => false,
            ValueKind::String(ref v) => v.is_empty(),
            ValueKind::Error => true,
        }
    }

    /// Convert the value to an integer.
    pub fn get_int(&self) -> Option<&BigInt> {
        match self.kind {
            ValueKind::Int(ref v, ..) => Some(v),
            _ => None,
        }
    }
}

impl std::fmt::Display for ValueData<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

/// The different forms a value can assume.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKind<'t> {
    /// The `void` value.
    Void,
    /// An arbitrary precision integer.
    ///
    /// The first field contains the value. The second field indicates the
    /// special bits (x or z), and the third indicates the x bits.
    Int(BigInt, BitVec, BitVec),
    /// An arbitrary precision time interval.
    Time(BigRational),
    /// A struct.
    StructOrArray(Vec<Value<'t>>),
    /// A string.
    ///
    /// Note that we use a raw `u8` array, instead of Rust's `String` type. This
    /// is due to `String` guaranteeing that the encoded byte sequence is valid
    /// UTF8, which SystemVerilog does not guarantee.
    String(Vec<u8>),
    /// An error occurred during value computation.
    Error,
}

impl<'t> ValueKind<'t> {
    /// Check if the value represents a computation error tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            ValueKind::Error => true,
            _ => false,
        }
    }
}

impl std::fmt::Display for ValueKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ValueKind::Void => write!(f, "void"),
            ValueKind::Int(v, ..) => write!(f, "{}", v),
            ValueKind::Time(v) => write!(f, "{}", v),
            ValueKind::StructOrArray(v) => {
                write!(f, "{{ {} }}", v.iter().map(|v| &v.kind).format(", "))
            }
            ValueKind::String(v) => {
                write!(f, "\"")?;
                for &b in v {
                    if (b as char).is_ascii() {
                        write!(f, "{}", b as char)?;
                    } else {
                        write!(f, "\\x{:02x}", b)?;
                    }
                }
                write!(f, "\"")
            }
            ValueKind::Error => write!(f, "<error>"),
        }
    }
}

/// Create a new tombstone value.
pub fn make_error<'a>(ty: &'a UnpackedType<'a>) -> ValueData<'a> {
    ValueData {
        ty,
        kind: ValueKind::Error,
    }
}

/// Create a new integer value.
///
/// Panics if `ty` is not an integer type. Truncates the value to `ty`.
pub fn make_int<'a>(ty: &'a UnpackedType<'a>, value: BigInt) -> ValueData<'a> {
    let w = match ty.get_bit_size() {
        Some(x) => x,
        None => panic!("make_int got type `{}` which has no size", ty),
    };
    make_int_special(
        ty,
        value,
        BitVec::from_elem(w, false),
        BitVec::from_elem(w, false),
    )
}

/// Create a new integer value with special bits.
///
/// Panics if `ty` is not an integer type. Truncates the value to `ty`.
pub fn make_int_special<'a>(
    ty: &'a UnpackedType<'a>,
    value: BigInt,
    special_bits: BitVec,
    x_bits: BitVec,
) -> ValueData<'a> {
    let w = ty.get_bit_size().unwrap();
    ValueData {
        ty: ty,
        kind: ValueKind::Int(value % (BigInt::from(1) << w), special_bits, x_bits),
    }
}

/// Create a new time value.
pub fn make_time<'a>(value: BigRational) -> ValueData<'a> {
    ValueData {
        ty: UnpackedType::make_time(),
        kind: ValueKind::Time(value),
    }
}

/// Create a new struct value.
pub fn make_struct<'a>(ty: &'a UnpackedType<'a>, fields: Vec<Value<'a>>) -> ValueData<'a> {
    assert!(ty.dims().next().is_none() && ty.get_struct().is_some());
    ValueData {
        ty,
        kind: ValueKind::StructOrArray(fields),
    }
}

/// Create a new array value.
pub fn make_array<'a>(ty: &'a UnpackedType<'a>, elements: Vec<Value<'a>>) -> ValueData<'a> {
    assert!(!ty.dims().next().is_none());
    ValueData {
        ty,
        kind: ValueKind::StructOrArray(elements),
    }
}

/// Create a new string value.
pub fn make_string<'a>(ty: &'a UnpackedType<'a>, bytes: Vec<u8>) -> ValueData<'a> {
    assert!(ty.is_string());
    ValueData {
        ty,
        kind: ValueKind::String(bytes),
    }
}

/// Determine the constant value of a node.
#[moore_derive::query]
pub(crate) fn constant_value_of<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Value<'a> {
    let v = constant_value_of_inner(cx, node_id, env);
    if cx.sess().has_verbosity(Verbosity::CONSTS) {
        let span = cx.span(node_id);
        let ext = span.extract();
        let line = span.begin().human_line();
        println!("{}: const({}) = {}, {}", line, ext, v.ty, v.kind);
    }
    v
}

fn constant_value_of_inner<'a>(cx: &impl Context<'a>, node_id: NodeId, env: ParamEnv) -> Value<'a> {
    let hir = match cx.hir_of(node_id) {
        Ok(x) => x,
        _ => return cx.intern_value(make_error(UnpackedType::make_error())),
    };
    match hir {
        HirNode::Expr(expr) => {
            let mir = cx.mir_rvalue(expr.id, env);
            cx.const_mir_rvalue(mir.into())
        }
        HirNode::ValueParam(param) => {
            let env_data = cx.param_env_data(env);
            match env_data.find_value(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.constant_value_of(assigned_id.id(), assigned_id.env())
                }
                Some(ParamEnvBinding::Direct(v)) => return v,
                _ => (),
            }
            if let Some(default) = param.default {
                return cx.constant_value_of(default, env);
            }
            let d = DiagBuilder2::error(format!(
                "{} not assigned and has no default",
                param.desc_full(),
            ));
            let contexts = cx.param_env_contexts(env);
            for &context in &contexts {
                cx.emit(
                    d.clone()
                        .span(cx.span(context))
                        .add_note("Parameter declared here:")
                        .span(param.human_span()),
                );
            }
            if contexts.is_empty() {
                cx.emit(d.span(param.human_span()));
            }
            cx.intern_value(make_error(UnpackedType::make_error()))
        }
        HirNode::GenvarDecl(decl) => {
            let env_data = cx.param_env_data(env);
            match env_data.find_value(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.constant_value_of(assigned_id.id(), assigned_id.env())
                }
                Some(ParamEnvBinding::Direct(v)) => return v,
                _ => (),
            }
            if let Some(init) = decl.init {
                return cx.constant_value_of(init, env);
            }
            cx.emit(
                DiagBuilder2::error(format!("{} not initialized", decl.desc_full()))
                    .span(decl.human_span()),
            );
            cx.intern_value(make_error(UnpackedType::make_error()))
        }
        HirNode::EnumVariant(var) => match var.value {
            Some(v) => cx.constant_value_of(v, env),
            None => {
                let ty = match cx.type_of(node_id, env) {
                    Ok(x) => x,
                    _ => return cx.intern_value(make_error(UnpackedType::make_error())),
                };
                cx.intern_value(make_int(ty, var.index.into()))
            }
        },
        _ => {
            cx.emit(
                DiagBuilder2::error(format!("{} has no constant value", hir.desc_full()))
                    .span(hir.human_span()),
            );
            cx.intern_value(make_error(UnpackedType::make_error()))
        }
    }
}

/// Determine the constant integer value of an MIR rvalue.
///
/// Emits a diagnostic if the value is not an integer.
#[moore_derive::query]
pub(crate) fn const_mir_rvalue_int<'a>(
    cx: &impl Context<'a>,
    mir: Ref<'a, mir::Rvalue<'a>>,
) -> Result<&'a num::BigInt> {
    match cx.const_mir_rvalue(mir).kind {
        ValueKind::Int(ref x, ..) => Ok(x),
        ValueKind::Error => Err(()),
        _ => {
            cx.emit(
                DiagBuilder2::error(format!(
                    "`{}` is not a constant integer",
                    mir.span.extract()
                ))
                .span(mir.span),
            );
            Err(())
        }
    }
}

/// Determine the constant string value of an MIR rvalue.
///
/// Emits a diagnostic if the value is not a string.
#[moore_derive::query]
pub(crate) fn const_mir_rvalue_string<'a>(
    cx: &impl Context<'a>,
    mir: Ref<'a, mir::Rvalue<'a>>,
) -> Result<&'a Vec<u8>> {
    match cx.const_mir_rvalue(mir).kind {
        ValueKind::String(ref x) => Ok(x),
        ValueKind::Error => Err(()),
        _ => {
            cx.emit(
                DiagBuilder2::error(format!("`{}` is not a constant string", mir.span.extract()))
                    .span(mir.span),
            );
            Err(())
        }
    }
}

/// Determine the constant value of an MIR rvalue.
#[moore_derive::query]
pub(crate) fn const_mir_rvalue<'a>(
    cx: &impl Context<'a>,
    Ref(mir): Ref<'a, mir::Rvalue<'a>>,
) -> Value<'a> {
    let v = const_mir_rvalue_inner(cx, mir);
    if cx.sess().has_verbosity(Verbosity::CONSTS) {
        let ext = mir.span.extract();
        let line = mir.span.begin().human_line();
        println!("{}: const_mir({}) = {}, {}", line, ext, v.ty, v.kind);
    }
    v
}

fn const_mir_rvalue_inner<'a>(cx: &impl Context<'a>, mir: &'a mir::Rvalue<'a>) -> Value<'a> {
    // Propagate MIR tombstones immediately.
    if mir.is_error() {
        return cx.intern_value(make_error(mir.ty));
    }

    match mir.kind {
        // TODO: Casts are just transparent at the moment. That's pretty bad.
        mir::RvalueKind::CastValueDomain { value, .. }
        | mir::RvalueKind::CastSign(_, value)
        | mir::RvalueKind::Truncate(_, value)
        | mir::RvalueKind::ZeroExtend(_, value)
        | mir::RvalueKind::SignExtend(_, value) => {
            warn!(
                "Cast ignored during constant evaluation: `{}` from `{}` to `{}`",
                value.span.extract(),
                value.ty,
                mir.ty
            );
            let v = cx.const_mir_rvalue(value.into());
            // TODO: This is an incredibly ugly hack.
            cx.intern_value(ValueData {
                ty: mir.ty,
                kind: v.kind.clone(),
            })
        }

        mir::RvalueKind::Transmute(value) => {
            let v = cx.const_mir_rvalue(value.into());
            cx.intern_value(ValueData {
                ty: mir.ty,
                kind: v.kind.clone(),
            })
        }

        mir::RvalueKind::CastToBool(value) => {
            let value = cx.const_mir_rvalue(value.into());
            if value.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            cx.intern_value(make_int(mir.ty, (value.is_true() as usize).into()))
        }

        mir::RvalueKind::ApplyTimescale(value, ref scale) => {
            let value = cx.const_mir_rvalue(value.into());
            if value.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            let int = value
                .get_int()
                .expect("value to be timescaled should be int");
            cx.intern_value(make_time(BigRational::from(int.clone()) * scale).into())
        }

        mir::RvalueKind::ConstructArray(ref values) => cx.intern_value(make_array(
            mir.ty,
            (0..values.len())
                .map(|index| cx.const_mir_rvalue(values[&index].into()))
                .collect(),
        )),

        mir::RvalueKind::ConstructStruct(ref values) => cx.intern_value(make_struct(
            mir.ty,
            values
                .iter()
                .map(|&value| cx.const_mir_rvalue(value.into()))
                .collect(),
        )),

        mir::RvalueKind::Const(value) => value,

        mir::RvalueKind::UnaryBitwise { op, arg } => {
            let arg_val = cx.const_mir_rvalue(arg.into());
            if arg_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match arg_val.kind {
                ValueKind::Int(ref arg_int, ..) => cx.intern_value(make_int(
                    mir.ty,
                    const_unary_bitwise_int(
                        cx,
                        mir.ty.simple_bit_vector(cx, mir.span),
                        op,
                        arg_int,
                    ),
                )),
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::BinaryBitwise { op, lhs, rhs } => {
            let lhs_val = cx.const_mir_rvalue(lhs.into());
            let rhs_val = cx.const_mir_rvalue(rhs.into());
            if lhs_val.is_error() || rhs_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&lhs_val.kind, &rhs_val.kind) {
                (ValueKind::Int(lhs_int, ..), ValueKind::Int(rhs_int, ..)) => {
                    cx.intern_value(make_int(
                        mir.ty,
                        const_binary_bitwise_int(
                            cx,
                            mir.ty.simple_bit_vector(cx, mir.span),
                            op,
                            lhs_int,
                            rhs_int,
                        ),
                    ))
                }
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::IntUnaryArith { op, arg, .. } => {
            let arg_val = cx.const_mir_rvalue(arg.into());
            if arg_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match arg_val.kind {
                ValueKind::Int(ref arg_int, ..) => cx.intern_value(make_int(
                    mir.ty,
                    const_unary_arith_int(cx, mir.ty.simple_bit_vector(cx, mir.span), op, arg_int),
                )),
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::IntBinaryArith { op, lhs, rhs, .. } => {
            let lhs_val = cx.const_mir_rvalue(lhs.into());
            let rhs_val = cx.const_mir_rvalue(rhs.into());
            if lhs_val.is_error() || rhs_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&lhs_val.kind, &rhs_val.kind) {
                (ValueKind::Int(lhs_int, ..), ValueKind::Int(rhs_int, ..)) => {
                    cx.intern_value(make_int(
                        mir.ty,
                        const_binary_arith_int(
                            cx,
                            mir.ty.simple_bit_vector(cx, mir.span),
                            op,
                            lhs_int,
                            rhs_int,
                        ),
                    ))
                }
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::IntComp { op, lhs, rhs, .. } => {
            let lhs_val = cx.const_mir_rvalue(lhs.into());
            let rhs_val = cx.const_mir_rvalue(rhs.into());
            if lhs_val.is_error() || rhs_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&lhs_val.kind, &rhs_val.kind) {
                (ValueKind::Int(lhs_int, ..), ValueKind::Int(rhs_int, ..)) => {
                    cx.intern_value(make_int(
                        mir.ty,
                        const_comp_int(
                            cx,
                            mir.ty.simple_bit_vector(cx, mir.span),
                            op,
                            lhs_int,
                            rhs_int,
                        ),
                    ))
                }
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::Concat(ref values) => {
            let mut result = BigInt::zero();
            for &value in values {
                result <<= value.ty.simple_bit_vector(cx, value.span).size;
                result |= cx
                    .const_mir_rvalue(value.into())
                    .get_int()
                    .expect("concat non-integer");
            }
            cx.intern_value(make_int(mir.ty, result))
        }

        mir::RvalueKind::Repeat(count, value) => {
            let value_const = cx.const_mir_rvalue(value.into());
            if value_const.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            let sbvt = value.ty.simple_bit_vector(cx, value.span);
            let mut result = BigInt::zero();
            for _ in 0..count {
                result <<= sbvt.size;
                result |= value_const.get_int().expect("repeat non-integer");
            }
            cx.intern_value(make_int(mir.ty, result))
        }

        mir::RvalueKind::Assignment { .. }
        | mir::RvalueKind::Var(_)
        | mir::RvalueKind::Port(_)
        | mir::RvalueKind::IntfSignal(..)
        | mir::RvalueKind::Intf(..) => {
            cx.emit(DiagBuilder2::error("value is not constant").span(mir.span));
            cx.intern_value(make_error(mir.ty))
        }

        mir::RvalueKind::Member { value, field } => {
            let value_const = cx.const_mir_rvalue(value.into());
            if value_const.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match value_const.kind {
                ValueKind::StructOrArray(ref fields) => fields[field],
                _ => unreachable!("member access on non-struct should be caught in typeck"),
            }
        }

        mir::RvalueKind::Ternary {
            cond,
            true_value,
            false_value,
        } => {
            let cond_val = cx.const_mir_rvalue(cond.into());
            let true_val = cx.const_mir_rvalue(true_value.into());
            let false_val = cx.const_mir_rvalue(false_value.into());
            match cond_val.is_true() {
                true => true_val,
                false => false_val,
            }
        }

        mir::RvalueKind::Shift {
            op,
            arith,
            value,
            amount,
            ..
        } => {
            let value_val = cx.const_mir_rvalue(value.into());
            let amount_val = cx.const_mir_rvalue(amount.into());
            if value_val.is_error() || amount_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&value_val.kind, &amount_val.kind) {
                (ValueKind::Int(value_int, ..), ValueKind::Int(amount_int, ..)) => {
                    cx.intern_value(make_int(
                        mir.ty,
                        const_shift_int(
                            cx,
                            value.ty.simple_bit_vector(cx, value.span),
                            op,
                            arith,
                            value_int,
                            amount_int,
                        ),
                    ))
                }
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::Reduction { op, arg } => {
            let arg_val = cx.const_mir_rvalue(arg.into());
            if arg_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match arg_val.kind {
                ValueKind::Int(ref arg_int, ..) => cx.intern_value(make_int(
                    mir.ty,
                    const_reduction_int(cx, arg.ty.simple_bit_vector(cx, arg.span), op, arg_int),
                )),
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::Index {
            value,
            base,
            length,
            ..
        } => {
            let inner_val = cx.const_mir_rvalue(value.into());
            if inner_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            let base = match cx.const_mir_rvalue_int(Ref(base)) {
                Ok(x) => x.to_isize().expect("base out of bounds"),
                _ => return cx.intern_value(make_error(mir.ty)),
            };
            match inner_val.kind {
                // TODO: This magic should all be replaced by a dedicated
                // arithmetic module which handles the semantics of SV properly.
                ValueKind::Int(ref int, ref special_bits, ref x_bits) => {
                    let length = std::cmp::max(length, 1); // bit-select same as length-1-select
                    let v = if base < 0 {
                        int << (-base) as usize
                    } else {
                        int >> base as usize
                    };
                    let v = v % (BigInt::one() << length);
                    let mut new_special_bits = BitVec::from_elem(length, false);
                    let mut new_x_bits = BitVec::from_elem(length, false);
                    for i in 0..length as isize {
                        if i >= base && i < base + length as isize {
                            new_special_bits.set((i - base) as usize, special_bits[i as usize]);
                            new_x_bits.set((i - base) as usize, x_bits[i as usize]);
                        }
                    }
                    cx.intern_value(make_int_special(mir.ty, v, new_special_bits, new_x_bits))
                }
                ValueKind::StructOrArray(ref values) if length == 0 => {
                    if base < 0 || base >= values.len() as isize {
                        cx.type_default_value(mir.ty)
                    } else {
                        values[base as usize]
                    }
                }
                ValueKind::StructOrArray(ref values) => {
                    let mut new_values = Vec::with_capacity(length);
                    if base < 0 {
                        let default = cx.type_default_value(mir.ty);
                        for _ in base..0 {
                            new_values.push(default);
                        }
                    }
                    let base = std::cmp::max(base, 0) as usize;
                    if base < values.len() {
                        for &v in &values[base..] {
                            new_values.push(v);
                        }
                    }
                    if new_values.len() < length {
                        let default = cx.type_default_value(mir.ty);
                        for _ in new_values.len()..length {
                            new_values.push(default);
                        }
                    }
                    cx.intern_value(make_array(mir.ty, new_values))
                }
                _ => unreachable!("const index op on value {:?}", inner_val),
            }
        }

        // Pack a string into a vector.
        mir::RvalueKind::PackString(value) => match cx.const_mir_rvalue_string(value.into()) {
            Ok(v) => cx.intern_value(make_int(
                mir.ty,
                BigInt::from_bytes_be(num::bigint::Sign::Plus, v),
            )),
            Err(()) => cx.intern_value(make_error(mir.ty)),
        },

        // Unpack a string from a vector.
        mir::RvalueKind::UnpackString(value) => {
            let mut konst = match cx.const_mir_rvalue_int(value.into()) {
                Ok(v) => v.clone(),
                Err(()) => return cx.intern_value(make_error(mir.ty)),
            };
            let mut bytes = vec![];
            while !konst.is_zero() {
                let byte = (&konst & BigInt::from(0xFF)).to_usize().unwrap() as u8;
                if byte != 0 {
                    bytes.push(byte);
                }
                konst >>= 8;
            }
            bytes.reverse();
            cx.intern_value(make_string(mir.ty, bytes))
        }

        mir::RvalueKind::StringComp { op, lhs, rhs, .. } => {
            let lhs_val = cx.const_mir_rvalue(lhs.into());
            let rhs_val = cx.const_mir_rvalue(rhs.into());
            if lhs_val.is_error() || rhs_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&lhs_val.kind, &rhs_val.kind) {
                (ValueKind::String(lhs_string), ValueKind::String(rhs_string)) => cx.intern_value(
                    make_int(mir.ty, const_comp_string(cx, op, lhs_string, rhs_string)),
                ),
                _ => unreachable!(),
            }
        }

        // TODO(fschuiki): Fix this once we support constant function calls.
        mir::RvalueKind::Call { .. } => cx.intern_value(make_error(mir.ty)),

        // Propagate tombstones.
        mir::RvalueKind::Error => cx.intern_value(make_error(mir.ty)),
    }
}

fn const_unary_bitwise_int<'gcx>(
    _cx: &impl Context<'gcx>,
    ty: SbvType,
    op: mir::UnaryBitwiseOp,
    arg: &BigInt,
) -> BigInt {
    match op {
        mir::UnaryBitwiseOp::Not => (BigInt::one() << ty.size) - 1 - arg,
    }
}

fn const_binary_bitwise_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: SbvType,
    op: mir::BinaryBitwiseOp,
    lhs: &BigInt,
    rhs: &BigInt,
) -> BigInt {
    match op {
        mir::BinaryBitwiseOp::And => lhs & rhs,
        mir::BinaryBitwiseOp::Or => lhs | rhs,
        mir::BinaryBitwiseOp::Xor => lhs ^ rhs,
    }
}

fn const_unary_arith_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: SbvType,
    op: mir::IntUnaryArithOp,
    arg: &BigInt,
) -> BigInt {
    match op {
        mir::IntUnaryArithOp::Neg => -arg,
    }
}

fn const_binary_arith_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: SbvType,
    op: mir::IntBinaryArithOp,
    lhs: &BigInt,
    rhs: &BigInt,
) -> BigInt {
    match op {
        mir::IntBinaryArithOp::Add => lhs + rhs,
        mir::IntBinaryArithOp::Sub => lhs - rhs,
        mir::IntBinaryArithOp::Mul => lhs * rhs,
        mir::IntBinaryArithOp::Div => lhs / rhs,
        mir::IntBinaryArithOp::Mod => lhs % rhs,
        mir::IntBinaryArithOp::Pow => {
            let mut result = num::one();
            let mut cnt = rhs.clone();
            while !cnt.is_zero() {
                result = result * lhs;
                cnt = cnt - 1;
            }
            result
        }
    }
}

fn const_comp_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: SbvType,
    op: mir::IntCompOp,
    lhs: &BigInt,
    rhs: &BigInt,
) -> BigInt {
    match op {
        mir::IntCompOp::Eq => ((lhs == rhs) as usize).into(),
        mir::IntCompOp::Neq => ((lhs != rhs) as usize).into(),
        mir::IntCompOp::Lt => ((lhs < rhs) as usize).into(),
        mir::IntCompOp::Leq => ((lhs <= rhs) as usize).into(),
        mir::IntCompOp::Gt => ((lhs > rhs) as usize).into(),
        mir::IntCompOp::Geq => ((lhs >= rhs) as usize).into(),
    }
}

fn const_shift_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: SbvType,
    op: mir::ShiftOp,
    _arith: bool,
    value: &BigInt,
    amount: &BigInt,
) -> BigInt {
    match op {
        mir::ShiftOp::Left => match amount.to_isize() {
            Some(sh) if sh < 0 => value >> -sh as usize,
            Some(sh) => value << sh as usize,
            None => num::zero(),
        },
        mir::ShiftOp::Right => match amount.to_isize() {
            Some(sh) if sh < 0 => value << -sh as usize,
            Some(sh) => value >> sh as usize,
            None => num::zero(),
        },
    }
}

fn const_reduction_int<'gcx>(
    _cx: &impl Context<'gcx>,
    ty: SbvType,
    op: mir::BinaryBitwiseOp,
    arg: &BigInt,
) -> BigInt {
    match op {
        mir::BinaryBitwiseOp::And => ((arg == &((BigInt::one() << ty.size) - 1)) as usize).into(),
        mir::BinaryBitwiseOp::Or => ((!arg.is_zero()) as usize).into(),
        mir::BinaryBitwiseOp::Xor => (arg
            .to_bytes_le()
            .1
            .into_iter()
            .map(|v| v.count_ones())
            .sum::<u32>()
            .is_odd() as usize)
            .into(),
    }
}

/// Perform a constant comparison of two string values.
fn const_comp_string<'gcx>(
    _cx: &impl Context<'gcx>,
    op: mir::StringCompOp,
    lhs: &[u8],
    rhs: &[u8],
) -> BigInt {
    match op {
        mir::StringCompOp::Eq => ((lhs == rhs) as usize).into(),
        mir::StringCompOp::Neq => ((lhs != rhs) as usize).into(),
    }
}

/// Check if a node has a constant value.
#[moore_derive::query]
pub(crate) fn is_constant<'a>(cx: &impl Context<'a>, node_id: NodeId) -> Result<bool> {
    let hir = cx.hir_of(node_id)?;
    Ok(match hir {
        HirNode::ValueParam(_) => true,
        HirNode::GenvarDecl(_) => true,
        HirNode::EnumVariant(_) => true,
        _ => false,
    })
}

/// Determine the default value of a type.
#[moore_derive::query]
pub(crate) fn type_default_value<'a>(cx: &impl Context<'a>, ty: &'a UnpackedType<'a>) -> Value<'a> {
    let ty = ty.resolve_full();
    if ty.is_error() {
        return cx.intern_value(ValueData {
            ty: UnpackedType::make_error(),
            kind: ValueKind::Error,
        });
    }

    // Handle structs.
    if let Some(strukt) = ty.get_struct() {
        let fields = strukt
            .members
            .iter()
            .map(|field| type_default_value(cx, field.ty))
            .collect();
        return cx.intern_value(make_struct(ty, fields));
    }

    // Handle packed base cases.
    if let Some(packed) = ty.get_packed() {
        let packed = packed;
        match packed.core {
            ty::PackedCore::IntVec(_) if packed.dims.len() <= 1 => {
                return cx.intern_value(make_int(ty, Zero::zero()));
            }
            ty::PackedCore::IntAtom(ty::IntAtomType::Time) if packed.dims.is_empty() => {
                return cx.intern_value(make_time(Zero::zero()));
            }
            ty::PackedCore::IntAtom(_) if packed.dims.is_empty() => {
                return cx.intern_value(make_int(ty, Zero::zero()));
            }
            _ => (),
        }
    }

    // Handle arrays.
    if let Some(dim) = ty.outermost_dim() {
        let length = dim
            .get_size()
            .expect("cannot build const value of unsized array");
        let elem_ty = ty.pop_dim(cx).unwrap();
        return cx.intern_value(make_array(
            ty,
            std::iter::repeat(cx.type_default_value(elem_ty))
                .take(length)
                .collect(),
        ));
    }
    assert!(
        ty.dims.is_empty(),
        "unpacked dims should have been handled above: `{}`",
        ty
    );

    // Handle unpacked types.
    let packed = match ty.core {
        ty::UnpackedCore::Packed(p) => p,
        _ => panic!("cannot build const value of unpacked type `{}`", ty),
    };

    // Handle packed types.
    assert!(
        packed.dims.is_empty(),
        "packed dims should have been handled above: `{}`",
        packed
    );
    match packed.core {
        ty::PackedCore::Void => {
            return cx.intern_value(ValueData {
                ty,
                kind: ValueKind::Void,
            })
        }
        ty::PackedCore::Enum(ref x) => return cx.type_default_value(x.base.to_unpacked(cx)),
        ty::PackedCore::IntVec(_) | ty::PackedCore::IntAtom(_) | ty::PackedCore::Struct(_) => {
            unreachable!("should be handled above")
        }
        _ => panic!("cannot build const value of packed type `{}`", packed),
    }
}

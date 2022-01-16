// Copyright (c) 2016-2021 Fabian Schuiki

//! A visitor for the MIR.

use super::*;
use crate::{
    common::{source::Span, NodeId},
    param_env::ParamEnv,
    ty, value,
};
use std::collections::HashMap;

/// A node that accepts `Visitor`s.
pub trait AcceptVisitor<'a> {
    /// Walk a visitor over the contents of `self`.
    fn accept(&'a self, _visitor: &mut dyn Visitor<'a>);
}

/// A node that walks a `Visitor` over itself.
pub trait WalkVisitor<'a> {
    /// Walk a visitor over `self`.
    fn walk(&'a self, _visitor: &mut dyn Visitor<'a>) {}
}

impl<'a> WalkVisitor<'a> for bool {}
impl<'a> WalkVisitor<'a> for usize {}
impl<'a> WalkVisitor<'a> for NodeId {}
impl<'a> WalkVisitor<'a> for ParamEnv {}
impl<'a> WalkVisitor<'a> for Span {}
impl<'a> WalkVisitor<'a> for ty::UnpackedType<'a> {}
impl<'a> WalkVisitor<'a> for ty::Sign {}
impl<'a> WalkVisitor<'a> for ty::Domain {}
impl<'a> WalkVisitor<'a> for value::Value<'_> {}
impl<'a> WalkVisitor<'a> for num::BigRational {}

impl<'a, T: WalkVisitor<'a>> WalkVisitor<'a> for &'_ T {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        (*self).walk(visitor);
    }
}

impl<'a, T: WalkVisitor<'a>> WalkVisitor<'a> for Vec<T> {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        for x in self {
            x.walk(visitor);
        }
    }
}

impl<'a, K, T: WalkVisitor<'a>> WalkVisitor<'a> for HashMap<K, T> {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        for x in self.values() {
            x.walk(visitor);
        }
    }
}

moore_derive::derive_visitor!();

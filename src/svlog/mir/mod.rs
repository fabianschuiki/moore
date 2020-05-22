// Copyright (c) 2016-2020 Fabian Schuiki

//! The medium-level intermediate representation for SystemVerilog.
//!
//! Represents a fully typed SystemVerilog design with all implicit operations
//! converted into explicit nodes.

#![deny(missing_docs)]

pub mod lower;
mod lvalue;
mod rvalue;

pub use lvalue::*;
pub use rvalue::*;

/// An MIR node reference
///
/// This reference is useful when querying the compiler database for information
/// about an MIR node. It compares the reference *by pointer address*, thus
/// allowing for pessimistic compiler queries.
#[derive(Copy, Clone)]
pub struct Ref<'a, T>(&'a T);

impl<'a, T> From<&'a T> for Ref<'a, T> {
    fn from(r: &'a T) -> Ref<'a, T> {
        Ref(r)
    }
}

impl<'a, T> std::ops::Deref for Ref<'a, T> {
    type Target = &'a T;

    fn deref(&self) -> &&'a T {
        &self.0
    }
}

impl<T> Eq for Ref<'_, T> {}

impl<T> PartialEq for Ref<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl<T> std::hash::Hash for Ref<'_, T> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        std::ptr::hash(self.0, h)
    }
}

impl<T> std::fmt::Debug for Ref<'_, T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.0, f)
    }
}

impl<T> std::fmt::Display for Ref<'_, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self.0, f)
    }
}

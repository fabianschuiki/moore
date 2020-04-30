// Copyright (c) 2016-2020 Fabian Schuiki

//! A collection of utility traits and functions specific to VHDL.

#![deny(missing_docs)]

use crate::source::{Span, Spanned};

/// Provides span information for syntax nodes.
pub trait HasSpan {
    /// Obtain the full span of the input file that this node covers.
    fn span(&self) -> Span;

    /// Obtain a span which can be used to refer to this node in error messages
    /// presented to humans. This will generally be the name for things like
    /// entities, processes, and variables. Defaults to return whatever `span()`
    /// returns.
    fn human_span(&self) -> Span {
        self.span()
    }
}

impl<T> HasSpan for Spanned<T> {
    fn span(&self) -> Span {
        self.span
    }
}

/// Describes syntax nodes.
pub trait HasDesc {
    /// Obtain a human-readable descriptive name for this node.
    fn desc(&self) -> &'static str;

    /// Obtain a human-readable description for this node, possibly containing
    /// the node's name.
    fn desc_full(&self) -> String {
        self.desc().into()
    }
}

impl<T> HasDesc for Spanned<T>
where
    T: HasDesc,
{
    fn desc(&self) -> &'static str {
        self.value.desc()
    }
}

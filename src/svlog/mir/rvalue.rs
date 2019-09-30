// Copyright (c) 2016-2019 Fabian Schuiki

//! Rvalue expressions
//!
//! An MIR representation for all expressions that may appear on the right-hand
//! side of an assignment.

use crate::{crate_prelude::*, ty::Type};

/// An rvalue expression.
#[derive(Debug, Clone)]
pub struct Rvalue<'a> {
    /// The span in the source file where the rvalue originates from.
    pub span: Span,
    /// The type of the expression.
    pub ty: Type<'a>,
    /// The expression data.
    pub kind: RvalueKind,
}

/// The different forms an rvalue expression may take.
#[derive(Debug, Clone)]
pub enum RvalueKind {
    /// An error occurred during lowering.
    Error,
}

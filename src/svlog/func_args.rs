// Copyright (c) 2016-2020 Fabian Schuiki

//! A list of arguments to a function or task, with different styles resolved.
//!
//! This module simplifies the list of arguments of a function or task. This is
//! necessary since SystemVerilog allows for two distinct styles of declaring
//! the function arguments, which are similar to the ANSI and non-ANSI port list
//! styles for modules. Essentially, the arguments can be declared in the
//! function prototype directly, or as part of the function body (at the very
//! top).
//!
//! More concretely, it does the following:
//!
//! - Canonicalize ANSI/non-ANSI style
//! - Fill in implicit argument details (defaults and carried-over from
//!   previous argument)
//!
//! Note that when this module refers to "functions", it generally means both
//! *functions* and *tasks*.

use crate::crate_prelude::*;

/// List of arguments of a function or task.
#[derive(Debug, PartialEq, Eq)]
pub struct FuncArgList<'a> {
    marker: std::marker::PhantomData<&'a ()>,
}

/// Resolve the arguments of a function or task a canonical list.
#[moore_derive::query]
pub(crate) fn canonicalize_func_args<'a>(
    cx: &impl Context<'a>,
    node: &'a ast::SubroutineDecl<'a>,
) -> &'a FuncArgList<'a> {
    debug!("Building port list of {:?}", node);

    // Package the argument list up.
    let list = FuncArgList {
        marker: std::marker::PhantomData,
    };
    trace!("Argument list of {:?} is: {:#?}", node, list);
    cx.gcx().arena.alloc_func_arg_list(list)
}

/// A visitor that emits diagnostics for canonicalized function argument lists.
pub struct FuncArgsVerbosityVisitor<'cx, C> {
    cx: &'cx C,
}

impl<'cx, C> FuncArgsVerbosityVisitor<'cx, C> {
    /// Create a new name resolution visitor.
    pub fn new(cx: &'cx C) -> Self {
        FuncArgsVerbosityVisitor { cx }
    }
}

impl<'a, 'cx, C> ast::Visitor<'a> for FuncArgsVerbosityVisitor<'cx, C>
where
    C: Context<'a>,
    'a: 'cx,
{
    fn pre_visit_subroutine_decl(&mut self, node: &'a ast::SubroutineDecl<'a>) -> bool {
        let list = self.cx.canonicalize_func_args(node);
        self.cx.emit(
            DiagBuilder2::note("canonicalized subroutine arguments")
                .span(node.span())
                .add_note(format!("{:#?}", list)),
        );
        true
    }
}

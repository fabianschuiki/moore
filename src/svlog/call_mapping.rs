// Copyright (c) 2016-2020 Fabian Schuiki

//! A pairing of call arguments and the arguments of the called function.
//!
//! This module takes a list of arguments passed to a function or task call, and
//! matches them against the argument list of the function or task declaration.

use crate::crate_prelude::*;
use crate::func_args::{FuncArg, FuncArgList};
use std::{collections::HashMap, sync::Arc};

/// A mapping of call arguments to function/task declaration arguments.
#[derive(Debug, Default, Clone)]
pub struct CallMapping<'a> {
    /// The mapping from declaration arguments to call arguments.
    pub args: Vec<CallArgMapping<'a>>,
}

/// A mapping of a single call argument to a function/task declaration argument.
#[derive(Debug, Clone, Copy)]
pub struct CallArgMapping<'a> {
    /// The argument in the function/task declaration.
    pub decl: &'a FuncArg<'a>,
    /// The source of the argument in the call.
    pub call: CallArgSource<'a>,
    /// The expression ultimately assigned. This is either the expression in the
    /// call argument, or the default expression in the declaration.
    pub expr: &'a ast::Expr<'a>,
    /// The parameter environment to evaluate the call argument.
    pub env: ParamEnv,
}

/// Whether an argument is explicitly provided by the call, or uses the default.
#[derive(Debug, Clone, Copy)]
pub enum CallArgSource<'a> {
    /// Argument explicitly provided in the call.
    Call(&'a ast::CallArg<'a>),
    /// Argument implicitly set to the default provided in the declaration.
    Default(&'a ast::Expr<'a>),
}

/// Map the arguments of a call to the arguments of the callee declaration.
#[moore_derive::query]
pub(crate) fn call_mapping<'a>(
    cx: &impl Context<'a>,
    Ref(decl_args): Ref<'a, FuncArgList<'a>>,
    Ref(call_args): Ref<'a, [ast::CallArg<'a>]>,
    call_span: Span,
) -> Result<Arc<CallMapping<'a>>> {
    debug!("Computing argument mapping");

    // Ensure that the call does not have more arguments than the declaration.
    if call_args.len() > decl_args.args.len() {
        cx.emit(
            DiagBuilder2::error(format!(
                "argument mismatch: {} only has {} arguments, but {} provided",
                decl_args.func,
                decl_args.args.len(),
                call_args.len(),
            ))
            .span(call_span),
        );
        return Err(());
    }

    // Build a lookup table of declaration argument names.
    let decl_args_by_name: HashMap<_, _> = decl_args
        .args
        .iter()
        .flat_map(|a| a.name.map(|n| (n.value, a)))
        .collect();
    trace!("Declaration args lookup: {:?}", decl_args_by_name);

    // Process call arguments and match them.
    let mut seen_named = false;
    let mut partial_mapping = HashMap::<Ref<FuncArg>, &ast::CallArg>::new();

    for (decl_arg, call_arg) in decl_args.args.iter().zip(call_args.iter()) {
        trace!("Matching up `{}`", call_arg.span().extract());

        // Match
        let matched_decl_arg = match call_arg.name {
            Some(call_name) => {
                seen_named = true;
                if let Some(decl_arg) = decl_args_by_name.get(&call_name.value).copied() {
                    decl_arg
                } else {
                    cx.emit(
                        DiagBuilder2::error(format!("unknown argument: `{}`", call_name))
                            .span(call_name.span)
                            .add_note(format!(
                                "Subroutine `{}` was declared here:",
                                decl_args.func.prototype.name
                            ))
                            .span(decl_args.func.span()),
                    );
                    return Err(());
                }
            }
            None if seen_named => {
                cx.emit(
                    DiagBuilder2::error("positional argument after named")
                        .span(call_arg.span())
                        .add_note(
                            "IEEE 1800-2017 requires all positional arguments to appear before \
                             named arguments.",
                        ),
                );
                return Err(());
            }
            None => decl_arg,
        };

        if let Some(previous) = partial_mapping.get(&Ref(matched_decl_arg)) {
            cx.emit(
                DiagBuilder2::error(format!(
                    "argument assigned multiple times: `{}`",
                    matched_decl_arg
                        .name
                        .map(|x| x.to_string())
                        .unwrap_or_else(|| "<unnamed>".to_string())
                ))
                .span(call_arg.span())
                .add_note("Previous assignment was here:")
                .span(previous.span()),
            );
            continue;
        } else {
            partial_mapping.insert(Ref(matched_decl_arg), call_arg);
        }
    }
    trace!("Mapping before assigning defaults: {:#?}", partial_mapping);

    // Make a canonical with one entry for each declaration argument, and
    // populate default values.
    let mut mapping = vec![];
    let mut failed = false;

    for decl_arg in &decl_args.args {
        // Establish the assigned value, either as explicitly provided in the
        // call, or from the default value in the declaration.
        let src = match partial_mapping.get(&Ref(decl_arg)) {
            Some(call_arg) => match &call_arg.expr {
                Some(expr) => Some((expr, call_arg)),
                None => None,
            },
            None => None,
        };
        let (expr, src) = match src {
            Some((expr, call_arg)) => (expr, CallArgSource::Call(call_arg)),
            None => match decl_arg.default {
                Some(default) => (default, CallArgSource::Default(default)),
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "argument without default: `{}` must be passed a value",
                            decl_arg
                                .name
                                .map(|x| x.to_string())
                                .unwrap_or_else(|| "<unnamed>".to_string())
                        ))
                        .span(call_span)
                        .add_note("Argument was declared here:")
                        .span(decl_arg.span),
                    );
                    failed = true;
                    continue;
                }
            },
        };

        // Assemble the data struct.
        let arg = CallArgMapping {
            decl: decl_arg,
            call: src,
            expr,
            env: cx.default_param_env(), // TODO(fschuiki): this needs to change
        };
        mapping.push(arg);
    }

    // Assemble the final struct.
    if failed {
        Err(())
    } else {
        Ok(Arc::new(CallMapping { args: mapping }))
    }
}

/// A visitor that emits diagnostics for the mapping of a call's arguments to
/// the callee's argument list.
pub struct CallMappingVerbosityVisitor<'cx, C> {
    cx: &'cx C,
}

impl<'cx, C> CallMappingVerbosityVisitor<'cx, C> {
    /// Create a new visitor.
    pub fn new(cx: &'cx C) -> Self {
        CallMappingVerbosityVisitor { cx }
    }
}

impl<'a, 'cx, C> ast::Visitor<'a> for CallMappingVerbosityVisitor<'cx, C>
where
    C: Context<'a>,
    'a: 'cx,
{
    fn pre_visit_expr(&mut self, node: &'a ast::Expr<'a>) -> bool {
        // We're only interested in function calls. Get the call target and
        // arguments.
        let (target, args) = match self.cx.hir_of_expr(Ref(node)) {
            Ok(hir::Expr {
                kind: hir::ExprKind::FunctionCall(target, args),
                ..
            }) => (target, args),
            _ => return true,
        };

        // Canonicalize the target's function arguments and establish the
        // mapping to the call arguments.
        let decl_args = self.cx.canonicalize_func_args(Ref(target));
        let mapping = match self.cx.call_mapping(Ref(decl_args), Ref(args), node.span()) {
            Ok(x) => x,
            Err(()) => return true,
        };

        let mut d = DiagBuilder2::note("call argument mapping")
            .span(node.span())
            .add_note(format!(
                "Call to subroutine `{}` has the following argument mapping:",
                target.prototype.name
            ));
        // d = d.add_note(format!("{:#?}", mapping));
        for m in &mapping.args {
            let name = match m.decl.name {
                Some(name) => format!(" {}", name),
                None => format!(""),
            };
            let ty = self.cx.unpacked_type_from_ast(
                Ref(m.decl.ty),
                Ref(m.decl.unpacked_dims),
                m.env,
                None,
            );
            let value = format!(
                "{} {}",
                m.expr.span().extract(),
                match m.call {
                    CallArgSource::Call(..) => "(call)",
                    CallArgSource::Default(..) => "(default)",
                }
            );
            d = d.add_note(format!("{} {}{} = {}", m.decl.dir, ty, name, value));
        }
        self.cx.emit(d);
        true
    }
}

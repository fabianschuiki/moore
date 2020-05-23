// Copyright (c) 2016-2020 Fabian Schuiki

//! A parser for the SystemVerilog language. Based on IEEE 1800-2009.

#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(dead_code)]

use crate::ast;
use crate::ast::*;
use crate::lexer::{Lexer, TokenAndSpan};
use crate::token::*;
use moore_common::{errors::*, name::*, source::*, util::HasSpan};
use std;
use std::collections::VecDeque;

// The problem with data_declaration and data_type_or_implicit:
//
//     [7:0] foo;            # implicit "[7:0]", var "foo"
//     foo bar;              # explicit "foo", var "bar"
//     foo [7:0];            # implicit, var "foo[7:0]"
//     foo [7:0] bar [7:0];  # explicit "foo[7:0]", var "bar[7:0]"

/// Return type of the lower parse primitives, allowing for further adjustment
/// of the diagnostic message that would be generated.
type ParseResult<T> = Result<T, DiagBuilder2>;

/// Return type of functions that emit diagnostic messages and only need to
/// communicate success to the parent.
type ReportedResult<T> = Result<T, ()>;

/// An abstraction around concrete parsers.
///
/// The lifetime `'n` represents nodes allocated into the the AST node arena.
trait AbstractParser<'n> {
    fn peek(&mut self, offset: usize) -> TokenAndSpan;
    fn bump(&mut self);
    fn skip(&mut self);
    fn consumed(&self) -> usize;
    fn last_span(&self) -> Span;
    fn add_diag(&mut self, diag: DiagBuilder2);
    fn severity(&self) -> Severity;

    fn try_eat_ident(&mut self) -> Option<(Name, Span)> {
        match self.peek(0) {
            (Ident(name), span) => {
                self.bump();
                Some((name, span))
            }
            (EscIdent(name), span) => {
                self.bump();
                Some((name, span))
            }
            _ => None,
        }
    }

    fn eat_ident_or(&mut self, msg: &str) -> ParseResult<(Name, Span)> {
        match self.peek(0) {
            (Ident(name), span) => {
                self.bump();
                Ok((name, span))
            }
            (EscIdent(name), span) => {
                self.bump();
                Ok((name, span))
            }
            (tkn, span) => {
                Err(DiagBuilder2::error(format!("expected {} before `{}`", msg, tkn)).span(span))
            }
        }
    }

    fn eat_ident(&mut self, msg: &str) -> ReportedResult<(Name, Span)> {
        match self.peek(0) {
            (Ident(name), span) => {
                self.bump();
                Ok((name, span))
            }
            (EscIdent(name), span) => {
                self.bump();
                Ok((name, span))
            }
            (tkn, span) => {
                self.add_diag(
                    DiagBuilder2::error(format!("expected {} before `{}`", msg, tkn)).span(span),
                );
                Err(())
            }
        }
    }

    fn is_ident(&mut self) -> bool {
        match self.peek(0).0 {
            Ident(_) | EscIdent(_) => true,
            _ => false,
        }
    }

    fn require(&mut self, expect: Token) -> Result<(), DiagBuilder2> {
        match self.peek(0) {
            (actual, _) if actual == expect => {
                self.bump();
                Ok(())
            }
            (wrong, span) => Err(DiagBuilder2::error(format!(
                "expected `{}`, but found `{}` instead",
                expect, wrong
            ))
            .span(span)),
        }
    }

    fn require_reported(&mut self, expect: Token) -> ReportedResult<()> {
        match self.require(expect) {
            Ok(x) => Ok(x),
            Err(e) => {
                self.add_diag(e);
                Err(())
            }
        }
    }

    fn try_eat(&mut self, expect: Token) -> bool {
        match self.peek(0) {
            (actual, _) if actual == expect => {
                self.bump();
                true
            }
            _ => false,
        }
    }

    // fn recover(&mut self, terminators: &[Token], eat_terminator: bool) {
    //  // println!("recovering to {:?}", terminators);
    //  loop {
    //      match self.peek(0) {
    //          (Eof, _) => return,
    //          (tkn, _) => {
    //              for t in terminators {
    //                  if *t == tkn {
    //                      if eat_terminator {
    //                          self.skip();
    //                      }
    //                      return;
    //                  }
    //              }
    //              self.skip();
    //          }
    //      }
    //  }
    // }

    fn recover_balanced(&mut self, terminators: &[Token], eat_terminator: bool) {
        // println!("recovering (balanced) to {:?}", terminators);
        let mut stack = Vec::new();
        loop {
            let (tkn, sp) = self.peek(0);
            if stack.is_empty() {
                for t in terminators {
                    if *t == tkn {
                        if eat_terminator {
                            self.skip();
                        }
                        return;
                    }
                }
            }

            match tkn {
                OpenDelim(x) => stack.push(x),
                CloseDelim(x) => {
                    if let Some(open) = stack.pop() {
                        if open != x {
                            self.add_diag(DiagBuilder2::fatal(format!("found closing `{}` which is not the complement to the previous opening `{}`", CloseDelim(x), OpenDelim(open))).span(sp));
                            break;
                        }
                    } else {
                        self.add_diag(
                            DiagBuilder2::fatal(format!(
                                "found closing `{}` without an earlier opening `{}`",
                                CloseDelim(x),
                                OpenDelim(x)
                            ))
                            .span(sp),
                        );
                        break;
                    }
                }
                Eof => break,
                _ => (),
            }
            self.skip();
        }
    }

    fn is_fatal(&self) -> bool {
        self.severity() >= Severity::Fatal
    }

    fn is_error(&self) -> bool {
        self.severity() >= Severity::Error
    }

    fn anticipate(&mut self, tokens: &[Token]) -> ReportedResult<()> {
        let (tkn, sp) = self.peek(0);
        for t in tokens {
            if *t == tkn {
                return Ok(());
            }
        }
        self.add_diag(
            DiagBuilder2::error(format!(
                "expected {:?}, but found {:?} instead",
                tokens, tkn
            ))
            .span(sp),
        );
        Err(())
    }
}

struct Parser<'a, 'n> {
    input: Lexer<'a>,
    queue: VecDeque<TokenAndSpan>,
    diagnostics: Vec<DiagBuilder2>,
    last_span: Span,
    severity: Severity,
    consumed: usize,
    arena_dummy: std::marker::PhantomData<&'n ()>,
}

impl<'a, 'n> AbstractParser<'n> for Parser<'a, 'n> {
    fn peek(&mut self, offset: usize) -> TokenAndSpan {
        self.ensure_queue_filled(offset);
        if offset < self.queue.len() {
            self.queue[offset]
        } else {
            *self
                .queue
                .back()
                .expect("At least an Eof token should be in the queue")
        }
    }

    fn bump(&mut self) {
        if self.queue.is_empty() {
            self.ensure_queue_filled(1);
        }
        if let Some((_, sp)) = self.queue.pop_front() {
            self.last_span = sp;
            self.consumed += 1;
        }
    }

    fn skip(&mut self) {
        self.bump()
    }

    fn consumed(&self) -> usize {
        self.consumed
    }

    fn last_span(&self) -> Span {
        self.last_span
    }

    fn add_diag(&mut self, diag: DiagBuilder2) {
        eprintln!("");
        eprintln!("{}", diag);

        // Emit a backtrace for this diagnostic.
        if diag.get_severity() >= Severity::Warning {
            trace!(
                "Diagnostic triggered here:\n{:?}",
                backtrace::Backtrace::new()
            );
        }

        // Keep track of the worst diagnostic severity we've encountered, such
        // that parsing can be aborted accordingly.
        if diag.get_severity() > self.severity {
            self.severity = diag.get_severity();
        }
        self.diagnostics.push(diag);
    }

    fn severity(&self) -> Severity {
        self.severity
    }
}

impl Parser<'_, '_> {
    fn new(input: Lexer) -> Parser {
        Parser {
            input: input,
            queue: VecDeque::new(),
            diagnostics: Vec::new(),
            last_span: INVALID_SPAN,
            severity: Severity::Note,
            consumed: 0,
            arena_dummy: Default::default(),
        }
    }

    fn ensure_queue_filled(&mut self, min_tokens: usize) {
        if let Some(&(Eof, _)) = self.queue.back() {
            return;
        }
        while self.queue.len() <= min_tokens {
            match self.input.next_token() {
                Ok((Eof, sp)) => self.queue.push_back((Eof, sp)),
                Ok(tkn) => self.queue.push_back(tkn),
                Err(x) => self.add_diag(x),
            }
        }
    }
}

/// Parses the opening delimiter, calls the `inner` function, and parses the
/// closing delimiter. Properly recovers to and including the closing
/// delimiter if the `inner` function throws an error.
fn flanked<'n, R, F>(
    p: &mut dyn AbstractParser<'n>,
    delim: DelimToken,
    mut inner: F,
) -> ReportedResult<R>
where
    F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R>,
{
    p.require_reported(OpenDelim(delim))?;
    match inner(p) {
        Ok(r) => match p.require_reported(CloseDelim(delim)) {
            Ok(_) => Ok(r),
            Err(e) => {
                p.recover_balanced(&[CloseDelim(delim)], true);
                Err(e)
            }
        },
        Err(e) => {
            p.recover_balanced(&[CloseDelim(delim)], true);
            Err(e)
        }
    }
}

/// If the opening delimiter is present, consumes it, calls the `inner`
/// function, and parses the closing delimiter. Properly recovers to and
/// including the closing delimiter if the `inner` function throws an error.
/// If the opening delimiter is not present, returns `None`.
fn try_flanked<'n, R, F>(
    p: &mut dyn AbstractParser<'n>,
    delim: DelimToken,
    inner: F,
) -> ReportedResult<Option<R>>
where
    F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R>,
{
    if p.peek(0).0 == OpenDelim(delim) {
        flanked(p, delim, inner).map(|r| Some(r))
    } else {
        Ok(None)
    }
}

/// Parse a comma-separated list of items, until a terminator token has been
/// reached. The terminator is not consumed.
fn comma_list<'n, R, F, T>(
    p: &mut dyn AbstractParser<'n>,
    mut term: T,
    msg: &str,
    mut item: F,
) -> ReportedResult<Vec<R>>
where
    F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R>,
    T: Predicate,
{
    let mut v = Vec::new();
    while !p.is_fatal() && p.peek(0).0 != Eof && !term.matches(p) {
        // Parse the item.
        match item(p) {
            Ok(x) => v.push(x),
            Err(e) => {
                term.recover(p, false);
                return Err(e);
            }
        }

        // Try to match the terminator. If it does not, consume a comma and
        // catch the case where the comma is immediately followed by the
        // terminator (superfluous terminator).
        if term.matches(p) {
            break;
        } else if p.try_eat(Comma) {
            if term.matches(p) {
                let q = p.last_span();
                p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(q));
                break;
            }
        } else {
            let sp = p.peek(0).1;
            p.add_diag(
                DiagBuilder2::error(format!("expected , or {} after {}", term.describe(), msg))
                    .span(sp),
            );
            term.recover(p, false);
            return Err(());
        }
    }
    Ok(v)
}

/// Same as `comma_list`, but at least one item is required.
fn comma_list_nonempty<'n, R, F, T>(
    p: &mut dyn AbstractParser<'n>,
    term: T,
    msg: &str,
    item: F,
) -> ReportedResult<Vec<R>>
where
    F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R>,
    T: Predicate,
{
    let q = p.peek(0).1;
    let v = comma_list(p, term, msg, item)?;
    if v.is_empty() {
        p.add_diag(DiagBuilder2::error(format!("expected at least one {}", msg)).span(q));
        Err(())
    } else {
        Ok(v)
    }
}

fn repeat_until<'n, R, F>(
    p: &mut dyn AbstractParser<'n>,
    term: Token,
    mut item: F,
) -> ReportedResult<Vec<R>>
where
    F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R>,
{
    let mut v = Vec::new();
    while p.peek(0).0 != term && p.peek(0).0 != Eof {
        match item(p) {
            Ok(x) => v.push(x),
            Err(_) => {
                p.recover_balanced(&[term], false);
                break;
            }
        }
    }
    Ok(v)
}

fn recovered<'n, R, F>(
    p: &mut dyn AbstractParser<'n>,
    term: Token,
    mut item: F,
) -> ReportedResult<R>
where
    F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R>,
{
    match item(p) {
        Ok(x) => Ok(x),
        Err(e) => {
            p.recover_balanced(&[term], false);
            Err(e)
        }
    }
}

/// Speculatively apply a parse function. If it fails, the parser `p` is left
/// untouched. If it succeeds, `p` is in the same state as if `parse` was called
/// on it directly. Use a ParallelParser for better error reporting.
#[allow(dead_code)]
fn r#try<'n, R, F>(p: &mut dyn AbstractParser<'n>, mut parse: F) -> Option<R>
where
    F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R>,
{
    let mut bp = BranchParser::new(p);
    match parse(&mut bp) {
        Ok(r) => {
            bp.commit();
            Some(r)
        }
        Err(_) => None,
    }
}

/// Consumes a `Ident` or `EscIdent` token, wrapping it in a `ast::Identifier`.
fn parse_identifier<'n, M: std::fmt::Display>(
    p: &mut dyn AbstractParser<'n>,
    msg: M,
) -> ReportedResult<ast::Identifier> {
    parse_identifier_name(p, msg).map(|n| ast::Identifier {
        span: n.span,
        name: n.value,
    })
}

/// Consumes a `Ident` or `EscIdent` token, wrapping it in a `Spanned<Name>`.
fn parse_identifier_name<'n, M: std::fmt::Display>(
    p: &mut dyn AbstractParser<'n>,
    msg: M,
) -> ReportedResult<Spanned<Name>> {
    let (tkn, span) = p.peek(0);
    match tkn {
        Ident(n) | EscIdent(n) => {
            p.bump();
            Ok(Spanned::new(n, span))
        }
        x => {
            p.add_diag(
                DiagBuilder2::error(format!("expected {}, but found `{}` instead", msg, x))
                    .span(span),
            );
            Err(())
        }
    }
}

fn try_identifier<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Option<ast::Identifier>> {
    let (tkn, span) = p.peek(0);
    match tkn {
        Ident(n) | EscIdent(n) => {
            p.bump();
            Ok(Some(ast::Identifier {
                span: span,
                name: n,
            }))
        }
        _ => Ok(None),
    }
}

trait Predicate {
    fn matches(&mut self, _: &mut dyn AbstractParser<'_>) -> bool;
    fn recover(&mut self, _: &mut dyn AbstractParser<'_>, consume: bool);
    fn describe(&self) -> String;
}

impl Predicate for Token {
    fn matches(&mut self, p: &mut dyn AbstractParser<'_>) -> bool {
        p.peek(0).0 == *self
    }

    fn recover(&mut self, p: &mut dyn AbstractParser<'_>, consume: bool) {
        p.recover_balanced(&[*self], consume)
    }

    fn describe(&self) -> String {
        self.as_str().into()
    }
}

struct FuncPredicate<
    M: FnMut(&mut dyn AbstractParser<'_>) -> bool,
    R: FnMut(&mut dyn AbstractParser<'_>, bool),
> {
    match_func: M,
    recover_func: R,
    desc: &'static str,
}

impl<
        M: FnMut(&mut dyn AbstractParser<'_>) -> bool,
        R: FnMut(&mut dyn AbstractParser<'_>, bool),
    > Predicate for FuncPredicate<M, R>
{
    fn matches(&mut self, p: &mut dyn AbstractParser<'_>) -> bool {
        (self.match_func)(p)
    }

    fn recover(&mut self, p: &mut dyn AbstractParser<'_>, consume: bool) {
        (self.recover_func)(p, consume)
    }

    fn describe(&self) -> String {
        self.desc.into()
    }
}

pub fn parse(input: Lexer) -> Result<Root, ()> {
    let mut p = Parser::new(input);
    let root = parse_source_text(&mut p);
    if p.is_error() {
        Err(())
    } else {
        Ok(root)
    }
}

fn parse_source_text<'n>(p: &mut dyn AbstractParser<'n>) -> Root<'n> {
    let mut span = p.peek(0).1;
    let mut root = RootData {
        timeunits: Timeunit {
            unit: None,
            prec: None,
        },
        items: Vec::new(),
    };

    // Parse the optional timeunits declaration.
    match parse_time_units(p) {
        Ok(x) => root.timeunits = x,
        Err(()) => (),
    }

    // Parse the descriptions in the source text.
    while !p.is_fatal() && p.peek(0).0 != Eof {
        match parse_hierarchy_item(p) {
            Ok(item) => root.items.push(item),
            Err(()) => (), // parse_item handles recovery, so no need to do anything here
        }
    }

    span.expand(p.last_span());
    Root::new(span, root)
}

fn parse_time_units<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Timeunit> {
    let mut unit = None;
    let mut prec = None;
    while p.peek(0).0 == Keyword(Kw::Timeunit) || p.peek(0).0 == Keyword(Kw::Timeprecision) {
        recovered(p, Semicolon, |p| {
            if p.try_eat(Keyword(Kw::Timeunit)) {
                unit = Some(parse_time_literal(p)?);
                if p.try_eat(Operator(Op::Div)) {
                    prec = Some(parse_time_literal(p)?);
                }
            } else if p.try_eat(Keyword(Kw::Timeprecision)) {
                prec = Some(parse_time_literal(p)?);
            } else {
                unreachable!();
            }
            Ok(())
        })?;
        p.require_reported(Semicolon)?;
    }

    Ok(Timeunit { unit, prec })
}

fn parse_time_literal<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Spanned<Lit>> {
    let (tkn, sp) = p.peek(0);
    match tkn {
        Literal(lit @ Time(..)) => {
            p.bump();
            Ok(Spanned::new(lit, sp))
        }
        _ => {
            p.add_diag(
                DiagBuilder2::error(format!("expected time literal, instead got `{}`", tkn))
                    .span(sp),
            );
            Err(())
        }
    }
}

/// Convert a token to the corresponding lifetime. Yields `None` if the token
/// does not correspond to a lifetime.
fn as_lifetime(tkn: Token) -> Option<Lifetime> {
    match tkn {
        Keyword(Kw::Static) => Some(Lifetime::Static),
        Keyword(Kw::Automatic) => Some(Lifetime::Automatic),
        _ => None,
    }
}

fn parse_interface_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<IntfDecl<'n>> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Interface))?;
    let result = recovered(p, Keyword(Kw::Endinterface), |p| {
        // Eat the optional lifetime.
        let lifetime = match as_lifetime(p.peek(0).0) {
            Some(l) => {
                p.bump();
                l
            }
            None => Lifetime::Static,
        };

        // Eat the interface name.
        let (name, name_sp) = p.eat_ident("interface name")?;

        // TODO: Parse package import declarations.

        // Eat the parameter port list.
        let param_ports = if p.try_eat(Hashtag) {
            parse_parameter_port_list(p)?
        } else {
            Vec::new()
        };

        // Eat the optional list of ports.
        let ports = if p.try_eat(OpenDelim(Paren)) {
            parse_port_list(p)?
        } else {
            Vec::new()
        };

        // Eat the semicolon at the end of the header.
        if !p.try_eat(Semicolon) {
            let q = p.peek(0).1.end();
            p.add_diag(
                DiagBuilder2::error(format!(
                    "Missing semicolon \";\" after header of interface \"{}\"",
                    name
                ))
                .span(q),
            );
        }

        // Eat the items in the interface.
        let mut items = Vec::new();
        while !p.is_fatal() && p.peek(0).0 != Keyword(Kw::Endinterface) && p.peek(0).0 != Eof {
            if p.try_eat(Semicolon) {
                continue;
            }
            items.push(parse_hierarchy_item(p)?);
        }

        span.expand(p.last_span());
        Ok(IntfDecl {
            span: span,
            lifetime: lifetime,
            name: name,
            name_span: name_sp,
            params: param_ports,
            ports: ports,
            items: items,
        })
    });
    p.require_reported(Keyword(Kw::Endinterface))?;
    result
}

fn parse_parameter_port_list<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Vec<ParamDecl<'n>>> {
    let mut local = false;

    flanked(p, Paren, |p| {
        comma_list(p, CloseDelim(Paren), "parameter port", |p| {
            // Parse the optional `parameter` or `localparam` keyword. If none is
            // provided, the previous scope is assumed.
            let mut outer_span = p.peek(0).1;
            match p.peek(0).0 {
                Keyword(Kw::Parameter) => {
                    p.bump();
                    local = false;
                }
                Keyword(Kw::Localparam) => {
                    p.bump();
                    local = true;
                }
                _ => (),
            };

            // If the next token is the `type` keyword, this is a type parameter.
            // Otherwise this is a value parameter.
            let kind = if p.try_eat(Keyword(Kw::Type)) {
                let mut span = p.peek(0).1;
                let name = parse_identifier(p, "parameter name")?;
                let ty = if p.try_eat(Operator(Op::Assign)) {
                    Some(parse_explicit_type(p)?)
                } else {
                    None
                };
                p.anticipate(&[Comma, CloseDelim(Paren)])?;
                span.expand(p.last_span());
                ast::ParamKind::Type(vec![ast::ParamTypeDecl {
                    span: span,
                    name: name,
                    ty: ty,
                }])
            } else {
                // Use a parallel parser to distinguish between the explicit and
                // implicit type versions of the declaration.
                let mut pp = ParallelParser::new();
                pp.add("explicit type", |p| {
                    let ty = parse_explicit_type(p)?;
                    tail(p, ty)
                });
                pp.add("implicit type", |p| {
                    let ty = parse_implicit_type(p)?;
                    tail(p, ty)
                });

                fn tail<'n>(
                    p: &mut dyn AbstractParser<'n>,
                    ty: Type<'n>,
                ) -> ReportedResult<ast::ParamValueDecl<'n>> {
                    let mut span = p.peek(0).1;
                    let name = parse_identifier(p, "parameter name")?;
                    let (dims, _) = parse_optional_dimensions(p)?;
                    let expr = if p.try_eat(Operator(Op::Assign)) {
                        Some(parse_expr(p)?)
                    } else {
                        None
                    };
                    p.anticipate(&[Comma, CloseDelim(Paren)])?;
                    span.expand(p.last_span());
                    Ok(ast::ParamValueDecl {
                        span: span,
                        ty: ty,
                        name: name,
                        dims: dims,
                        expr: expr,
                    })
                }

                ast::ParamKind::Value(vec![pp.finish(p, "explicit or implicit type")?])
            };

            outer_span.expand(p.last_span());
            Ok(ast::ParamDecl {
                span: outer_span,
                local: local,
                kind: kind,
            })
        })
    })
}

/// Parse a module declaration, assuming that the leading `module` keyword has
/// already been consumed.
fn parse_module_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ModDecl<'n>> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Module))?;
    let result = recovered(p, Keyword(Kw::Endmodule), |p| {
        // Eat the optional lifetime.
        let lifetime = match as_lifetime(p.peek(0).0) {
            Some(l) => {
                p.bump();
                l
            }
            None => Lifetime::Static,
        };

        // Eat the module name.
        let (name, name_sp) = p.eat_ident("module name")?;

        // TODO: Parse package import declarations.
        // Eat the optional package import declarations.
        let mut imports = vec![];
        while p.peek(0).0 == Keyword(Kw::Import) {
            imports.push(parse_import_decl(p)?);
        }

        // Eat the optional parameter port list.
        let params = if p.try_eat(Hashtag) {
            parse_parameter_port_list(p)?
        } else {
            Vec::new()
        };

        // Eat the optional list of ports. Not having such a list requires the ports
        // to be defined further down in the body of the module.
        let ports = if p.try_eat(OpenDelim(Paren)) {
            parse_port_list(p)?
        } else {
            Vec::new()
        };

        // Eat the semicolon after the header.
        if !p.try_eat(Semicolon) {
            let q = p.peek(0).1.end();
            p.add_diag(
                DiagBuilder2::error(format!("Missing ; after header of module \"{}\"", name))
                    .span(q),
            );
        }

        // Parse the module items.
        let mut items = Vec::new();
        while !p.is_fatal() && p.peek(0).0 != Keyword(Kw::Endmodule) && p.peek(0).0 != Eof {
            if p.try_eat(Semicolon) {
                continue;
            }
            items.push(parse_hierarchy_item(p)?);
        }

        span.expand(p.last_span());
        Ok(ModDecl {
            span,
            lifetime,
            name,
            name_span: name_sp,
            imports,
            params,
            ports,
            items,
        })
    });
    let sp = p.peek(0).1;
    p.require_reported(Keyword(Kw::Endmodule))?;
    if p.try_eat(Colon) {
        p.eat_ident("module name")?;
    }
    result
}

fn parse_package_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<PackageDecl<'n>> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Package))?;
    let result = recovered(p, Keyword(Kw::Endpackage), |p| {
        // Parse the optional lifetime.
        let lifetime = match as_lifetime(p.peek(0).0) {
            Some(x) => {
                p.bump();
                x
            }
            None => Lifetime::Static,
        };

        // Parse the package name.
        let (name, name_span) = p.eat_ident("package name")?;
        p.require_reported(Semicolon)?;

        // TODO: Parse the optional timeunits declaration.
        let timeunits = Timeunit {
            unit: None,
            prec: None,
        };

        // Parse the package items.
        let mut items = Vec::new();
        while !p.is_fatal() && p.peek(0).0 != Keyword(Kw::Endpackage) && p.peek(0).0 != Eof {
            if p.try_eat(Semicolon) {
                continue;
            }
            items.push(parse_hierarchy_item(p)?);
        }

        span.expand(p.last_span());
        Ok(PackageDecl {
            span: span,
            lifetime: lifetime,
            name: name,
            name_span: name_span,
            timeunits: timeunits,
            items: items,
        })
    });
    p.require_reported(Keyword(Kw::Endpackage))?;
    if p.try_eat(Colon) {
        p.eat_ident("package name")?;
    }
    result
}

fn parse_program_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<()> {
    p.require_reported(Keyword(Kw::Program))?;
    let result = recovered(p, Keyword(Kw::Endprogram), |p| {
        let q = p.peek(0).1;
        p.add_diag(DiagBuilder2::error("Don't know how to parse program declarations").span(q));
        Err(())
    });
    p.require_reported(Keyword(Kw::Endprogram))?;
    result
}

fn parse_hierarchy_item<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Item<'n>> {
    // Consume optional leading label.
    if p.is_ident() && p.peek(1).0 == Colon {
        p.bump();
        p.bump();
    }

    // First attempt the simple cases where a keyword reliably identifies the
    // following item.
    let class_follows = p.peek(1).0 == Keyword(Kw::Class);
    match p.peek(0).0 {
        Keyword(Kw::Module) => return parse_module_decl(p).map(Item::ModuleDecl),
        Keyword(Kw::Interface) | Keyword(Kw::Virtual) if class_follows => {
            return parse_class_decl(p).map(Item::ClassDecl)
        }
        Keyword(Kw::Class) => return parse_class_decl(p).map(Item::ClassDecl),
        Keyword(Kw::Interface) => return parse_interface_decl(p).map(Item::InterfaceDecl),
        Keyword(Kw::Package) => return parse_package_decl(p).map(Item::PackageDecl),
        Keyword(Kw::Program) => return parse_program_decl(p).map(Item::ProgramDecl),

        Keyword(Kw::Localparam) | Keyword(Kw::Parameter) => {
            let decl = parse_param_decl(p, false)?;
            p.require_reported(Semicolon)?;
            return Ok(Item::ParamDecl(decl));
        }
        Keyword(Kw::Modport) => return parse_modport_decl(p).map(|x| Item::ModportDecl(x)),
        Keyword(Kw::Typedef) => return parse_typedef(p).map(|x| Item::Typedef(x)),
        Keyword(Kw::Import) => return parse_import_decl(p).map(|x| Item::ImportDecl(x)),

        // Structured procedures as per IEEE 1800-2009 section 9.2
        Keyword(Kw::Initial) => {
            return parse_procedure(p, ProcedureKind::Initial).map(|x| Item::Procedure(x));
        }
        Keyword(Kw::Always) => {
            return parse_procedure(p, ProcedureKind::Always).map(|x| Item::Procedure(x));
        }
        Keyword(Kw::AlwaysComb) => {
            return parse_procedure(p, ProcedureKind::AlwaysComb).map(|x| Item::Procedure(x));
        }
        Keyword(Kw::AlwaysLatch) => {
            return parse_procedure(p, ProcedureKind::AlwaysLatch).map(|x| Item::Procedure(x));
        }
        Keyword(Kw::AlwaysFf) => {
            return parse_procedure(p, ProcedureKind::AlwaysFf).map(|x| Item::Procedure(x));
        }
        Keyword(Kw::Final) => {
            return parse_procedure(p, ProcedureKind::Final).map(|x| Item::Procedure(x));
        }
        Keyword(Kw::Function) | Keyword(Kw::Task) => {
            return parse_subroutine_decl(p).map(|x| Item::SubroutineDecl(x));
        }

        // Port declarations
        Keyword(Kw::Inout) | Keyword(Kw::Input) | Keyword(Kw::Output) | Keyword(Kw::Ref) => {
            return parse_port_decl(p).map(|x| Item::PortDecl(x));
        }

        // Continuous assign
        Keyword(Kw::Assign) => {
            return parse_continuous_assign(p).map(|x| Item::ContAssign(x));
        }

        // Genvar declaration
        Keyword(Kw::Genvar) => {
            p.bump();
            let decl = comma_list_nonempty(p, Semicolon, "genvar declaration", parse_genvar_decl)?;
            p.require_reported(Semicolon)?;
            return Ok(Item::GenvarDecl(decl));
        }

        // Generate region and constructs
        Keyword(Kw::Generate) => {
            let mut span = p.peek(0).1;
            p.bump();
            let items = repeat_until(p, Keyword(Kw::Endgenerate), parse_generate_item)?;
            p.require_reported(Keyword(Kw::Endgenerate))?;
            span.expand(p.last_span());
            return Ok(Item::GenerateRegion(span, items));
        }
        Keyword(Kw::For) => return parse_generate_for(p).map(|x| Item::GenerateFor(x)),
        Keyword(Kw::If) => return parse_generate_if(p).map(|x| Item::GenerateIf(x)),
        Keyword(Kw::Case) => return parse_generate_case(p).map(|x| Item::GenerateCase(x)),

        // Assertions
        Keyword(Kw::Assert)
        | Keyword(Kw::Assume)
        | Keyword(Kw::Cover)
        | Keyword(Kw::Expect)
        | Keyword(Kw::Restrict) => return parse_assertion(p).map(|x| Item::Assertion(x)),
        Semicolon => {
            p.bump();
            return Ok(Item::Dummy);
        }

        // Default clocking and disable declarations.
        Keyword(Kw::Default) => {
            p.bump();
            let mut span = p.last_span();
            if p.try_eat(Keyword(Kw::Clocking)) {
                let name = p.eat_ident("clocking identifier")?;
                p.require_reported(Semicolon)?;
                span.expand(p.last_span());
                return Ok(Item::Dummy);
            }
            if p.try_eat(Keyword(Kw::Disable)) {
                p.require_reported(Keyword(Kw::Iff))?;
                let expr = parse_expr(p)?;
                p.require_reported(Semicolon)?;
                span.expand(p.last_span());
                return Ok(Item::Dummy);
            }
            p.add_diag(
                DiagBuilder2::error("expected `clocking` or `disable` after `default`").span(span),
            );
            p.recover_balanced(&[Semicolon], true);
            return Err(());
        }

        // Unsupported constructs as of now.
        SysIdent(..) => return parse_elab_system_task(p).map(|_| Item::Dummy),

        _ => (),
    }

    // Handle the possibly ambiguous cases.
    let mut pp = ParallelParser::new();
    pp.add_greedy("net declaration", |p| {
        parse_net_decl(p).map(|d| Item::NetDecl(d))
    });
    pp.add("instantiation", |p| parse_inst(p).map(|i| Item::Inst(i)));
    pp.add("variable declaration", |p| {
        parse_var_decl(p).map(|d| Item::VarDecl(d))
    });
    let res = pp.finish(p, "hierarchy item");
    if res.is_err() {
        p.recover_balanced(&[Semicolon], true);
    }
    res
}

fn parse_elab_system_task<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<()> {
    let mut span = p.peek(0).1;
    let name = match p.peek(0).0 {
        SysIdent(name) => name,
        _ => unreachable!(),
    };
    p.recover_balanced(&[Semicolon], true);
    span.expand(p.last_span());
    p.add_diag(DiagBuilder2::warning("unsupported elaboration system task").span(span));
    Ok(())
}

fn parse_localparam_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<()> {
    p.require_reported(Keyword(Kw::Localparam))?;
    // TODO: Parse data type or implicit type.

    // Eat the list of parameter assignments.
    loop {
        // parameter_identifier { unpacked_dimension } [ = constant_param_expression ]
        let (name, name_sp) = match p.eat_ident_or("parameter name") {
            Ok(x) => x,
            Err(e) => {
                p.add_diag(e);
                return Err(());
            }
        };

        // TODO: Eat the unpacked dimensions.

        // Eat the optional assignment.
        if p.try_eat(Operator(Op::Assign)) {
            match parse_expr(p) {
                Ok(_) => (),
                Err(_) => p.recover_balanced(&[Comma, Semicolon], false),
            }
        }

        // Eat the trailing comma or semicolon.
        match p.peek(0) {
            (Comma, sp) => {
                p.bump();

                // A closing parenthesis indicates that the previous
                // comma was superfluous. Report the issue but continue
                // gracefully.
                if p.peek(0).0 == Semicolon {
                    // TODO: This should be an error in pedantic mode.
                    p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(sp));
                    break;
                }
            }
            (Semicolon, _) => break,
            (x, sp) => {
                p.add_diag(
                    DiagBuilder2::error(format!("expected , or ; after localparam, found {}", x))
                        .span(sp),
                );
                return Err(());
            }
        }
    }
    p.require_reported(Semicolon)?;
    Ok(())
}

fn parse_parameter_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<()> {
    p.require_reported(Keyword(Kw::Parameter))?;

    // Branch to try the explicit and implicit type version.
    let mut pp = ParallelParser::new();
    pp.add("explicit type", |p| {
        let ty = parse_explicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    pp.add("implicit type", |p| {
        let ty = parse_implicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    let (ty, ()) = pp.finish(p, "explicit or implicit type")?;

    fn tail<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<()> {
        let names = parse_parameter_names(p)?;
        p.require_reported(Semicolon)?;
        Ok(())
    }

    return Ok(());
}

fn parse_parameter_names<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Vec<()>> {
    let v = comma_list_nonempty(p, Semicolon, "parameter name", |p| {
        // Consume the parameter name and optional dimensions.
        let (name, name_sp) = p.eat_ident("parameter name")?;
        let (dims, _) = parse_optional_dimensions(p)?;

        // Parse the optional assignment.
        let expr = if p.try_eat(Operator(Op::Assign)) {
            Some(parse_expr(p)?)
        } else {
            None
        };

        Ok(())
    })?;
    Ok(v)
}

/// Parse a modport declaration.
///
/// ```text
/// modport_decl: "modport" modport_item {"," modport_item} ";"
/// modport_item: ident "(" modport_ports_decl {"," modport_ports_decl} ")"
/// modport_ports_decl:
///   port_direction modport_simple_port {"," modport_simple_port} |
///   ("import"|"export") modport_tf_port {"," modport_tf_port} |
///   "clocking" ident
/// modport_simple_port: ident | "." ident "(" [expr] ")"
/// ```
fn parse_modport_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::ModportDecl> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Modport))?;
    let items = comma_list_nonempty(p, Semicolon, "modport item", parse_modport_item)?;
    p.require_reported(Semicolon)?;
    span.expand(p.last_span());

    Ok(ast::ModportDecl {
        span: span,
        items: items,
    })

    // loop {
    //  parse_modport_item(p)?;
    //  match p.peek(0) {
    //      (Comma, sp) => {
    //          p.bump();
    //          if let (Semicolon, _) = p.peek(0) {
    //              p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(sp));
    //              break;
    //          } else {
    //              continue;
    //          }
    //      },
    //      (Semicolon, _) => break,
    //      (x, sp) => {
    //          p.add_diag(DiagBuilder2::error(format!("expected , or ; after modport declaration, got `{:?}`", x)).span(sp));
    //          return Err(());
    //      }
    //  }
    // }

    // Ok(())
}

/// Parse a modport item.
///
/// ```text
/// modport_item: ident "(" modport_ports_decl {"," modport_ports_decl} ")"
/// modport_ports_decl:
///   port_direction modport_simple_port {"," modport_simple_port} |
///   ("import"|"export") modport_tf_port {"," modport_tf_port} |
///   "clocking" ident
/// modport_simple_port: ident | "." ident "(" [expr] ")"
/// ```
fn parse_modport_item<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::ModportItem> {
    let mut span = p.peek(0).1;

    // Eat the modport item name.
    let name = parse_identifier(p, "modport name")?;

    // Eat the port declarations.
    let ports = flanked(p, Paren, |p| {
        comma_list(
            p,
            CloseDelim(Paren),
            "port declaration",
            parse_modport_port_decl,
        )
    })?;

    // // Eat the opening parenthesis.
    // if !p.try_eat(OpenDelim(Paren)) {
    //  let (tkn, q) = p.peek(0);
    //  p.add_diag(DiagBuilder2::error(format!("expected ( after modport name `{}`, got `{:?}`", name, tkn)).span(q));
    //  return Err(());
    // }

    span.expand(p.last_span());
    Ok(ast::ModportItem {
        span: span,
        name: name,
        ports: ports,
    })

    // // Parse the port declarations.
    // loop {
    //  match parse_modport_port_decl(p) {
    //      Ok(x) => x,
    //      Err(_) => {
    //          p.recover(&[CloseDelim(Paren)], true);
    //          return Err(());
    //      }
    //  }
    //  match p.peek(0) {
    //      (Comma, sp) => {
    //          p.bump();
    //          if let (CloseDelim(Paren), _) = p.peek(0) {
    //              p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(sp));
    //              break;
    //          } else {
    //              continue;
    //          }
    //      }
    //      (CloseDelim(Paren), _) => break,
    //      (x, sp) => {
    //          p.add_diag(DiagBuilder2::error(format!("expected , or ) after port declaration, got `{:?}`", x)).span(sp));
    //          return Err(());
    //      }
    //  }
    // }

    // // Eat the closing parenthesis.
    // if !p.try_eat(CloseDelim(Paren)) {
    //  let (tkn, q) = p.peek(0);
    //  p.add_diag(DiagBuilder2::error(format!("expected ) after port list of modport `{}`, got `{:?}`", name, tkn)).span(q));
    //  return Err(());
    // }

    // Ok(())
}

/// ```text
/// modport_ports_decl:
///   port_direction modport_simple_port {"," modport_simple_port} |
///   ("import"|"export") modport_tf_port {"," modport_tf_port} |
///   "clocking" ident
/// modport_simple_port: ident | "." ident "(" [expr] ")"
/// ```
fn parse_modport_port_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::ModportPort> {
    let (tkn, span) = p.peek(0);

    // Attempt to parse a simple port introduced by one of the port direction
    // keywords.
    if let Some(dir) = as_port_direction(tkn) {
        p.bump();
        loop {
            if p.try_eat(Period) {
                let name = parse_identifier(p, "port name")?;
                p.require_reported(OpenDelim(Paren))?;
                let expr = parse_expr(p)?;
                p.require_reported(CloseDelim(Paren))?;
            } else {
                let name = parse_identifier(p, "port name")?;
            }

            // Decide whether we should continue iterating and thus consuming
            // more simple ports. According to the grammar, a comma followed by
            // a keyword indicates a different port declaration, so we abort.
            // Otherwise, if the next item is a comma still, we continue
            // iteration. In all other cases, we assume the port declaration to
            // be done.
            match (p.peek(0).0, p.peek(1).0) {
                (Comma, Keyword(_)) => break,
                (Comma, _) => {
                    p.bump();
                    continue;
                }
                _ => break,
            }
        }
        return Ok(ast::ModportPort::Port);
    }

    // TODO: Parse modport_tf_port.

    // Attempt to parse a clocking declaration.
    if p.try_eat(Keyword(Kw::Clocking)) {
        // TODO: Parse modport_clocking_declaration.
        p.add_diag(DiagBuilder2::error("modport clocking declaration not implemented").span(span));
        return Err(());
    }

    // If we've come thus far, none of the above matched.
    p.add_diag(DiagBuilder2::error("expected port declaration").span(span));
    Err(())
}

/// Convert a token to the corresponding PortDir. The token may be one of the
/// keywords `input`, `output`, `inout`, or `ref`. Otherwise `None` is returned.
fn as_port_direction(tkn: Token) -> Option<PortDir> {
    match tkn {
        Keyword(Kw::Input) => Some(PortDir::Input),
        Keyword(Kw::Output) => Some(PortDir::Output),
        Keyword(Kw::Inout) => Some(PortDir::Inout),
        Keyword(Kw::Ref) => Some(PortDir::Ref),
        _ => None,
    }
}

/// Parse an implicit or explicit type. This is a catch-all function that will
/// always succeed unless one of the explicit types contains a syntax error. For
/// all other tokens the function will at least return an ImplicitType if none
/// could be consumed. You might have to use `parse_explicit_type` and
/// `parse_implicit_type` separately if the type is to be embedded in a larger
/// function. For example, a variable declaration with implicit type looks like
/// an explicit type at first glance. Only after reaching the trailing `[=,;]`
/// it becomes apparent that the explicit type was rather the name of the
/// variable. In this case, having to parallel parsers, one with explicit and
/// one with implicit type, can resolve the issue.
fn parse_data_type<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Type<'n>> {
    // Try to parse this as an explicit type.
    {
        let mut bp = BranchParser::new(p);
        match parse_explicit_type(&mut bp) {
            Ok(x) => {
                bp.commit();
                return Ok(x);
            }
            Err(_) => (),
        }
    }

    // Otherwise simply go with an implicit type, which basically always
    // succeeds.
    parse_implicit_type(p)
}

fn parse_explicit_type<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Type<'n>> {
    let mut span = p.peek(0).1;
    let data = parse_type_data(p)?;
    span.expand(p.last_span());
    let ty = parse_type_signing_and_dimensions(p, span, data)?;
    parse_type_suffix(p, ty)
}

fn parse_type_suffix<'n>(p: &mut dyn AbstractParser<'n>, ty: Type<'n>) -> ReportedResult<Type<'n>> {
    let (tkn, sp) = p.peek(0);
    match tkn {
        // Interfaces allow their internal modports and typedefs to be accessed
        // via the `.` operator.
        Period => {
            p.bump();
            let name = parse_identifier(p, "member type name")?;
            let subty = parse_type_signing_and_dimensions(
                p,
                sp,
                ScopedType {
                    ty: Box::new(ty),
                    member: true,
                    name: name,
                },
            )?;
            parse_type_suffix(p, subty)
        }

        // The `::` operator.
        Namespace => {
            p.bump();
            let name = parse_identifier(p, "type name")?;
            let subty = parse_type_signing_and_dimensions(
                p,
                sp,
                ScopedType {
                    ty: Box::new(ty),
                    member: false,
                    name: name,
                },
            )?;
            parse_type_suffix(p, subty)
        }

        // Classes can be specialized with a parameter list.
        Hashtag => {
            p.bump();
            let params = parse_parameter_assignments(p)?;
            let span = Span::union(sp, p.last_span());
            parse_type_suffix(
                p,
                ast::Type {
                    span: span,
                    data: ast::SpecializedType(Box::new(ty), params),
                    sign: ast::TypeSign::None,
                    dims: Vec::new(),
                },
            )
        }

        _ => Ok(ty),
    }
}

/// Parse an implicit type (`[signing] {dimensions}`).
fn parse_implicit_type<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Type<'n>> {
    let span = p.peek(0).1.begin().into();
    parse_type_signing_and_dimensions(p, span, ImplicitType)
}

/// Parse the optional signing keyword and packed dimensions that may follow a
/// data type. Wraps a previously parsed TypeData in a Type struct.
fn parse_type_signing_and_dimensions<'n>(
    p: &mut dyn AbstractParser<'n>,
    mut span: Span,
    data: TypeData<'n>,
) -> ReportedResult<Type<'n>> {
    // Parse the optional sign information.
    let sign = match p.peek(0).0 {
        Keyword(Kw::Signed) => {
            p.bump();
            TypeSign::Signed
        }
        Keyword(Kw::Unsigned) => {
            p.bump();
            TypeSign::Unsigned
        }
        _ => TypeSign::None,
    };

    // Parse the optional dimensions.
    let (dims, _) = parse_optional_dimensions(p)?;
    span.expand(p.last_span());

    Ok(Type {
        span: span,
        data: data,
        sign: sign,
        dims: dims,
    })
}

/// Parse the core type data of a type.
fn parse_type_data<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<TypeData<'n>> {
    let (tkn, sp) = p.peek(0);
    match tkn {
        Keyword(Kw::Void) => {
            p.bump();
            Ok(ast::VoidType)
        }
        Keyword(Kw::String) => {
            p.bump();
            Ok(ast::StringType)
        }
        Keyword(Kw::Chandle) => {
            p.bump();
            Ok(ast::ChandleType)
        }
        Keyword(Kw::Event) => {
            p.bump();
            Ok(ast::EventType)
        }
        // Keyword(Kw::Signed) => {
        //     p.bump();
        //     Ok(ast::ImplicitSignedType)
        // }
        // Keyword(Kw::Unsigned) => {
        //     p.bump();
        //     Ok(ast::ImplicitUnsignedType)
        // }

        // Integer Vector Types
        Keyword(Kw::Bit) => {
            p.bump();
            Ok(ast::BitType)
        }
        Keyword(Kw::Logic) => {
            p.bump();
            Ok(ast::LogicType)
        }
        Keyword(Kw::Reg) => {
            p.bump();
            Ok(ast::RegType)
        }

        // Integer Atom Types
        Keyword(Kw::Byte) => {
            p.bump();
            Ok(ast::ByteType)
        }
        Keyword(Kw::Shortint) => {
            p.bump();
            Ok(ast::ShortIntType)
        }
        Keyword(Kw::Int) => {
            p.bump();
            Ok(ast::IntType)
        }
        Keyword(Kw::Longint) => {
            p.bump();
            Ok(ast::LongIntType)
        }
        Keyword(Kw::Integer) => {
            p.bump();
            Ok(ast::IntegerType)
        }
        Keyword(Kw::Time) => {
            p.bump();
            Ok(ast::TimeType)
        }

        // Non-integer Types
        Keyword(Kw::Shortreal) => {
            p.bump();
            Ok(ast::ShortRealType)
        }
        Keyword(Kw::Real) => {
            p.bump();
            Ok(ast::RealType)
        }
        Keyword(Kw::Realtime) => {
            p.bump();
            Ok(ast::RealtimeType)
        }

        // Enumerations
        Keyword(Kw::Enum) => parse_enum_type(p),
        Keyword(Kw::Struct) | Keyword(Kw::Union) => parse_struct_type(p),

        // Built-in types
        Ident(n) if &*n.as_str() == "mailbox" => {
            p.bump();
            Ok(ast::MailboxType)
        }

        // Named types
        Ident(n) | EscIdent(n) => {
            p.bump();
            Ok(ast::NamedType(ast::Identifier { span: sp, name: n }))
        }

        // Virtual Interface Type
        Keyword(Kw::Virtual) => {
            p.bump();
            p.try_eat(Keyword(Kw::Interface));
            let (name, _) = p.eat_ident("virtual interface name")?;
            Ok(ast::VirtIntfType(name))
        }

        // type_reference ::= `type` `(` expression `)`
        // type_reference ::= `type` `(` data_type `)`
        Keyword(Kw::Type) => {
            p.bump();
            let arg = flanked(p, Paren, |p| parse_type_or_expr(p, &[CloseDelim(Paren)]))?;
            Ok(ast::TypeRef(Box::new(arg)))
        }

        _ => {
            let q = p.peek(0).1;
            p.add_diag(DiagBuilder2::error("expected type").span(q));
            return Err(());
        }
    }
}

fn parse_enum_type<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<TypeData<'n>> {
    // Consume the enum keyword.
    p.bump();

    // Parse the optional enum base type.
    let base = if p.peek(0).0 != OpenDelim(Brace) {
        Some(Box::new(parse_data_type(p)?))
    } else {
        None
    };

    // Parse the name declarations.
    let names = flanked(p, Brace, |p| {
        comma_list(p, CloseDelim(Brace), "enum name", parse_enum_name)
    })?;

    Ok(EnumType(base, names))
}

fn parse_enum_name<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<EnumName<'n>> {
    // Eat the name.
    let name = parse_identifier(p, "enum name")?;
    let mut span = name.span;

    // Parse the optional range.
    let range = try_flanked(p, Brack, parse_expr)?;

    // Parse the optional value.
    let value = if p.try_eat(Operator(Op::Assign)) {
        Some(parse_expr(p)?)
    } else {
        None
    };
    span.expand(p.last_span());

    Ok(EnumName {
        span: span,
        name: name,
        range: range,
        value: value,
    })
}

fn parse_struct_type<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<TypeData<'n>> {
    let q = p.peek(0).1;

    // Consume the "struct", "union", or "union tagged" keywords.
    let kind = match (p.peek(0).0, p.peek(1).0) {
        (Keyword(Kw::Struct), _) => {
            p.bump();
            StructKind::Struct
        }
        (Keyword(Kw::Union), Keyword(Kw::Tagged)) => {
            p.bump();
            p.bump();
            StructKind::TaggedUnion
        }
        (Keyword(Kw::Union), _) => {
            p.bump();
            StructKind::Union
        }
        _ => {
            p.add_diag(
                DiagBuilder2::error("expected `struct`, `union`, or `union tagged`").span(q),
            );
            return Err(());
        }
    };

    // Consume the optional "packed" keyword, followed by an optional signing
    // indication.
    let (packed, signing) = if p.try_eat(Keyword(Kw::Packed)) {
        (true, parse_signing(p))
    } else {
        (false, TypeSign::None)
    };

    // Parse the struct members.
    let members = flanked(p, Brace, |p| {
        repeat_until(p, CloseDelim(Brace), parse_struct_member)
    })?;

    Ok(StructType {
        kind: kind,
        packed: packed,
        signing: signing,
        members: members,
    })
}

fn parse_struct_member<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<StructMember<'n>> {
    let mut span = p.peek(0).1;

    // Parse the optional random qualifier.
    let rand_qualifier = match p.peek(0).0 {
        Keyword(Kw::Rand) => {
            p.bump();
            Some(RandomQualifier::Rand)
        }
        Keyword(Kw::Randc) => {
            p.bump();
            Some(RandomQualifier::Randc)
        }
        _ => None,
    };

    // Parse the data type of the member.
    let ty = parse_data_type(p)?;

    // Parse the list of names and assignments.
    let names = comma_list_nonempty(p, Semicolon, "member name", parse_variable_decl_assignment)?;

    p.require_reported(Semicolon)?;
    span.expand(p.last_span());

    Ok(StructMember {
        span: span,
        rand_qualifier: rand_qualifier,
        ty: Box::new(ty),
        names: names,
    })
}

fn try_signing<'n>(p: &mut dyn AbstractParser<'n>) -> Option<TypeSign> {
    match p.peek(0).0 {
        Keyword(Kw::Signed) => {
            p.bump();
            Some(TypeSign::Signed)
        }
        Keyword(Kw::Unsigned) => {
            p.bump();
            Some(TypeSign::Unsigned)
        }
        _ => None,
    }
}

fn parse_signing<'n>(p: &mut dyn AbstractParser<'n>) -> TypeSign {
    try_signing(p).unwrap_or(TypeSign::None)
}

fn parse_optional_dimensions<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<(Vec<TypeDim<'n>>, Span)> {
    let mut v = Vec::new();
    let mut span;
    if let Some((d, sp)) = try_dimension(p)? {
        span = sp;
        v.push(d);
    } else {
        return Ok((v, INVALID_SPAN));
    }
    while let Some((d, sp)) = try_dimension(p)? {
        v.push(d);
        span.expand(sp);
    }
    Ok((v, span))
}

fn try_dimension<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Option<(TypeDim<'n>, Span)>> {
    let mut span = Span::from(p.peek(0).1.begin());
    let dim = try_flanked(p, Brack, |p| {
        Ok(match p.peek(0).0 {
            // unsized_dimension ::= `[` `]`
            CloseDelim(Brack) => TypeDim::Unsized,
            // associative_dimension ::= `[` `*` `]`
            Operator(Op::Mul) => {
                p.bump();
                TypeDim::Associative(None)
            }
            // queue_dimension ::= `[` `$` `]`
            // queue_dimension ::= `[` `$` `:` constant_expression `]`
            Dollar => {
                p.bump();
                let expr = if p.try_eat(Colon) {
                    Some(parse_expr(p)?)
                } else {
                    None
                };
                TypeDim::Queue(expr)
            }
            _ => match parse_type_or_expr(p, &[Colon, CloseDelim(Brack)])? {
                // associative_dimension ::= '[' data_type ']'
                TypeOrExpr::Type(ty) => TypeDim::Associative(Some(ty)),
                // unpacked_dimension ::= '[' constant_expression ']'
                // unpacked_dimension ::= '[' constant_range ']'
                TypeOrExpr::Expr(expr) => {
                    if p.try_eat(Colon) {
                        let other = parse_expr(p)?;
                        TypeDim::Range(expr, other)
                    } else {
                        TypeDim::Expr(expr)
                    }
                }
            },
        })
    })?;
    span.expand(p.last_span());
    Ok(dim.map(|dim| (dim, span)))
}

fn parse_list_of_port_connections<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Vec<PortConn<'n>>> {
    comma_list(p, CloseDelim(Paren), "list of port connections", |p| {
        let mut span = p.peek(0).1;

        // A period introduces a named port connection. Otherwise this is an
        // unnamed connection.
        let kind = if p.try_eat(Period) {
            if p.try_eat(Operator(Op::Mul)) {
                // handle .* case
                ast::PortConnKind::Auto
            } else {
                let name = parse_identifier(p, "port name")?;
                // handle .name, .name(), and .name(expr) cases
                let mode = try_flanked(p, Paren, |p| {
                    Ok(if p.peek(0).0 != CloseDelim(Paren) {
                        ast::PortConnMode::Connected(parse_expr(p)?)
                    } else {
                        ast::PortConnMode::Unconnected
                    })
                })?
                .unwrap_or(ast::PortConnMode::Auto);
                ast::PortConnKind::Named(name, mode)
            }
        } else {
            ast::PortConnKind::Positional(parse_expr(p)?)
        };

        span.expand(p.last_span());
        Ok(ast::PortConn {
            span: span,
            kind: kind,
        })
    })
}

/// Parse either an expression or a type. Prefers expressions over types.
fn parse_type_or_expr<'n>(
    p: &mut dyn AbstractParser<'n>,
    terminators: &[Token],
) -> ReportedResult<ast::TypeOrExpr<'n>> {
    let terminators = Vec::from(terminators);
    let mut pp = ParallelParser::new();
    pp.add_greedy("expression", |p| {
        let expr = parse_expr(p)?;
        p.anticipate(&terminators)?;
        Ok(ast::TypeOrExpr::Expr(expr))
    });
    pp.add("type", |p| {
        let ty = parse_explicit_type(p)?;
        p.anticipate(&terminators)?;
        Ok(ast::TypeOrExpr::Type(ty))
    });
    pp.finish(p, "type or expression")
}

fn parse_expr<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Expr<'n>> {
    parse_expr_prec(p, Precedence::Min)
}

fn parse_expr_prec<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: Precedence,
) -> ReportedResult<Expr<'n>> {
    // TODO: Keep track of the location here and pass that to the
    // parse_expr_first and parse_expr_suffix calls further down. This will
    // allow the spans of those expressions to properly reflect the full span of
    // the expression, mitigating the following issue:
    //
    // assign foo = (operator_i = ALU_ABS) ? operand_a_neg : operand_a_i;
    //               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    //
    // Note the opening parenthesis `(` is not included in the expression's
    // span.

    // Parse class-new and dynamic-array-new expressions, which are used on the
    // right hand side of assignments.
    if p.try_eat(Keyword(Kw::New)) {
        let mut span = p.last_span();
        if let Some(dim_expr) = try_flanked(p, Brack, parse_expr)? {
            let expr = try_flanked(p, Paren, parse_expr)?;
            span.expand(p.last_span());
            return Ok(Expr::new(
                span,
                ArrayNewExpr(Box::new(dim_expr), expr.map(|x| Box::new(x))),
            ));
        } else {
            if let Some(args) = try_flanked(p, Paren, parse_call_args)? {
                span.expand(p.last_span());
                return Ok(Expr::new(span, ConstructorCallExpr(args)));
            } else {
                // Parse the optional expression.
                let mut bp = BranchParser::new(p);
                let expr = match parse_expr(&mut bp) {
                    Ok(x) => {
                        bp.commit();
                        Some(Box::new(x))
                    }
                    Err(_) => None,
                };
                span.expand(p.last_span());
                return Ok(Expr::new(span, ClassNewExpr(expr)));
            }
        }
    }

    // Try to parse a cast or pattern expression, which starts with an explicit
    // type, followed by an apostrophe.
    // pattern_expr ::= type? pattern
    // cast ::= type `'` `(` expr `)`
    {
        let mut bp = BranchParser::new(p);
        let mut span = bp.peek(0).1;
        let ty = parse_explicit_type(&mut bp);
        match (ty, bp.peek(0).0, bp.peek(1).0) {
            // type `'` `(` ...
            (Ok(ty), Apostrophe, OpenDelim(Paren)) => {
                bp.commit();
                p.require_reported(Apostrophe)?;
                let expr = flanked(p, Paren, parse_expr)?;
                span.expand(p.last_span());
                let cast = Expr::new(span, CastExpr(ty, Box::new(expr)));
                return parse_expr_suffix(p, cast, precedence);
            }
            // type `'` `{` ...
            (Ok(ty), Apostrophe, OpenDelim(Brace)) => {
                bp.commit();
                // Don't consume the apostrophe -- it's part of the pattern.
                let expr = parse_expr(p)?;
                span.expand(p.last_span());
                let cast = Expr::new(span, CastExpr(ty, Box::new(expr)));
                return parse_expr_suffix(p, cast, precedence);
            }
            _ => (),
        }
    }

    // Try to parse a sign cast expression, which starts with a `unsigned` or
    // `signed` keyword.
    if let Some(sign) = try_signing(p) {
        let mut span = p.last_span();
        let sign = Spanned::new(sign, span);
        p.require_reported(Apostrophe)?;
        let expr = flanked(p, Paren, parse_expr)?;
        span.expand(p.last_span());
        let cast = Expr::new(span, CastSignExpr(sign, Box::new(expr)));
        return parse_expr_suffix(p, cast, precedence);
    }

    // Otherwise treat this as a normal expression.
    let q = p.peek(0).1;
    // p.add_diag(DiagBuilder2::note(format!("expr_suffix with precedence {:?}", precedence)).span(q));
    let prefix = parse_expr_first(p, precedence)?;
    parse_expr_suffix(p, prefix, precedence)
}

fn parse_expr_suffix<'n>(
    p: &mut dyn AbstractParser<'n>,
    prefix: Expr<'n>,
    precedence: Precedence,
) -> ReportedResult<Expr<'n>> {
    // p.add_diag(DiagBuilder2::note(format!("expr_suffix with precedence {:?}", precedence)).span(prefix.span));

    // Try to parse the index and call expressions.
    let (tkn, sp) = p.peek(0);
    match tkn {
        // Index: "[" range_expression "]"
        OpenDelim(Brack) if precedence <= Precedence::Postfix => {
            p.bump();
            let expr = match parse_range_expr(p) {
                Ok(x) => x,
                Err(e) => {
                    p.recover_balanced(&[CloseDelim(Brack)], true);
                    return Err(e);
                }
            };
            p.require_reported(CloseDelim(Brack))?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                IndexExpr {
                    indexee: Box::new(prefix),
                    index: Box::new(expr),
                },
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // Call: "(" [list_of_arguments] ")"
        OpenDelim(Paren) if precedence <= Precedence::Postfix => {
            let args = flanked(p, Paren, parse_call_args)?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                CallExpr(Box::new(prefix), args),
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // expr "." ident
        Period if precedence <= Precedence::Scope => {
            p.bump();
            let (name, name_span) = p.eat_ident("member name")?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                MemberExpr {
                    expr: Box::new(prefix),
                    name: Identifier {
                        span: name_span,
                        name: name,
                    },
                },
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // expr "::" ident
        Namespace if precedence <= Precedence::Scope => {
            p.bump();
            let ident = parse_identifier(p, "scope name")?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                ScopeExpr(Box::new(prefix), ident),
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // expr "++"
        Operator(Op::Inc) if precedence <= Precedence::Unary => {
            p.bump();
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                UnaryExpr {
                    op: Op::Inc,
                    expr: Box::new(prefix),
                    postfix: true,
                },
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // expr "--"
        Operator(Op::Dec) if precedence <= Precedence::Unary => {
            p.bump();
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                UnaryExpr {
                    op: Op::Dec,
                    expr: Box::new(prefix),
                    postfix: true,
                },
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // expr "?" expr ":" expr
        Ternary if precedence < Precedence::Ternary => {
            p.bump();
            let true_expr = parse_expr_prec(p, Precedence::Ternary)?;
            p.require_reported(Colon)?;
            let false_expr = parse_expr_prec(p, Precedence::Ternary)?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                TernaryExpr {
                    cond: Box::new(prefix),
                    true_expr: Box::new(true_expr),
                    false_expr: Box::new(false_expr),
                },
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // expr "inside" "{" open_range_list "}"
        Keyword(Kw::Inside) if precedence <= Precedence::Relational => {
            p.bump();
            let set = flanked(p, Brace, |p| {
                comma_list_nonempty(p, CloseDelim(Brace), "range", |p| {
                    if p.peek(0).0 == OpenDelim(Brack) {
                        p.require_reported(OpenDelim(Brack))?;
                        let mut sp = p.last_span();
                        let lo = parse_expr(p)?;
                        p.require_reported(Colon)?;
                        let hi = parse_expr(p)?;
                        p.require_reported(CloseDelim(Brack))?;
                        sp.expand(p.last_span());
                        Ok(ValueRange::Range { lo, hi, span: sp })
                    } else {
                        Ok(ValueRange::Single(parse_expr(p)?))
                    }
                })
            })?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                InsideExpr(Box::new(prefix), set),
            );
            return parse_expr_suffix(p, expr, precedence);
        }

        // expr "'" "(" expr ")"
        Apostrophe if precedence <= Precedence::Postfix => {
            p.bump();
            let inner = flanked(p, Paren, |p| parse_expr(p))?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                CastSizeExpr(Box::new(prefix), Box::new(inner)),
            );
            return parse_expr_suffix(p, expr, precedence);
        }
        _ => (),
    }

    // Try assign operators.
    if let Some(op) = as_assign_operator(tkn) {
        if precedence <= Precedence::Assignment {
            p.bump();
            let rhs = parse_expr_prec(p, Precedence::Assignment)?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                AssignExpr {
                    op: op,
                    lhs: Box::new(prefix),
                    rhs: Box::new(rhs),
                },
            );
            return parse_expr_suffix(p, expr, precedence);
        }
    }

    // Try to parse binary operations.
    if let Some(op) = as_binary_operator(tkn) {
        let prec = op.get_precedence();
        if precedence < prec {
            p.bump();
            let rhs = parse_expr_prec(p, prec)?;
            let expr = Expr::new(
                Span::union(prefix.span, p.last_span()),
                BinaryExpr {
                    op: op,
                    lhs: Box::new(prefix),
                    rhs: Box::new(rhs),
                },
            );
            return parse_expr_suffix(p, expr, precedence);
        }
    }

    Ok(prefix)
}

fn parse_expr_first<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: Precedence,
) -> ReportedResult<Expr<'n>> {
    let first = p.peek(0).1;

    // Certain expressions are introduced by an operator or keyword. Handle
    // these cases first, since they are the quickest to decide.
    match p.peek(0) {
        (Operator(Op::Inc), _) if precedence <= Precedence::Unary => {
            p.bump();
            let expr = parse_expr_prec(p, Precedence::Unary)?;
            return Ok(Expr::new(
                Span::union(first, p.last_span()),
                UnaryExpr {
                    op: Op::Inc,
                    expr: Box::new(expr),
                    postfix: false,
                },
            ));
        }

        (Operator(Op::Dec), _) if precedence <= Precedence::Unary => {
            p.bump();
            let expr = parse_expr_prec(p, Precedence::Unary)?;
            return Ok(Expr::new(
                Span::union(first, p.last_span()),
                UnaryExpr {
                    op: Op::Dec,
                    expr: Box::new(expr),
                    postfix: false,
                },
            ));
        }

        (Keyword(Kw::Tagged), sp) => {
            p.add_diag(DiagBuilder2::error("Tagged union expressions not implemented").span(sp));
            return Err(());
        }

        _ => (),
    }

    // Try the unary operators next.
    if let Some(op) = as_unary_operator(p.peek(0).0) {
        p.bump();
        let expr = parse_expr_prec(p, Precedence::Unary)?;
        return Ok(Expr::new(
            Span::union(first, p.last_span()),
            UnaryExpr {
                op: op,
                expr: Box::new(expr),
                postfix: false,
            },
        ));
    }

    // Since none of the above matched, this must be a primary expression.
    parse_primary_expr(p)
}

fn parse_primary_expr<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Expr<'n>> {
    let (tkn, sp) = p.peek(0);
    match tkn {
        // Primary Literals
        Literal(lit) => {
            p.bump();
            return Ok(Expr::new(sp, LiteralExpr(lit)));
        }

        // Identifiers
        Ident(n) | EscIdent(n) => {
            p.bump();
            return Ok(Expr::new(sp, IdentExpr(Identifier { span: sp, name: n })));
        }
        SysIdent(n) => {
            p.bump();
            return Ok(Expr::new(
                sp,
                SysIdentExpr(Identifier { span: sp, name: n }),
            ));
        }

        // Concatenation and empty queue
        OpenDelim(Brace) => {
            p.bump();
            if p.try_eat(CloseDelim(Brace)) {
                return Ok(Expr::new(Span::union(sp, p.last_span()), EmptyQueueExpr));
            }
            let data = match parse_concat_expr(p) {
                Ok(x) => x,
                Err(e) => {
                    p.recover_balanced(&[CloseDelim(Brace)], true);
                    return Err(e);
                }
            };
            p.require_reported(CloseDelim(Brace))?;
            return Ok(Expr::new(Span::union(sp, p.last_span()), data));
        }

        // Parenthesis
        OpenDelim(Paren) => {
            p.bump();
            let expr = match parse_primary_parenthesis(p) {
                Ok(x) => x,
                Err(e) => {
                    p.recover_balanced(&[CloseDelim(Paren)], true);
                    return Err(e);
                }
            };
            p.require_reported(CloseDelim(Paren))?;
            return Ok(expr);
        }

        // Patterns
        Apostrophe => {
            p.bump();
            let fields = flanked(p, Brace, |p| {
                comma_list_nonempty(p, CloseDelim(Brace), "pattern field", parse_pattern_field)
            })?;
            return Ok(Expr::new(
                Span::union(sp, p.last_span()),
                PatternExpr(fields),
            ));
        }

        tkn => {
            p.add_diag(
                DiagBuilder2::error(format!("expected expression, found `{}` instead", tkn))
                    .span(sp),
            );
            return Err(());
        }
    }
}

fn parse_pattern_field<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<PatternField<'n>> {
    let mut span = p.peek(0).1;

    // Handle the trivial case of the "default" pattern.
    if p.try_eat(Keyword(Kw::Default)) {
        p.require_reported(Colon)?;
        let value = Box::new(parse_expr(p)?);
        span.expand(p.last_span());
        return Ok(PatternField {
            span: span,
            data: PatternFieldData::Default(value),
        });
    }

    // Otherwise handle the non-trivial cases.
    let mut pp = ParallelParser::new();

    // Try to parse expression patterns, which are of the form `expr ":" ...`.
    pp.add_greedy("expression pattern", |p| {
        let expr = Box::new(parse_expr(p)?);
        p.require_reported(Colon)?;
        let value = Box::new(parse_expr(p)?);
        Ok(PatternFieldData::Member(expr, value))
    });

    // Try to parse type patterns, which are of the form `type ":" ...`.
    pp.add_greedy("type pattern", |p| {
        let ty = parse_explicit_type(p)?;
        p.require_reported(Colon)?;
        let value = Box::new(parse_expr(p)?);
        Ok(PatternFieldData::Type(ty, value))
    });

    // ident ":"
    // expression ":"
    // type ":"
    // "default" ":"

    // expr
    // expr "{" expr {"," expr} "}"

    // Try to parse pattern fields that start with an expression, which may
    // either be a simple expression pattern or a repeat pattern.
    pp.add("expression or repeat pattern", |p| {
        let expr = Box::new(parse_expr(p)?);

        // If the expression is followed by an opening brace this is a repeat
        // pattern.
        let data = if let Some(inner_exprs) = try_flanked(p, Brace, |p| {
            comma_list(p, CloseDelim(Brace), "expression", parse_expr)
        })? {
            PatternFieldData::Repeat(expr, inner_exprs)
        } else {
            PatternFieldData::Expr(expr)
        };

        // Make sure this covers the whole pattern field.
        p.anticipate(&[Comma, CloseDelim(Brace)])?;
        Ok(data)
    });

    let data = pp.finish(p, "expression pattern")?;
    span.expand(p.last_span());
    Ok(PatternField {
        span: span,
        data: data,
    })
}

pub enum StreamDir {
    In,
    Out,
}

fn parse_concat_expr<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ExprData<'n>> {
    // Streaming concatenations have a "<<" or ">>" following the opening "{".
    let stream = match p.peek(0).0 {
        Operator(Op::LogicShL) => Some(StreamDir::Out),
        Operator(Op::LogicShR) => Some(StreamDir::In),
        _ => None,
    };

    if let Some(dir) = stream {
        p.bump();

        // Parse the optional slice size. This can either be an expression or a
        // type. We prefer to parse things as expressions, and only if that does
        // not succeed do we switch to a type.
        let slice_size = if p.peek(0).0 != OpenDelim(Brace) {
            let mut pp = ParallelParser::new();
            pp.add_greedy("slice size expression", |p| {
                let s = parse_expr(p).map(|e| StreamConcatSlice::Expr(Box::new(e)))?;
                p.anticipate(&[OpenDelim(Brace)])?;
                Ok(s)
            });
            pp.add_greedy("slice size type", |p| {
                let s = parse_explicit_type(p).map(|t| StreamConcatSlice::Type(t))?;
                p.anticipate(&[OpenDelim(Brace)])?;
                Ok(s)
            });
            Some(pp.finish(p, "slice size expression or type")?)
        } else {
            None
        };

        // Parse the stream expressions.
        let exprs = flanked(p, Brace, |p| {
            comma_list_nonempty(p, CloseDelim(Brace), "stream expression", |p| {
                // Consume the expression.
                let expr = Box::new(parse_expr(p)?);

                // Consume the optional range.
                let range = if p.try_eat(Keyword(Kw::With)) {
                    Some(Box::new(flanked(p, Brack, parse_range_expr)?))
                } else {
                    None
                };

                Ok(StreamExpr {
                    expr: expr,
                    range: range,
                })
            })
        })?;

        return Ok(StreamConcatExpr {
            slice: slice_size,
            exprs: exprs,
        });
    }

    // Parse the expression that follows the opening "{". Depending on whether
    // this is a regular concatenation or a multiple concatenation, the meaning
    // of the expression changes.
    let first_expr = parse_expr_prec(p, Precedence::Concatenation)?;

    // If the expression is followed by a "{", this is a multiple concatenation.
    if p.try_eat(OpenDelim(Brace)) {
        let exprs = match parse_expr_list(p) {
            Ok(x) => x,
            Err(e) => {
                p.recover_balanced(&[CloseDelim(Brace)], true);
                return Err(e);
            }
        };
        p.require_reported(CloseDelim(Brace))?;
        return Ok(ConcatExpr {
            repeat: Some(Box::new(first_expr)),
            exprs: exprs,
        });
    }

    // Otherwise this is just a regular concatenation, so the first expression
    // may be followed by "," and another expression multiple times.
    let mut exprs = Vec::new();
    exprs.push(first_expr);
    while p.try_eat(Comma) {
        if p.peek(0).0 == CloseDelim(Brace) {
            let q = p.peek(0).1;
            p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(q));
            break;
        }
        exprs.push(parse_expr_prec(p, Precedence::Min)?);
    }

    Ok(ConcatExpr {
        repeat: None,
        exprs: exprs,
    })
}

fn parse_expr_list<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Vec<Expr<'n>>> {
    let mut v = Vec::new();
    loop {
        v.push(parse_expr_prec(p, Precedence::Min)?);

        match p.peek(0) {
            (Comma, sp) => {
                p.bump();
                if p.peek(0).0 == CloseDelim(Brace) {
                    p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(sp));
                    break;
                }
            }
            (CloseDelim(Brace), _) => break,
            (_, sp) => {
                p.add_diag(DiagBuilder2::error("expected , or } after expression").span(sp));
                return Err(());
            }
        }
    }
    Ok(v)
}

/// Parse the tail of a primary expression that started with a parenthesis.
///
/// ## Syntax
/// ```text
/// "(" expression ")"
/// "(" expression ":" expression ":" expression ")"
/// ```
fn parse_primary_parenthesis<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Expr<'n>> {
    let first = parse_expr_prec(p, Precedence::Min)?;
    if p.try_eat(Colon) {
        let typ = parse_expr_prec(p, Precedence::Min)?;
        p.require_reported(Colon)?;
        let max = parse_expr_prec(p, Precedence::Min)?;
        Ok(Expr::new(
            Span::union(first.span, max.span),
            MinTypMaxExpr {
                min: Box::new(first),
                typ: Box::new(typ),
                max: Box::new(max),
            },
        ))
    } else {
        Ok(first)
    }
}

/// Parse a range expression.
///
/// ## Syntax
/// ```text
/// expression
/// expression ":" expression
/// expression "+:" expression
/// expression "-:" expression
/// ```
fn parse_range_expr<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Expr<'n>> {
    let mut span = p.peek(0).1;
    let first_expr = parse_expr(p)?;
    let mode = match p.peek(0).0 {
        Colon => RangeMode::Absolute,
        AddColon => RangeMode::RelativeUp,
        SubColon => RangeMode::RelativeDown,

        // Otherwise the index expression consists only of one expression.
        _ => return Ok(first_expr),
    };
    p.bump(); // skip the operator
    let second_expr = parse_expr(p)?;
    span.expand(p.last_span());
    Ok(Expr::new(
        span,
        RangeExpr {
            mode: mode,
            lhs: Box::new(first_expr),
            rhs: Box::new(second_expr),
        },
    ))
}

/// Convert a token to the corresponding unary operator. Return `None` if the
/// token does not map to a unary operator.
fn as_unary_operator(tkn: Token) -> Option<Op> {
    if let Operator(op) = tkn {
        match op {
            Op::Add
            | Op::Sub
            | Op::LogicNot
            | Op::BitNot
            | Op::BitAnd
            | Op::BitNand
            | Op::BitOr
            | Op::BitNor
            | Op::BitXor
            | Op::BitNxor
            | Op::BitXnor => Some(op),
            _ => None,
        }
    } else {
        None
    }
}

/// Convert a token to the corresponding binary operator. Return `None` if the
/// token does not map to a binary operator.
fn as_binary_operator(tkn: Token) -> Option<Op> {
    if let Operator(op) = tkn {
        match op {
            Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Mod
            | Op::LogicEq
            | Op::LogicNeq
            | Op::CaseEq
            | Op::CaseNeq
            | Op::WildcardEq
            | Op::WildcardNeq
            | Op::LogicAnd
            | Op::LogicOr
            | Op::Pow
            | Op::Lt
            | Op::Leq
            | Op::Gt
            | Op::Geq
            | Op::BitAnd
            | Op::BitNand
            | Op::BitOr
            | Op::BitNor
            | Op::BitXor
            | Op::BitXnor
            | Op::BitNxor
            | Op::LogicShL
            | Op::LogicShR
            | Op::ArithShL
            | Op::ArithShR
            | Op::LogicImpl
            | Op::LogicEquiv => Some(op),
            _ => None,
        }
    } else {
        None
    }
}

/// Convert a token to the corresponding AssignOp. Return `None` if the token
/// does not map to an assignment operator.
fn as_assign_operator(tkn: Token) -> Option<AssignOp> {
    match tkn {
        Operator(Op::Assign) => Some(AssignOp::Identity),
        Operator(Op::AssignAdd) => Some(AssignOp::Add),
        Operator(Op::AssignSub) => Some(AssignOp::Sub),
        Operator(Op::AssignMul) => Some(AssignOp::Mul),
        Operator(Op::AssignDiv) => Some(AssignOp::Div),
        Operator(Op::AssignMod) => Some(AssignOp::Mod),
        Operator(Op::AssignBitAnd) => Some(AssignOp::BitAnd),
        Operator(Op::AssignBitOr) => Some(AssignOp::BitOr),
        Operator(Op::AssignBitXor) => Some(AssignOp::BitXor),
        Operator(Op::AssignLogicShL) => Some(AssignOp::LogicShL),
        Operator(Op::AssignLogicShR) => Some(AssignOp::LogicShR),
        Operator(Op::AssignArithShL) => Some(AssignOp::ArithShL),
        Operator(Op::AssignArithShR) => Some(AssignOp::ArithShR),
        _ => None,
    }
}

/// Parse a comma-separated list of ports, up to a closing parenthesis. Assumes
/// that the opening parenthesis has already been consumed.
fn parse_port_list<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Vec<Port<'n>>> {
    let mut v = Vec::new();

    // In case the port list is empty.
    if p.try_eat(CloseDelim(Paren)) {
        return Ok(v);
    }

    loop {
        // Parse a port.
        match parse_port(p) {
            Ok(x) => v.push(x),
            Err(()) => p.recover_balanced(&[Comma, CloseDelim(Paren)], false),
        }

        // Depending on what follows, continue or break out of the loop.
        match p.peek(0) {
            (Comma, sp) => {
                p.bump();
                if p.peek(0).0 == CloseDelim(Paren) {
                    p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(sp));
                    break;
                }
            }
            (CloseDelim(Paren), _) => break,
            (_, sp) => {
                p.add_diag(DiagBuilder2::error("expected , or ) after port").span(sp));
                p.recover_balanced(&[CloseDelim(Paren)], false);
                break;
            }
        }
    }

    p.require_reported(CloseDelim(Paren))?;
    Ok(v)
}

/// Parse one port in a module or interface port list. The `prev` argument shall
/// be a reference to the previously parsed port, or `None` if this is the first
/// port in the list. This is required since ports inherit certain information
/// from their predecessor if omitted.
// fn parse_port(p: &mut dyn AbstractParser<'n>, prev: Option<&Port>) -> ReportedResult<Port> {
//  let mut span = p.peek(0).1;

//  // TODO: Rewrite this function to leverage the branch parser for the
//  // different kinds of port declarations.

//  // Consume the optional port direction.
//  let mut dir = as_port_direction(p.peek(0).0);
//  if dir.is_some() {
//      p.bump();
//  }

//  // Consume the optional net type or var keyword, which determines the port
//  // kind.
//  let mut kind = match p.peek(0).0 {
//      // Net Types
//      Keyword(Kw::Supply0) => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Supply1) => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Tri)     => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Triand)  => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Trior)   => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Trireg)  => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Tri0)    => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Tri1)    => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Uwire)   => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Wire)    => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Wand)    => Some(PortKind::Net(NetType::Wire)),
//      Keyword(Kw::Wor)     => Some(PortKind::Net(NetType::Wire)),

//      // Var Kind
//      Keyword(Kw::Var)     => Some(PortKind::Var),
//      _ => None
//  };
//  if kind.is_some() {
//      p.bump();
//  }

//  // Try to parse ports of the form:
//  // "." port_identifier "(" [expression] ")"
//  if p.try_eat(Period) {
//      let q = p.peek(0).1;
//      p.add_diag(DiagBuilder2::error("Ports starting with a . not yet supported").span(q));
//      return Err(())
//  }

//  // Otherwise parse the port data type, which may be a whole host of
//  // different things.
//  let mut ty = parse_data_type(p)?;

//  // Here goes the tricky part: If the data type not followed by the name (and
//  // optional dimensions) of the port, the data type actually was the port
//  // name. These are indistinguishable.
//  let (name, name_span, (dims, dims_span)) = if let Some((name, span)) = p.try_eat_ident() {
//      (name, span, parse_optional_dimensions(p)?)
//  } else {
//      if let Type { span: span, data: NamedType(ast::Identifier{name,..}), dims: dims, .. } = ty {
//          let r = (name, span, (dims, span));
//          ty = Type {
//              span: span.begin().into(),
//              data: ast::ImplicitType,
//              dims: Vec::new(),
//              sign: ast::TypeSign::None,
//          };
//          r
//      } else {
//          p.add_diag(DiagBuilder2::error("expected port type or name").span(ty.span));
//          return Err(());
//      }
//  };

//  // TODO: The following goes into the lowering to HIR phase. Just keep track
//  // of what was unspecified here.

//  // // Determine the kind of the port based on the optional kind keywords, the
//  // // direction, and the type.
//  // if dir.is_none() && kind.is_none() && ty.is_none() && prev.is_some() {
//  //  dir = Some(prev.unwrap().dir.clone());
//  //  kind = Some(prev.unwrap().kind.clone());
//  //  ty = Some(prev.unwrap().ty.clone());
//  // } else {
//  //  // The direction defaults to inout.
//  //  if dir.is_none() {
//  //      dir = Some(PortDir::Inout);
//  //  }

//  //  // The type defaults to logic.
//  //  if ty.is_none() {
//  //      ty = Some(Type {
//  //          span: INVALID_SPAN,
//  //          data: LogicType,
//  //          sign: TypeSign::None,
//  //          dims: Vec::new(),
//  //      });
//  //  }

//  //  // The kind defaults to different things based on the direction and
//  //  // type:
//  //  // - input,inout: default net
//  //  // - ref: var
//  //  // - output (implicit type): net
//  //  // - output (explicit type): var
//  //  if kind.is_none() {
//  //      kind = Some(match dir.unwrap() {
//  //          PortDir::Input | PortDir::Inout => NetPort,
//  //          PortDir::Ref => VarPort,
//  //          PortDir::Output if ty.clone().unwrap().data == ImplicitType => NetPort,
//  //          PortDir::Output => VarPort,
//  //      });
//  //  }
//  // }

//  // Parse the optional initial assignment for this port.
//  if p.try_eat(Operator(Op::Assign)) {
//      let q = p.peek(0).1;
//      p.add_diag(DiagBuilder2::error("Ports with initial assignment not yet supported").span(q));
//  }

//  // Update the port's span to cover all of the tokens consumed.
//  span.expand(p.last_span());

//  Ok(Port {
//      span: span,
//      name: name,
//      name_span: name_span,
//      kind: kind,
//      ty: ty,
//      dir: dir,
//      dims: dims,
//  })
// }

/// Parse a single port declaration. These can take a few different forms.
fn parse_port<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::Port<'n>> {
    let mut pp = ParallelParser::new();
    pp.add_greedy("interface port", parse_interface_port);
    pp.add_greedy("explicit port", parse_explicit_port);
    pp.add_greedy("named port", parse_named_port);
    pp.add_greedy("implicit port", parse_implicit_port);
    pp.finish(p, "port")
}

/// Parse a interface port declaration.
/// ```text
/// "interface" ["." ident] ident {dimension} ["=" expr]
/// ```
fn parse_interface_port<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::Port<'n>> {
    let mut span = p.peek(0).1;

    // Consume the interface keyword.
    p.require_reported(Keyword(Kw::Interface))?;

    // Consume the optional modport name.
    let modport = if p.try_eat(Period) {
        Some(parse_identifier(p, "modport name")?)
    } else {
        None
    };

    // Consume the port name.
    let name = parse_identifier(p, "port name")?;

    // Consume the optional dimensions.
    let (dims, _) = parse_optional_dimensions(p)?;

    // Consume the optional initial expression.
    let expr = if p.try_eat(Operator(Op::Assign)) {
        Some(parse_expr(p)?)
    } else {
        None
    };

    p.anticipate(&[CloseDelim(Paren), Comma])?;
    span.expand(p.last_span());
    Ok(ast::Port::Intf {
        span: span,
        modport: modport,
        name: name,
        dims: dims,
        expr: expr,
    })
}

/// Parse an explicit port declaration.
/// ```text
/// [direction] "." ident "(" [expr] ")"
/// ```
fn parse_explicit_port<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::Port<'n>> {
    let mut span = p.peek(0).1;

    // Consume the optional port direction.
    let dir = as_port_direction(p.peek(0).0);
    if dir.is_some() {
        p.bump();
    }

    // Consume the period and port name.
    p.require_reported(Period)?;
    let name = parse_identifier(p, "port name")?;

    // Consume the port expression in parenthesis.
    let expr = flanked(p, Paren, |p| {
        if p.peek(0).0 == CloseDelim(Paren) {
            Ok(None)
        } else {
            Ok(Some(parse_expr(p)?))
        }
    })?;

    p.anticipate(&[CloseDelim(Paren), Comma])?;
    span.expand(p.last_span());
    Ok(ast::Port::Explicit {
        span: span,
        dir: dir,
        name: name,
        expr: expr,
    })
}

/// Parse a named port declaration.
/// ```text
/// [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
/// ```
fn parse_named_port<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::Port<'n>> {
    let mut span = p.peek(0).1;

    // Consume the optional port direction.
    let dir = as_port_direction(p.peek(0).0);
    if dir.is_some() {
        p.bump();
    }

    // Consume the optional port kind, which is either a specific net type, a
    // "var" keyword, or nothing at all.
    let kind = {
        let tkn = p.peek(0).0;
        if let Some(net) = as_net_type(tkn) {
            p.bump();
            Some(ast::PortKind::Net(net))
        } else if tkn == Keyword(Kw::Var) {
            p.bump();
            Some(ast::PortKind::Var)
        } else {
            None
        }
    };

    // Branch to parse ports with explicit and implicit type.
    let mut pp = ParallelParser::new();
    pp.add("explicit type", |p| {
        let ty = parse_explicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    pp.add("implicit type", |p| {
        let ty = parse_implicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    let (ty, (name, dims, expr)) = pp.finish(p, "explicit or implicit type")?;

    fn tail<'n>(
        p: &mut dyn AbstractParser<'n>,
    ) -> ReportedResult<(
        ast::Identifier,
        Vec<ast::TypeDim<'n>>,
        Option<ast::Expr<'n>>,
    )> {
        // Consume the port name.
        let name = parse_identifier(p, "port name")?;

        // Consume the optional dimensions.
        let (dims, _) = parse_optional_dimensions(p)?;

        // Consume the optional initial expression.
        let expr = if p.try_eat(Operator(Op::Assign)) {
            Some(parse_expr(p)?)
        } else {
            None
        };

        p.anticipate(&[CloseDelim(Paren), Comma])?;
        Ok((name, dims, expr))
    }

    span.expand(p.last_span());
    Ok(ast::Port::Named {
        span: span,
        dir: dir,
        kind: kind,
        ty: ty,
        name: name,
        dims: dims,
        expr: expr,
    })
}

/// Parse an implicit port declaration.
/// ```text
/// expr
/// ```
fn parse_implicit_port<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::Port<'n>> {
    parse_expr(p).map(|e| ast::Port::Implicit(e))
}

fn parse_parameter_assignments<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Vec<ast::ParamAssignment<'n>>> {
    flanked(p, Paren, |p| {
        comma_list(
            p,
            CloseDelim(Paren),
            "parameter assignment",
            parse_parameter_assignment,
        )
    })
}

fn parse_parameter_assignment<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<ast::ParamAssignment<'n>> {
    let mut span = p.peek(0).1;
    let terms = [Comma, CloseDelim(Paren)];
    // If the parameter assignment starts with a ".", this is a named
    // assignment. Otherwise it's an ordered assignment.
    let (name, expr) = if p.try_eat(Period) {
        let name = parse_identifier(p, "parameter name")?;
        let expr = flanked(p, Paren, |p| parse_type_or_expr(p, &terms))?;
        (Some(name), expr)
    } else {
        (None, parse_type_or_expr(p, &terms)?)
    };
    span.expand(p.last_span());
    Ok(ast::ParamAssignment {
        span: span,
        name: name,
        expr: expr,
    })
}

fn parse_procedure<'n>(
    p: &mut dyn AbstractParser<'n>,
    kind: ProcedureKind,
) -> ReportedResult<Procedure<'n>> {
    p.bump();
    let mut span = p.last_span();
    let stmt = parse_stmt(p)?;
    span.expand(p.last_span());
    Ok(Procedure {
        span: span,
        kind: kind,
        stmt: stmt,
    })
}

fn parse_subroutine_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<SubroutineDecl<'n>> {
    let mut span = p.peek(0).1;

    // Consume the subroutine prototype, which covers everything up to the ";"
    // after the argument list.
    let prototype = parse_subroutine_prototype(p)?;

    // Consume the subroutine body, which basically is a list of statements.
    let term = match prototype.kind {
        SubroutineKind::Func => Keyword(Kw::Endfunction),
        SubroutineKind::Task => Keyword(Kw::Endtask),
    };
    let items = repeat_until(p, term, parse_subroutine_item)?;

    // Consume the "endfunction" or "endtask" keywords.
    p.require_reported(term)?;
    if p.try_eat(Colon) {
        p.eat_ident("function/task name")?;
    }
    span.expand(p.last_span());
    Ok(SubroutineDecl {
        span: span,
        prototype: prototype,
        items: items,
    })
}

fn parse_subroutine_prototype<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<SubroutinePrototype<'n>> {
    let mut span = p.peek(0).1;

    // Consume the "function" or "task" keyword, which then also decides what
    // kind of subroutine we're parsing.
    let kind = match p.peek(0).0 {
        Keyword(Kw::Function) => {
            p.bump();
            SubroutineKind::Func
        }
        Keyword(Kw::Task) => {
            p.bump();
            SubroutineKind::Task
        }
        _ => {
            p.add_diag(DiagBuilder2::error("expected function or task prototype").span(span));
            return Err(());
        }
    };

    // Parse the optional lifetime specifier.
    let lifetime = as_lifetime(p.peek(0).0);
    if lifetime.is_some() {
        p.bump();
    }

    // Parse the return type (if this is a function), the subroutine name, and
    // the optional argument list.
    let (retty, (name, args)) = if kind == SubroutineKind::Func {
        if p.peek(0).0 == Keyword(Kw::New) {
            (None, parse_subroutine_prototype_tail(p)?)
        } else {
            let mut pp = ParallelParser::new();
            pp.add("implicit function return type", |p| {
                let ty = parse_implicit_type(p)?;
                Ok((Some(ty), parse_subroutine_prototype_tail(p)?))
            });
            pp.add("explicit function return type", |p| {
                let ty = parse_explicit_type(p)?;
                Ok((Some(ty), parse_subroutine_prototype_tail(p)?))
            });
            pp.finish(p, "implicit or explicit function return type")?
        }
    } else {
        (None, parse_subroutine_prototype_tail(p)?)
    };

    span.expand(p.last_span());
    Ok(SubroutinePrototype {
        span,
        kind,
        lifetime,
        name,
        args,
        retty,
    })
}

fn parse_subroutine_prototype_tail<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<(ast::Identifier, Vec<SubroutinePort<'n>>)> {
    // Consume the subroutine name, or "new".
    // TODO: Make this accept the full `[interface_identifier "." | class_scope] tf_identifier`.
    let name = if p.try_eat(Keyword(Kw::New)) {
        ast::Identifier {
            span: p.last_span(),
            name: get_name_table().intern("new", true),
        }
    } else {
        parse_identifier(p, "function or task name")?
    };

    // Consume the port list.
    let args = try_flanked(p, Paren, |p| {
        comma_list(p, CloseDelim(Paren), "subroutine port", |p| {
            let mut span = p.peek(0).1;

            // Consume the optional port direction.
            let dir = try_subroutine_port_dir(p);

            // Consume the optional "var" keyword.
            let var = p.try_eat(Keyword(Kw::Var));

            // Branch to parse ports with explicit and implicit type.
            let mut pp = ParallelParser::new();
            pp.add("explicit type", |p| {
                let ty = parse_explicit_type(p)?;
                Ok((ty, tail(p)?))
            });
            pp.add("implicit type", |p| {
                let ty = parse_implicit_type(p)?;
                Ok((ty, tail(p)?))
            });
            let (ty, name) = pp.finish(p, "explicit or implicit type")?;

            // The `tail` function handles everything that follows the data type. To
            // ensure that the ports are parsed correctly, the function must fail if
            // the port is not immediately followed by a "," or ")". Otherwise
            // implicit and explicit types cannot be distinguished.
            fn tail<'n>(
                p: &mut dyn AbstractParser<'n>,
            ) -> ReportedResult<Option<SubroutinePortName<'n>>> {
                // Parse the optional port identifier.
                let data = if let Some(name) = try_identifier(p)? {
                    // Parse the optional dimensions.
                    let (dims, _) = parse_optional_dimensions(p)?;

                    // Parse the optional initial assignment.
                    let expr = if p.try_eat(Operator(Op::Assign)) {
                        Some(parse_expr(p)?)
                    } else {
                        None
                    };

                    Some(SubroutinePortName {
                        name: name,
                        dims: dims,
                        expr: expr,
                    })
                } else {
                    None
                };

                // Ensure that we have consumed all tokens for this port.
                match p.peek(0) {
                    (Comma, _) | (CloseDelim(Paren), _) => Ok(data),
                    (_, sp) => {
                        p.add_diag(
                            DiagBuilder2::error("expected , or ) after subroutine port").span(sp),
                        );
                        Err(())
                    }
                }
            }

            span.expand(p.last_span());
            Ok(SubroutinePort {
                span: span,
                dir: dir,
                var: var,
                ty: ty,
                name: name,
            })
        })
    })?
    .unwrap_or(Vec::new());

    // Wrap things up.
    p.require_reported(Semicolon)?;
    Ok((name, args))
}

fn try_subroutine_port_dir<'n>(p: &mut dyn AbstractParser<'n>) -> Option<SubroutinePortDir> {
    match (p.peek(0).0, p.peek(1).0) {
        (Keyword(Kw::Input), _) => {
            p.bump();
            Some(SubroutinePortDir::Input)
        }
        (Keyword(Kw::Output), _) => {
            p.bump();
            Some(SubroutinePortDir::Output)
        }
        (Keyword(Kw::Inout), _) => {
            p.bump();
            Some(SubroutinePortDir::Inout)
        }
        (Keyword(Kw::Ref), _) => {
            p.bump();
            Some(SubroutinePortDir::Ref)
        }
        (Keyword(Kw::Const), Keyword(Kw::Ref)) => {
            p.bump();
            p.bump();
            Some(SubroutinePortDir::ConstRef)
        }
        _ => None,
    }
}

fn parse_subroutine_item<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<SubroutineItem<'n>> {
    let mut span = p.peek(0).1;

    // Try to parse a port declaration of the form:
    // direction ["var"] type_or_implicit [name_assignment {"," name_assignment}]
    if let Some(dir) = try_subroutine_port_dir(p) {
        // Consume the optional "var" keyword.
        let var = p.try_eat(Keyword(Kw::Var));

        // Branch to handle the cases of implicit and explicit data type.
        let mut pp = ParallelParser::new();
        pp.add("explicit type", |p| {
            let ty = parse_explicit_type(p)?;
            let names = comma_list_nonempty(
                p,
                Semicolon,
                "port declaration",
                parse_variable_decl_assignment,
            )?;
            p.require_reported(Semicolon)?;
            Ok((ty, names))
        });
        pp.add("implicit type", |p| {
            let ty = parse_implicit_type(p)?;
            let names = comma_list_nonempty(
                p,
                Semicolon,
                "port declaration",
                parse_variable_decl_assignment,
            )?;
            p.require_reported(Semicolon)?;
            Ok((ty, names))
        });
        let (ty, names) = pp.finish(p, "explicit or implicit type")?;

        // Wrap things up.
        span.expand(p.last_span());
        return Ok(SubroutineItem::PortDecl(SubroutinePortDecl {
            span: span,
            dir: dir,
            var: var,
            ty: ty,
            names: names,
        }));
    }

    // Otherwise simply treat this as a statement.
    Ok(SubroutineItem::Stmt(parse_stmt(p)?))
}

fn parse_stmt<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Stmt<'n>> {
    let mut span = p.peek(0).1;

    // Null statements simply consist of a semicolon.
    if p.try_eat(Semicolon) {
        return Ok(Stmt::new_null(span));
    }

    // Consume the optional statement label.
    let mut label = if p.is_ident() && p.peek(1).0 == Colon {
        let (n, _) = p.eat_ident("statement label")?;
        p.bump(); // eat the colon
        Some(n)
    } else {
        None
    };

    // Parse the actual statement item.
    let data = parse_stmt_data(p, &mut label)?;
    span.expand(p.last_span());

    Ok(Stmt {
        span: span,
        label: label,
        data: data,
    })
}

fn parse_stmt_data<'n>(
    p: &mut dyn AbstractParser<'n>,
    label: &mut Option<Name>,
) -> ReportedResult<StmtData<'n>> {
    let (tkn, sp) = p.peek(0);

    // See if this is a timing-controlled statement as per IEEE 1800-2009
    // section 9.4.
    if let Some(dc) = try_delay_control(p)? {
        let stmt = Box::new(parse_stmt(p)?);
        return Ok(TimedStmt(TimingControl::Delay(dc), stmt));
    }
    if let Some(ec) = try_event_control(p)? {
        let stmt = Box::new(parse_stmt(p)?);
        return Ok(TimedStmt(TimingControl::Event(ec), stmt));
    }
    if let Some(cd) = try_cycle_delay(p)? {
        let stmt = Box::new(parse_stmt(p)?);
        return Ok(TimedStmt(TimingControl::Cycle(cd), stmt));
    }

    Ok(match tkn {
        // Sequential blocks
        OpenDelim(Bgend) => {
            p.bump();
            let (stmts, _) = parse_block(p, label, &[CloseDelim(Bgend)])?;
            SequentialBlock(stmts)
        }

        // Parallel blocks
        Keyword(Kw::Fork) => {
            p.bump();
            let (stmts, terminator) = parse_block(
                p,
                label,
                &[
                    Keyword(Kw::Join),
                    Keyword(Kw::JoinAny),
                    Keyword(Kw::JoinNone),
                ],
            )?;
            let join = match terminator {
                Keyword(Kw::Join) => JoinKind::All,
                Keyword(Kw::JoinAny) => JoinKind::Any,
                Keyword(Kw::JoinNone) => JoinKind::None,
                x => panic!("Invalid parallel block terminator {:?}", x),
            };
            ParallelBlock(stmts, join)
        }

        // If and case statements
        Keyword(Kw::Unique) => {
            p.bump();
            parse_if_or_case(p, Some(UniquePriority::Unique))?
        }
        Keyword(Kw::Unique0) => {
            p.bump();
            parse_if_or_case(p, Some(UniquePriority::Unique0))?
        }
        Keyword(Kw::Priority) => {
            p.bump();
            parse_if_or_case(p, Some(UniquePriority::Priority))?
        }
        Keyword(Kw::If) | Keyword(Kw::Case) | Keyword(Kw::Casex) | Keyword(Kw::Casez) => {
            parse_if_or_case(p, None)?
        }

        // Loops, as per IEEE 1800-2009 section 12.7.
        Keyword(Kw::Forever) => {
            p.bump();
            let stmt = Box::new(parse_stmt(p)?);
            ForeverStmt(stmt)
        }
        Keyword(Kw::Repeat) => {
            p.bump();
            let expr = flanked(p, Paren, parse_expr)?;
            let stmt = Box::new(parse_stmt(p)?);
            RepeatStmt(expr, stmt)
        }
        Keyword(Kw::While) => {
            p.bump();
            let expr = flanked(p, Paren, parse_expr)?;
            let stmt = Box::new(parse_stmt(p)?);
            WhileStmt(expr, stmt)
        }
        Keyword(Kw::Do) => {
            p.bump();
            let stmt = Box::new(parse_stmt(p)?);
            let q = p.last_span();
            if !p.try_eat(Keyword(Kw::While)) {
                p.add_diag(DiagBuilder2::error("Do loop requires a while clause").span(q));
                return Err(());
            }
            let expr = flanked(p, Paren, parse_expr)?;
            DoStmt(stmt, expr)
        }
        Keyword(Kw::For) => {
            p.bump();
            let (init, cond, step) = flanked(p, Paren, |p| {
                let init = Box::new(parse_stmt(p)?);
                let cond = parse_expr(p)?;
                p.require_reported(Semicolon)?;
                let step = parse_expr(p)?;
                Ok((init, cond, step))
            })?;
            let stmt = Box::new(parse_stmt(p)?);
            ForStmt(init, cond, step, stmt)
        }
        Keyword(Kw::Foreach) => {
            p.bump();
            let (expr, vars) = flanked(p, Paren, |p| {
                let expr = parse_expr_prec(p, Precedence::Scope)?;
                let vars = flanked(p, Brack, |p| {
                    let mut v = Vec::new();
                    while p.peek(0).0 != Eof && p.peek(0).0 != CloseDelim(Brack) {
                        if p.peek(0).0 != Comma {
                            v.push(Some(parse_identifier(p, "loop variable name")?));
                        } else {
                            v.push(None)
                        }
                        match p.peek(0) {
                            (Comma, _) => p.bump(),
                            (CloseDelim(Brack), _) => (),
                            (tkn, sp) => {
                                p.add_diag(
                                    DiagBuilder2::error(format!(
                                        "expected , or ] after loop variable; found {} instead",
                                        tkn
                                    ))
                                    .span(sp),
                                );
                                return Err(());
                            }
                        }
                    }
                    Ok(v)
                })?;
                Ok((expr, vars))
            })?;
            let stmt = Box::new(parse_stmt(p)?);
            ForeachStmt(expr, vars, stmt)
        }

        // Generate variables
        Keyword(Kw::Genvar) => {
            p.bump();
            let names = comma_list_nonempty(p, Semicolon, "genvar declaration", parse_genvar_decl)?;
            p.require_reported(Semicolon)?;
            GenvarDeclStmt(names)
        }

        // Flow control
        Keyword(Kw::Return) => {
            p.bump();
            ReturnStmt(if p.try_eat(Semicolon) {
                None
            } else {
                let expr = parse_expr(p)?;
                p.require_reported(Semicolon)?;
                Some(expr)
            })
        }
        Keyword(Kw::Break) => {
            p.bump();
            p.require_reported(Semicolon)?;
            BreakStmt
        }
        Keyword(Kw::Continue) => {
            p.bump();
            p.require_reported(Semicolon)?;
            ContinueStmt
        }

        // Import statements
        Keyword(Kw::Import) => ImportStmt(parse_import_decl(p)?),

        // Assertion statements
        Keyword(Kw::Assert)
        | Keyword(Kw::Assume)
        | Keyword(Kw::Cover)
        | Keyword(Kw::Expect)
        | Keyword(Kw::Restrict) => AssertionStmt(Box::new(parse_assertion(p)?)),

        // Wait statements
        Keyword(Kw::Wait) => {
            p.bump();
            match p.peek(0) {
                (OpenDelim(Paren), _) => {
                    let expr = flanked(p, Paren, parse_expr)?;
                    let stmt = Box::new(parse_stmt(p)?);
                    WaitExprStmt(expr, stmt)
                }
                (Keyword(Kw::Fork), _) => {
                    p.bump();
                    p.require_reported(Semicolon)?;
                    WaitForkStmt
                }
                (tkn, sp) => {
                    p.add_diag(
                        DiagBuilder2::error(format!(
                            "expected (<expr>) or fork after wait, found {} instead",
                            tkn
                        ))
                        .span(sp),
                    );
                    return Err(());
                }
            }
        }
        Keyword(Kw::WaitOrder) => {
            p.add_diag(
                DiagBuilder2::error("Don't know how to parse wait_order statements").span(sp),
            );
            return Err(());
        }

        // Disable statements
        Keyword(Kw::Disable) => {
            p.bump();
            if p.try_eat(Keyword(Kw::Fork)) {
                p.require_reported(Semicolon)?;
                DisableForkStmt
            } else {
                let (name, _) = p.eat_ident("task or block name")?;
                p.require_reported(Semicolon)?;
                DisableStmt(name)
            }
        }

        // Everything else needs special treatment as things such as variable
        // declarations look very similar to other expressions.
        _ => {
            let result = {
                let mut pp = ParallelParser::new();
                pp.add("variable declaration", |p| {
                    parse_var_decl(p).map(|d| ast::VarDeclStmt(d))
                });
                pp.add("assign statement", |p| parse_assign_stmt(p));
                pp.add("expression statement", |p| parse_expr_stmt(p));
                pp.finish(p, "statement")
            };
            match result {
                Ok(x) => x,
                Err(_) => {
                    p.recover_balanced(&[Semicolon], true);
                    return Err(());
                }
            }
        }
    })
}

fn parse_block<'n>(
    p: &mut dyn AbstractParser<'n>,
    label: &mut Option<Name>,
    terminators: &[Token],
) -> ReportedResult<(Vec<Stmt<'n>>, Token)> {
    let span = p.last_span();

    // Consume the optional block label. If the block has already been labelled
    // via a statement label, an additional block label is illegal.
    if p.try_eat(Colon) {
        let (name, name_span) = p.eat_ident("block label")?;
        if let Some(existing) = *label {
            if name == existing {
                p.add_diag(
                    DiagBuilder2::warning(format!("Block {} labelled twice", name)).span(name_span),
                );
            } else {
                p.add_diag(
                    DiagBuilder2::error(format!(
                        "Block has been given two conflicting labels, {} and {}",
                        existing, name
                    ))
                    .span(name_span),
                );
            }
        } else {
            *label = Some(name);
        }
    }

    // Parse the block statements.
    let mut v = Vec::new();
    let terminator;
    'outer: loop {
        // Check if we have reached one of the terminators.
        let tkn = p.peek(0).0;
        for term in terminators {
            if tkn == *term {
                terminator = *term;
                p.bump();
                break 'outer;
            }
        }

        // Otherwise parse the next statement.
        match parse_stmt(p) {
            Ok(x) => v.push(x),
            Err(()) => {
                p.recover_balanced(terminators, false);
                terminator = p.peek(0).0;
                p.bump();
                break;
            }
        }
    }

    // Consume the optional block label after the terminator and verify that it
    // matches the label provided at the beginning of the block.
    if p.try_eat(Colon) {
        let (name, name_span) = p.eat_ident("block label")?;
        if let Some(before) = *label {
            if before != name {
                p.add_diag(DiagBuilder2::error(format!("Block label {} at end of block does not match label {} at beginning of block", name, before)).span(name_span));
            }
        } else {
            p.add_diag(
                DiagBuilder2::error(format!(
                    "Block label {} provided at the end of the block, but not at the beginning",
                    name
                ))
                .span(name_span),
            );
        }
    }

    Ok((v, terminator))
}

/// Parse a continuous assignment.
/// ```text
/// "assign" [drive_strength] [delay3] list_of_assignments ";"
/// "assign" [delay_control] list_of_assignments ";"
/// ```
fn parse_continuous_assign<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ContAssign<'n>> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Assign))?;

    // Consume the optional drive strength.
    let strength = try_flanked(p, Paren, |p| {
        let span = p.peek(0).1;
        match try_drive_strength(p)? {
            Some(x) => Ok(x),
            None => {
                p.add_diag(DiagBuilder2::error("expected drive strength").span(span));
                Err(())
            }
        }
    })?;

    // Parse the optional delay control.
    let delay_control = try_delay_control(p)?;

    // Parse the names and assignments.
    let assignments = comma_list_nonempty(p, Semicolon, "continuous assignment", parse_assignment)?;
    p.require_reported(Semicolon)?;

    span.expand(p.last_span());
    Ok(ContAssign {
        span: span,
        strength: strength,
        delay: None,
        delay_control: delay_control,
        assignments: assignments,
    })
}

fn parse_if_or_case<'n>(
    p: &mut dyn AbstractParser<'n>,
    up: Option<UniquePriority>,
) -> ReportedResult<StmtData<'n>> {
    let (tkn, span) = p.peek(0);
    match tkn {
        // Case statements
        Keyword(Kw::Case) => {
            p.bump();
            parse_case(p, up, CaseKind::Normal)
        }
        Keyword(Kw::Casez) => {
            p.bump();
            parse_case(p, up, CaseKind::DontCareZ)
        }
        Keyword(Kw::Casex) => {
            p.bump();
            parse_case(p, up, CaseKind::DontCareXZ)
        }

        // If statement
        Keyword(Kw::If) => {
            p.bump();
            parse_if(p, up)
        }

        x => {
            p.add_diag(
                DiagBuilder2::error(format!("expected case or if statement, got {:?}", x))
                    .span(span),
            );
            Err(())
        }
    }
}

/// Parse a case statement as per IEEE 1800-2009 section 12.5.
fn parse_case<'n>(
    p: &mut dyn AbstractParser<'n>,
    up: Option<UniquePriority>,
    kind: CaseKind,
) -> ReportedResult<StmtData<'n>> {
    let q = p.last_span();

    // Parse the case expression.
    p.require_reported(OpenDelim(Paren))?;
    let expr = match parse_expr(p) {
        Ok(x) => x,
        Err(()) => {
            p.recover_balanced(&[CloseDelim(Paren)], true);
            return Err(());
        }
    };
    p.require_reported(CloseDelim(Paren))?;

    // The case expression may be followed by a "matches" or "inside" keyword
    // which changes the kind of operation the statement performs.
    let mode = match p.peek(0).0 {
        Keyword(Kw::Inside) => {
            p.bump();
            CaseMode::Inside
        }
        Keyword(Kw::Matches) => {
            p.bump();
            CaseMode::Pattern
        }
        _ => CaseMode::Normal,
    };

    // Parse the case items.
    let mut items = Vec::new();
    while p.peek(0).0 != Keyword(Kw::Endcase) && p.peek(0).0 != Eof {
        let mut span = p.peek(0).1;

        // Handle the default case items.
        if p.peek(0).0 == Keyword(Kw::Default) {
            p.bump();
            p.try_eat(Colon);
            let stmt = Box::new(parse_stmt(p)?);
            items.push(CaseItem::Default(stmt));
        }
        // Handle regular case items.
        else {
            let mut exprs = Vec::new();
            loop {
                if p.peek(0).0 == OpenDelim(Brack) {
                    // TODO(fschuiki): Keep track of results
                    // TODO(fschuiki): Error recovery
                    p.require_reported(OpenDelim(Brack))?;
                    parse_expr(p)?;
                    p.require_reported(Colon)?;
                    parse_expr(p)?;
                    p.require_reported(CloseDelim(Brack))?;
                } else {
                    match parse_expr(p) {
                        Ok(x) => exprs.push(x),
                        Err(()) => {
                            p.recover_balanced(&[Colon], false);
                            break;
                        }
                    }
                }

                match p.peek(0) {
                    (Comma, sp) => {
                        p.bump();
                        if p.try_eat(Colon) {
                            p.add_diag(
                                DiagBuilder2::warning("superfluous trailing comma").span(sp),
                            );
                            break;
                        }
                    }
                    (Colon, _) => break,
                    (_, sp) => {
                        p.add_diag(
                            DiagBuilder2::error("expected , or : after case expression").span(sp),
                        );
                        break;
                    }
                }
            }

            // Parse the statement.
            p.require_reported(Colon)?;
            let stmt = Box::new(parse_stmt(p)?);
            items.push(CaseItem::Expr(exprs, stmt));
        }
    }

    p.require_reported(Keyword(Kw::Endcase))?;

    Ok(CaseStmt {
        up: up,
        kind: kind,
        expr: expr,
        mode: mode,
        items: items,
    })
}

fn parse_if<'n>(
    p: &mut dyn AbstractParser<'n>,
    up: Option<UniquePriority>,
) -> ReportedResult<StmtData<'n>> {
    // Parse the condition expression surrounded by parenthesis.
    p.require_reported(OpenDelim(Paren))?;
    let cond = match parse_expr(p) {
        Ok(x) => x,
        Err(()) => {
            p.recover_balanced(&[CloseDelim(Paren)], true);
            return Err(());
        }
    };
    p.require_reported(CloseDelim(Paren))?;

    // Parse the main statement.
    let main_stmt = Box::new(parse_stmt(p)?);

    // Parse the optional "else" branch.
    let else_stmt = if p.peek(0).0 == Keyword(Kw::Else) {
        p.bump();
        Some(Box::new(parse_stmt(p)?))
    } else {
        None
    };

    Ok(IfStmt {
        up: up,
        cond: cond,
        main_stmt: main_stmt,
        else_stmt: else_stmt,
    })
}

fn try_delay_control<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Option<DelayControl<'n>>> {
    // Try to consume the hashtag which introduces the delay control.
    if !p.try_eat(Hashtag) {
        return Ok(None);
    }
    let mut span = p.last_span();

    // Parse the delay value. This may either be a literal delay value,
    // or a min-typ-max expression in parenthesis.
    let (tkn, sp) = p.peek(0);
    let expr = match tkn {
        // Expression
        OpenDelim(Paren) => {
            p.bump();
            let e = parse_expr_prec(p, Precedence::MinTypMax)?;
            p.require_reported(CloseDelim(Paren))?;
            e
        }

        // Literals
        Literal(Number(..)) | Literal(Time(..)) | Ident(..) => {
            parse_expr_first(p, Precedence::Max)?
        }

        // TODO: Parse "1step" keyword
        _ => {
            p.add_diag(DiagBuilder2::error("expected delay value or expression after #").span(sp));
            return Err(());
        }
    };
    span.expand(p.last_span());

    Ok(Some(DelayControl {
        span: span,
        expr: expr,
    }))
}

/// Try to parse an event control as described in IEEE 1800-2009 section 9.4.2.
fn try_event_control<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Option<EventControl<'n>>> {
    if !p.try_eat(At) {
        return Ok(None);
    }
    let mut span = p.last_span();

    // @*
    if p.peek(0).0 == Operator(Op::Mul) {
        p.bump();
        span.expand(p.last_span());
        return Ok(Some(EventControl {
            span: span,
            data: EventControlData::Implicit,
        }));
    }

    // @(*)
    if p.peek(0).0 == OpenDelim(Paren)
        && p.peek(1).0 == Operator(Op::Mul)
        && p.peek(2).0 == CloseDelim(Paren)
    {
        p.bump();
        p.bump();
        p.bump();
        span.expand(p.last_span());
        return Ok(Some(EventControl {
            span: span,
            data: EventControlData::Implicit,
        }));
    }

    let expr = parse_event_expr(p, EventPrecedence::Max)?;
    span.expand(p.last_span());

    Ok(Some(EventControl {
        span: span,
        data: EventControlData::Expr(expr),
    }))
}

fn try_cycle_delay<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Option<CycleDelay>> {
    if !p.try_eat(DoubleHashtag) {
        return Ok(None);
    }

    let q = p.last_span();
    p.add_diag(DiagBuilder2::error("Don't know how to parse cycle delay").span(q));
    Err(())
}

fn parse_assignment<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<(Expr<'n>, Expr<'n>)> {
    let lhs = parse_expr_prec(p, Precedence::Postfix)?;
    p.require_reported(Operator(Op::Assign))?;
    let rhs = parse_expr_prec(p, Precedence::Assignment)?;
    Ok((lhs, rhs))
}

fn parse_assign_stmt<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<StmtData<'n>> {
    // Parse the leading expression.
    let expr = parse_expr_prec(p, Precedence::Postfix)?;
    let (tkn, sp) = p.peek(0);

    // Handle blocking assignments (IEEE 1800-2009 section 10.4.1), where the
    // expression is followed by an assignment operator.
    if let Some(op) = as_assign_operator(tkn) {
        p.bump();
        let rhs = parse_expr(p)?;
        p.require_reported(Semicolon)?;
        return Ok(BlockingAssignStmt {
            lhs: expr,
            rhs: rhs,
            op: op,
        });
    }

    // Handle non-blocking assignments (IEEE 1800-2009 section 10.4.2).
    if tkn == Operator(Op::Leq) {
        p.bump();

        // Parse the optional delay and event control.
        let delay_control = try_delay_control(p)?;
        let event_control = /*try_event_control(p)?*/ None;

        // Parse the right-hand side of the assignment.
        let rhs = parse_expr(p)?;
        p.require_reported(Semicolon)?;

        return Ok(NonblockingAssignStmt {
            lhs: expr,
            rhs: rhs,
            delay: delay_control,
            event: event_control,
        });
    }

    p.add_diag(DiagBuilder2::error("expected blocking or non-blocking assign statement").span(sp));
    Err(())
}

fn parse_expr_stmt<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<StmtData<'n>> {
    let expr = parse_expr_prec(p, Precedence::Unary)?;
    p.require_reported(Semicolon)?;
    Ok(ExprStmt(expr))
}

fn parse_event_expr<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: EventPrecedence,
) -> ReportedResult<EventExpr<'n>> {
    let mut span = p.peek(0).1;

    // Try parsing an event expression in parentheses.
    if p.try_eat(OpenDelim(Paren)) {
        return match parse_event_expr(p, EventPrecedence::Min) {
            Ok(x) => {
                p.require_reported(CloseDelim(Paren))?;
                parse_event_expr_suffix(p, x, precedence)
            }
            Err(()) => {
                p.recover_balanced(&[CloseDelim(Paren)], true);
                Err(())
            }
        };
    }

    // Consume the optional edge identifier.
    let edge = as_edge_ident(p.peek(0).0);
    if edge != EdgeIdent::Implicit {
        p.bump();
    }

    // Parse the value.
    let value = parse_expr(p)?;
    span.expand(p.last_span());

    let expr = EventExpr::Edge {
        span: span,
        edge: edge,
        value: value,
    };
    parse_event_expr_suffix(p, expr, precedence)

    // p.add_diag(DiagBuilder2::error("expected event expression").span(span));
    // Err(())
}

fn parse_event_expr_suffix<'n>(
    p: &mut dyn AbstractParser<'n>,
    expr: EventExpr<'n>,
    precedence: EventPrecedence,
) -> ReportedResult<EventExpr<'n>> {
    match p.peek(0).0 {
        // event_expr "iff" expr
        Keyword(Kw::Iff) if precedence < EventPrecedence::Iff => {
            p.bump();
            let cond = parse_expr(p)?;
            Ok(EventExpr::Iff {
                span: Span::union(expr.span(), cond.span),
                expr: Box::new(expr),
                cond: cond,
            })
        }
        // event_expr "or" event_expr
        // event_expr "," event_expr
        Keyword(Kw::Or) | Comma if precedence <= EventPrecedence::Or => {
            p.bump();
            let rhs = parse_event_expr(p, EventPrecedence::Or)?;
            Ok(EventExpr::Or {
                span: Span::union(expr.span(), rhs.span()),
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            })
        }
        _ => Ok(expr),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EventPrecedence {
    Min,
    Or,
    Iff,
    Max,
}

fn as_edge_ident(tkn: Token) -> EdgeIdent {
    match tkn {
        Keyword(Kw::Edge) => EdgeIdent::Edge,
        Keyword(Kw::Posedge) => EdgeIdent::Posedge,
        Keyword(Kw::Negedge) => EdgeIdent::Negedge,
        _ => EdgeIdent::Implicit,
    }
}

fn parse_call_args<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Vec<CallArg<'n>>> {
    let mut v = Vec::new();
    if p.peek(0).0 == CloseDelim(Paren) {
        return Ok(v);
    }
    loop {
        match p.peek(0) {
            (Comma, sp) => v.push(CallArg {
                span: sp,
                name_span: sp,
                name: None,
                expr: None,
            }),
            (Period, mut sp) => {
                p.bump();
                let (name, mut name_sp) = p.eat_ident("argument name")?;
                name_sp.expand(sp);
                let expr = flanked(p, Paren, |p| {
                    Ok(if p.peek(0).0 == CloseDelim(Paren) {
                        None
                    } else {
                        Some(parse_expr(p)?)
                    })
                })?;
                sp.expand(p.last_span());

                v.push(CallArg {
                    span: sp,
                    name_span: name_sp,
                    name: Some(name),
                    expr: expr,
                });
            }
            (_, mut sp) => {
                let expr = parse_expr(p)?;
                sp.expand(p.last_span());
                v.push(CallArg {
                    span: sp,
                    name_span: sp,
                    name: None,
                    expr: Some(expr),
                });
            }
        }

        match p.peek(0) {
            (Comma, sp) => {
                p.bump();
                if p.try_eat(CloseDelim(Paren)) {
                    p.add_diag(DiagBuilder2::warning("superfluous trailing comma").span(sp));
                    break;
                }
            }
            (CloseDelim(Paren), _) => break,
            (_, sp) => {
                p.add_diag(DiagBuilder2::error("expected , or ) after call argument").span(sp));
                return Err(());
            }
        }
    }
    Ok(v)
}

fn parse_variable_decl_assignment<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<VarDeclName<'n>> {
    let mut span = p.peek(0).1;

    // Parse the variable name.
    let (name, name_span) = p.eat_ident("variable name")?;

    // Parse the optional dimensions.
    let (dims, _) = parse_optional_dimensions(p)?;

    // Parse the optional initial expression.
    let init = if p.try_eat(Operator(Op::Assign)) {
        Some(parse_expr(p)?)
    } else {
        None
    };
    span.expand(p.last_span());

    Ok(VarDeclName {
        span: span,
        name: name,
        name_span: name_span,
        dims: dims,
        init: init,
    })
}

fn parse_genvar_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<GenvarDecl<'n>> {
    let mut span = p.peek(0).1;

    // Parse the genvar name.
    let (name, name_span) = p.eat_ident("genvar name")?;

    // Parse the optional initial expression.
    let init = if p.try_eat(Operator(Op::Assign)) {
        Some(parse_expr(p)?)
    } else {
        None
    };
    span.expand(p.last_span());

    Ok(GenvarDecl {
        span: span,
        name: name,
        name_span: name_span,
        init: init,
    })
}

fn parse_generate_item<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Item<'n>> {
    match p.peek(0).0 {
        Keyword(Kw::For) => parse_generate_for(p).map(|x| Item::GenerateFor(x)),
        Keyword(Kw::If) => parse_generate_if(p).map(|x| Item::GenerateIf(x)),
        Keyword(Kw::Case) => parse_generate_case(p).map(|x| Item::GenerateCase(x)),
        _ => parse_hierarchy_item(p),
    }
}

/// Parse a generate-for construct.
/// ```text
/// "for" "(" stmt expr ";" expr ")" generate_block
/// ```
fn parse_generate_for<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<GenerateFor<'n>> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::For))?;
    let (init, cond, step) = flanked(p, Paren, |p| {
        let init = parse_stmt(p)?;
        let cond = parse_expr(p)?;
        p.require_reported(Semicolon)?;
        let step = parse_expr(p)?;
        Ok((init, cond, step))
    })?;
    let block = parse_generate_block(p)?;
    span.expand(p.last_span());
    Ok(GenerateFor {
        span: span,
        init: init,
        cond: cond,
        step: step,
        block: block,
    })
}

fn parse_generate_if<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<GenerateIf<'n>> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::If))?;
    let cond = flanked(p, Paren, parse_expr)?;
    let main_block = parse_generate_block(p)?;
    let else_block = if p.try_eat(Keyword(Kw::Else)) {
        Some(parse_generate_block(p)?)
    } else {
        None
    };
    span.expand(p.last_span());
    Ok(GenerateIf {
        span: span,
        cond: cond,
        main_block: main_block,
        else_block: else_block,
    })
}

fn parse_generate_case<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<GenerateCase> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Case))?;
    let q = p.last_span();
    p.add_diag(DiagBuilder2::error("Don't know how to parse case-generate statements").span(q));
    Err(())
}

fn parse_generate_block<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<GenerateBlock<'n>> {
    let mut span = p.peek(0).1;

    // Parse the optional block label.
    let mut label = if p.is_ident() && p.peek(1).0 == Colon {
        let (n, _) = p.eat_ident("generate block label")?;
        p.require_reported(Colon)?;
        Some(n)
    } else {
        None
    };

    // Consume the opening "begin" keyword if present. Otherwise simply parse
    // a single generate item.
    if !p.try_eat(OpenDelim(Bgend)) {
        if label.is_some() {
            let (t, q) = p.peek(0);
            p.add_diag(
                DiagBuilder2::error(format!(
                    "expected `begin` keyword after generate block label, found {} instead",
                    t
                ))
                .span(q),
            );
            return Err(());
        }
        let item = parse_generate_item(p)?;
        span.expand(p.last_span());
        return Ok(GenerateBlock {
            span: span,
            label: label,
            items: vec![item],
        });
    }

    // Consume the optional label after the "begin" keyword.
    if p.try_eat(Colon) {
        let (n, sp) = p.eat_ident("generate block label")?;
        if let Some(existing) = label {
            if existing == n {
                p.add_diag(
                    DiagBuilder2::warning(format!("Generate block {} labelled twice", n)).span(sp),
                );
            } else {
                p.add_diag(
                    DiagBuilder2::error(format!(
                        "Generate block given conflicting labels {} and {}",
                        existing, n
                    ))
                    .span(sp),
                );
                return Err(());
            }
        } else {
            label = Some(n);
        }
    }

    let items = repeat_until(p, CloseDelim(Bgend), parse_generate_item)?;
    p.require_reported(CloseDelim(Bgend))?;

    // Consume the optional label after the "end" keyword.
    if p.try_eat(Colon) {
        let (n, sp) = p.eat_ident("generate block label")?;
        if let Some(existing) = label {
            if existing != n {
                p.add_diag(DiagBuilder2::error(format!("Label {} given after generate block does not match label {} given before the block", n, existing)).span(sp));
                return Err(());
            }
        } else {
            p.add_diag(
                DiagBuilder2::warning(format!(
                    "Generate block has trailing label {}, but is missing leading label",
                    n
                ))
                .span(sp),
            );
        }
    }

    span.expand(p.last_span());
    Ok(GenerateBlock {
        span: span,
        label: label,
        items: items,
    })
}

fn parse_class_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ClassDecl<'n>> {
    let mut span = p.peek(0).1;
    let result = recovered(p, Keyword(Kw::Endclass), |p| {
        // Eat the optional "virtual" or "interface" keyword.
        let virt = p.try_eat(Keyword(Kw::Virtual));
        let intf = p.try_eat(Keyword(Kw::Interface));

        // Eat the "class" keyword.
        p.require_reported(Keyword(Kw::Class))?;

        // Eat the optional lifetime.
        let lifetime = match as_lifetime(p.peek(0).0) {
            Some(l) => {
                p.bump();
                l
            }
            None => Lifetime::Static,
        };

        // Parse the class name.
        let name = parse_identifier(p, "class name")?;

        // Parse the optional parameter port list.
        let params = if p.try_eat(Hashtag) {
            parse_parameter_port_list(p)?
        } else {
            Vec::new()
        };

        // Parse the optional inheritance clause.
        let extends = if p.try_eat(Keyword(Kw::Extends)) {
            let superclass = parse_data_type(p)?;
            let args = try_flanked(p, Paren, parse_call_args)?.unwrap_or(Vec::new());
            Some((superclass, args))
        } else {
            None
        };

        // Parse the optional implementation clause.
        let impls = if p.try_eat(Keyword(Kw::Implements)) {
            comma_list_nonempty(p, Semicolon, "interface class", |p| {
                parse_identifier(p, "class name")
            })?
        } else {
            vec![]
        };

        p.require_reported(Semicolon)?;

        // Parse the class items.
        let items = repeat_until(p, Keyword(Kw::Endclass), |p| parse_class_item(p, intf))?;
        Ok((virt, lifetime, name, params, extends, impls, items))
    });
    p.require_reported(Keyword(Kw::Endclass))?;

    let (virt, lifetime, name, params, extends, impls, items) = result?;

    // Parse the optional class name after "endclass".
    if p.try_eat(Colon) {
        let (n, sp) = p.eat_ident("class name")?;
        if n != name.name {
            p.add_diag(
                DiagBuilder2::error(format!(
                    "Class name {} disagrees with name {} given before",
                    n, name.name
                ))
                .span(sp),
            );
            return Err(());
        }
    }

    span.expand(p.last_span());
    Ok(ClassDecl {
        span,
        virt,
        lifetime,
        name,
        params,
        extends,
        impls,
        items,
    })
}

fn parse_class_item<'n>(
    p: &mut dyn AbstractParser<'n>,
    intf: bool,
) -> ReportedResult<ClassItem<'n>> {
    let mut span = p.peek(0).1;

    // Easy path for null class items.
    if p.try_eat(Semicolon) {
        return Ok(ClassItem {
            span,
            qualifiers: vec![],
            data: ClassItemData::Null,
        });
    }

    // Parse localparam and parameter declarations.
    // TODO: Replace these by calls to parse_param_decl.
    match p.peek(0).0 {
        Keyword(Kw::Localparam) | Keyword(Kw::Parameter) => {
            let decl = parse_param_decl(p, false)?;
            span.expand(p.last_span());
            p.require_reported(Semicolon)?;
            return Ok(ClassItem {
                span,
                qualifiers: vec![],
                data: ClassItemData::ParamDecl(decl),
            });
        }
        // Parse "extern" task and function prototypes.
        Keyword(Kw::Extern) => {
            p.bump();
            let proto = parse_subroutine_prototype(p)?;
            span.expand(p.last_span());
            return Ok(ClassItem {
                span,
                qualifiers: vec![],
                data: ClassItemData::ExternSubroutine(proto),
            });
        }
        // Parse type defs.
        Keyword(Kw::Typedef) => {
            let def = parse_typedef(p)?;
            span.expand(p.last_span());
            return Ok(ClassItem {
                span,
                qualifiers: vec![],
                data: ClassItemData::Typedef(def),
            });
        }
        _ => (),
    }

    // Parse the optional class item qualifiers.
    let qualifiers = parse_class_item_qualifiers(p)?;

    let data = {
        let mut pp = ParallelParser::new();
        pp.add("class property", |p| {
            let ty = parse_data_type(p)?;
            let names = comma_list_nonempty(
                p,
                Semicolon,
                "data declaration",
                parse_variable_decl_assignment,
            )?;
            p.require_reported(Semicolon)?;
            Ok(ClassItemData::Property)
        });
        if intf {
            pp.add("class function or task prototype", |p| {
                parse_subroutine_prototype(p).map(ClassItemData::ExternSubroutine)
            });
        } else {
            pp.add("class function or task", |p| {
                parse_subroutine_decl(p).map(ClassItemData::SubroutineDecl)
            });
        }
        pp.add("class constraint", |p| {
            parse_constraint(p).map(ClassItemData::Constraint)
        });
        pp.finish(p, "class item")?
    };
    span.expand(p.last_span());

    Ok(ClassItem {
        span: span,
        qualifiers: qualifiers,
        data: data,
    })
}

fn parse_class_item_qualifiers<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Vec<(ClassItemQualifier, Span)>> {
    let mut v = Vec::new();
    loop {
        let (tkn, sp) = p.peek(0);
        match tkn {
            Keyword(Kw::Static) => v.push((ClassItemQualifier::Static, sp)),
            Keyword(Kw::Protected) => v.push((ClassItemQualifier::Protected, sp)),
            Keyword(Kw::Local) => v.push((ClassItemQualifier::Local, sp)),
            Keyword(Kw::Rand) => v.push((ClassItemQualifier::Rand, sp)),
            Keyword(Kw::Randc) => v.push((ClassItemQualifier::Randc, sp)),
            Keyword(Kw::Pure) => v.push((ClassItemQualifier::Pure, sp)),
            Keyword(Kw::Virtual) => v.push((ClassItemQualifier::Virtual, sp)),
            Keyword(Kw::Const) => v.push((ClassItemQualifier::Const, sp)),
            _ => break,
        }
        p.bump();
    }
    Ok(v)
}

fn parse_class_method<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ClassItem<'n>> {
    println!("Parsing class method");
    Err(())
}

fn parse_class_property<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ClassItem<'n>> {
    println!("Parsing class property");
    p.try_eat(Keyword(Kw::Rand));
    Err(())
}

fn parse_constraint<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Constraint<'n>> {
    let mut span = p.peek(0).1;

    // Parse the prototype qualifier.
    let kind = match p.peek(0).0 {
        Keyword(Kw::Extern) => {
            p.bump();
            ConstraintKind::ExternProto
        }
        Keyword(Kw::Pure) => {
            p.bump();
            ConstraintKind::PureProto
        }
        _ => ConstraintKind::Decl,
    };
    let kind_span = span;

    // Parse the optional "static" keyword.
    let statik = p.try_eat(Keyword(Kw::Static));

    // Parse the "constraint" keyword.
    p.require_reported(Keyword(Kw::Constraint))?;

    // Parse the constraint name.
    let (name, name_span) = p.eat_ident("constraint name")?;

    let items = if p.try_eat(Semicolon) {
        let kind = match kind {
            ConstraintKind::Decl => ConstraintKind::Proto,
            x => x,
        };
        Vec::new()
    } else {
        // Make sure that no "extern" or "pure" keyword was used, as these are
        // only valid for prototypes.
        if kind == ConstraintKind::ExternProto || kind == ConstraintKind::PureProto {
            p.add_diag(
                DiagBuilder2::error("Only constraint prototypes can be extern or pure")
                    .span(kind_span),
            );
            return Err(());
        }
        flanked(p, Brace, |p| {
            repeat_until(p, CloseDelim(Brace), parse_constraint_item)
        })?
    };
    span.expand(p.last_span());

    Ok(Constraint {
        span: span,
        kind: kind,
        statik: statik,
        name: name,
        name_span: name_span,
        items: items,
    })
}

fn parse_constraint_item<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ConstraintItem<'n>> {
    let mut span = p.peek(0).1;
    let data = parse_constraint_item_data(p)?;
    span.expand(p.last_span());
    Ok(ConstraintItem {
        span: span,
        data: data,
    })
}

fn parse_constraint_item_data<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<ConstraintItemData<'n>> {
    // Handle the trivial cases that start with a keyword first.
    if p.try_eat(Keyword(Kw::If)) {
        let q = p.last_span();
        p.add_diag(DiagBuilder2::error("Don't know how to parse `if` constraint items").span(q));
        return Err(());
    }

    if p.try_eat(Keyword(Kw::Foreach)) {
        let q = p.last_span();
        p.add_diag(
            DiagBuilder2::error("Don't know how to parse `foreach` constraint items").span(q),
        );
        return Err(());
    }

    // If we arrive here, the item starts with an expression.
    let expr = parse_expr(p)?;
    p.require_reported(Semicolon)?;
    Ok(ConstraintItemData::Expr(expr))
}

struct ParallelParser<'a, 'n, R: Clone> {
    branches: Vec<(
        String,
        Box<dyn FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R> + 'a>,
        bool,
    )>,
}

impl<'a, 'n, R: Clone> ParallelParser<'a, 'n, R> {
    pub fn new() -> Self {
        ParallelParser {
            branches: Vec::new(),
        }
    }

    pub fn add<F>(&mut self, name: &str, func: F)
    where
        F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R> + 'a,
    {
        self.branches.push((name.to_owned(), Box::new(func), false));
    }

    pub fn add_greedy<F>(&mut self, name: &str, func: F)
    where
        F: FnMut(&mut dyn AbstractParser<'n>) -> ReportedResult<R> + 'a,
    {
        self.branches.push((name.to_owned(), Box::new(func), true));
    }

    pub fn finish(self, p: &mut dyn AbstractParser<'n>, msg: &str) -> ReportedResult<R> {
        let (tkn, q) = p.peek(0);
        // p.add_diag(DiagBuilder2::note(format!("Trying as {:?}", self.branches.iter().map(|&(ref x,_)| x).collect::<Vec<_>>())).span(q));

        // Create a separate speculative parser for each branch.
        let mut results = Vec::new();
        let mut matched = Vec::new();
        for (name, mut func, greedy) in self.branches {
            // p.add_diag(DiagBuilder2::note(format!("Trying as {}", name)).span(q));
            let mut bp = BranchParser::new(p);
            match func(&mut bp) {
                Ok(x) => {
                    if greedy {
                        bp.commit();
                        return Ok(x);
                    } else {
                        let sp = bp.last_span();
                        results.push((name, bp.consumed, bp.diagnostics, x, Span::union(q, sp)));
                    }
                }
                Err(_) => matched.push((
                    name,
                    bp.consumed() - bp.skipped(),
                    bp.consumed(),
                    bp.diagnostics,
                )),
            }
        }

        if results.len() > 1 {
            let mut names = String::new();
            names.push_str(&results[0].0);
            if results.len() == 2 {
                names.push_str(" or ");
                names.push_str(&results[1].0);
            } else {
                for &(ref name, _, _, _, _) in &results[..results.len() - 1] {
                    names.push_str(", ");
                    names.push_str(&name);
                }
                names.push_str(", or ");
                names.push_str(&results[results.len() - 1].0);
            }
            p.add_diag(DiagBuilder2::fatal(format!("ambiguous code, could be {}", names)).span(q));
            for &(ref name, _, _, _, span) in &results {
                p.add_diag(DiagBuilder2::note(format!("{} would be this part", name)).span(span));
            }
            Err(())
        } else if let Some(&(_, consumed, ref diagnostics, ref res, _)) = results.last() {
            for d in diagnostics {
                p.add_diag(d.clone());
            }
            for _ in 0..consumed {
                p.bump();
            }
            Ok((*res).clone())
        } else {
            // Sort the errors by score and remove all but the highest scoring
            // ones.
            matched.sort_by(|a, b| (b.1).cmp(&a.1));
            let highest_score = matched[0].1;
            let highest_consumed = matched[0].2;
            let errors = matched
                .into_iter()
                .take_while(|e| e.1 == highest_score)
                .collect::<Vec<_>>();
            let num_errors = errors.len();

            // Print the errors.
            if num_errors != 1 {
                p.add_diag(
                    DiagBuilder2::error(format!("expected {}, found `{}` instead", msg, tkn))
                        .span(q),
                );
                for (name, _, _, ds) in errors {
                    p.add_diag(DiagBuilder2::note(format!("parsing as {}:", name)));
                    for d in ds {
                        p.add_diag(d);
                    }
                }
            } else {
                for d in errors.into_iter().next().unwrap().3 {
                    p.add_diag(d);
                }
            }
            for _ in 0..highest_consumed {
                p.bump();
            }
            Err(())

            // if errors.is_empty() {
            //  Err(())
            // } else {
            //  for (n, _, m) in errors {
            //      if num_errors > 1 {
            //          p.add_diag(DiagBuilder2::note(format!("Assuming this is a {}", n)).span(q));
            //      }
            //      for d in m {
            //          p.add_diag(d);
            //      }
            //  }
            //  Err(())
            // }
        }
    }
}

struct BranchParser<'tp, 'n> {
    parser: &'tp mut dyn AbstractParser<'n>,
    consumed: usize,
    skipped: usize,
    diagnostics: Vec<DiagBuilder2>,
    last_span: Span,
    severity: Severity,
}

impl<'tp, 'n> BranchParser<'tp, 'n> {
    pub fn new(parser: &'tp mut dyn AbstractParser<'n>) -> Self {
        let last = parser.last_span();
        BranchParser {
            parser: parser,
            consumed: 0,
            skipped: 0,
            diagnostics: Vec::new(),
            last_span: last,
            severity: Severity::Note,
        }
    }

    pub fn skipped(&self) -> usize {
        self.skipped
    }

    pub fn commit(self) {
        for _ in 0..self.consumed {
            self.parser.bump();
        }
        for d in self.diagnostics {
            self.parser.add_diag(d);
        }
    }
}

impl<'tp, 'n> AbstractParser<'n> for BranchParser<'tp, 'n> {
    fn peek(&mut self, offset: usize) -> TokenAndSpan {
        self.parser.peek(self.consumed + offset)
    }

    fn bump(&mut self) {
        self.last_span = self.parser.peek(self.consumed).1;
        self.consumed += 1;
    }

    fn skip(&mut self) {
        self.bump();
        self.skipped += 1;
    }

    fn consumed(&self) -> usize {
        self.consumed
    }

    fn last_span(&self) -> Span {
        self.last_span
    }

    fn add_diag(&mut self, diag: DiagBuilder2) {
        if diag.severity > self.severity {
            self.severity = diag.severity;
        }
        self.diagnostics.push(diag);
    }

    fn severity(&self) -> Severity {
        self.severity
    }
}

fn parse_typedef<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Typedef<'n>> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Typedef))?;
    let ty = parse_explicit_type(p)?;
    let name = parse_identifier(p, "type name")?;
    let (dims, _) = parse_optional_dimensions(p)?;
    p.require_reported(Semicolon)?;
    span.expand(p.last_span());
    Ok(Typedef {
        span: span,
        name: name,
        ty: ty,
        dims: dims,
    })
}

fn parse_port_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<PortDecl<'n>> {
    let mut span = p.peek(0).1;

    // Consume the port direction.
    let dir = match as_port_direction(p.peek(0).0) {
        Some(x) => {
            p.bump();
            x
        }
        None => {
            p.add_diag(
                DiagBuilder2::error("expected port direction (inout, input, output, or ref)")
                    .span(span),
            );
            return Err(());
        }
    };

    // Consume the optional net type or "var" keyword.
    let kind = if let Some(nt) = as_net_type(p.peek(0).0) {
        p.bump();
        Some(PortKind::Net(nt))
    } else if p.try_eat(Keyword(Kw::Var)) {
        Some(PortKind::Var)
    } else {
        None
    };

    // Branch to handle explicit and implicit types.
    let mut pp = ParallelParser::new();
    pp.add("explicit type", |p| {
        let ty = parse_explicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    pp.add("implicit type", |p| {
        let ty = parse_implicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    let (ty, names) = pp.finish(p, "explicit or implicit type")?;

    fn tail<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Vec<VarDeclName<'n>>> {
        let names = comma_list_nonempty(
            p,
            Semicolon,
            "port declaration",
            parse_variable_decl_assignment,
        )?;
        p.require_reported(Semicolon)?;
        Ok(names)
    }

    // Wrap things up.
    span.expand(p.last_span());
    Ok(PortDecl {
        span,
        dir,
        kind,
        ty,
        names,
    })
}

fn as_net_type(tkn: Token) -> Option<NetType> {
    match tkn {
        Keyword(Kw::Supply0) => Some(NetType::Supply0),
        Keyword(Kw::Supply1) => Some(NetType::Supply1),
        Keyword(Kw::Tri) => Some(NetType::Tri),
        Keyword(Kw::Triand) => Some(NetType::TriAnd),
        Keyword(Kw::Trior) => Some(NetType::TriOr),
        Keyword(Kw::Trireg) => Some(NetType::TriReg),
        Keyword(Kw::Tri0) => Some(NetType::Tri0),
        Keyword(Kw::Tri1) => Some(NetType::Tri1),
        Keyword(Kw::Uwire) => Some(NetType::Uwire),
        Keyword(Kw::Wire) => Some(NetType::Wire),
        Keyword(Kw::Wand) => Some(NetType::WireAnd),
        Keyword(Kw::Wor) => Some(NetType::WireOr),
        _ => None,
    }
}

fn parse_net_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<NetDecl<'n>> {
    let mut span = p.peek(0).1;

    // Consume the net type.
    let net_type = match as_net_type(p.peek(0).0) {
        Some(x) => {
            p.bump();
            x
        }
        None => {
            let q = p.peek(0).1;
            p.add_diag(DiagBuilder2::error("expected net type").span(q));
            return Err(());
        }
    };

    // Consume the optional drive strength or charge strength.
    let strength = try_flanked(p, Paren, parse_net_strength)?;

    // Consume the optional "vectored" or "scalared" keywords.
    let kind = match p.peek(0).0 {
        Keyword(Kw::Vectored) => {
            p.bump();
            NetKind::Vectored
        }
        Keyword(Kw::Scalared) => {
            p.bump();
            NetKind::Scalared
        }
        _ => NetKind::None,
    };

    // Branch to handle explicit and implicit types separately.
    let mut pp = ParallelParser::new();
    pp.add("explicit type", |p| {
        let ty = parse_explicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    pp.add("implicit type", |p| {
        let ty = parse_implicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    let (ty, (delay, names)) = pp.finish(p, "explicit or implicit type")?;

    // This function handles parsing of everything after the type.
    fn tail<'n>(
        p: &mut dyn AbstractParser<'n>,
    ) -> ReportedResult<(Option<DelayControl<'n>>, Vec<VarDeclName<'n>>)> {
        // Parse the optional delay.
        let delay = try_delay_control(p)?;

        // Parse the names and assignments.
        let names = comma_list_nonempty(
            p,
            Semicolon,
            "net declaration",
            parse_variable_decl_assignment,
        )?;
        p.require_reported(Semicolon)?;
        Ok((delay, names))
    }

    span.expand(p.last_span());
    Ok(NetDecl {
        span: span,
        net_type: net_type,
        strength: strength,
        kind: kind,
        ty: ty,
        delay: delay,
        names: names,
    })
}

fn try_drive_strength<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<Option<(DriveStrength, DriveStrength)>> {
    if let Some(a) = as_drive_strength(p.peek(0).0) {
        p.bump();
        p.require_reported(Comma)?;
        if let Some(b) = as_drive_strength(p.peek(0).0) {
            Ok(Some((a, b)))
        } else {
            let q = p.peek(0).1;
            p.add_diag(DiagBuilder2::error("expected second drive strength").span(q));
            Err(())
        }
    } else {
        Ok(None)
    }
}

fn parse_net_strength<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<NetStrength> {
    if let Some((a, b)) = try_drive_strength(p)? {
        Ok(NetStrength::Drive(a, b))
    } else if let Some(s) = as_charge_strength(p.peek(0).0) {
        p.bump();
        Ok(NetStrength::Charge(s))
    } else {
        let q = p.peek(0).1;
        p.add_diag(DiagBuilder2::error("expected drive or charge strength").span(q));
        Err(())
    }
}

fn as_drive_strength(tkn: Token) -> Option<DriveStrength> {
    match tkn {
        Keyword(Kw::Supply0) => Some(DriveStrength::Supply0),
        Keyword(Kw::Strong0) => Some(DriveStrength::Strong0),
        Keyword(Kw::Pull0) => Some(DriveStrength::Pull0),
        Keyword(Kw::Weak0) => Some(DriveStrength::Weak0),
        Keyword(Kw::Highz0) => Some(DriveStrength::HighZ0),
        Keyword(Kw::Supply1) => Some(DriveStrength::Supply1),
        Keyword(Kw::Strong1) => Some(DriveStrength::Strong1),
        Keyword(Kw::Pull1) => Some(DriveStrength::Pull1),
        Keyword(Kw::Weak1) => Some(DriveStrength::Weak1),
        Keyword(Kw::Highz1) => Some(DriveStrength::HighZ1),
        _ => None,
    }
}

fn as_charge_strength(tkn: Token) -> Option<ChargeStrength> {
    match tkn {
        Keyword(Kw::Small) => Some(ChargeStrength::Small),
        Keyword(Kw::Medium) => Some(ChargeStrength::Medium),
        Keyword(Kw::Large) => Some(ChargeStrength::Large),
        _ => None,
    }
}

/// Parse a import declaration.
/// ```text
/// "import" package_ident "::" "*" ";"
/// "import" package_ident "::" ident ";"
/// "import" string ["context"|"pure"] [ident "="] subroutine_prototype ";"
/// ```
fn parse_import_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ImportDecl> {
    let mut span = p.peek(0).1;
    p.require_reported(Keyword(Kw::Import))?;

    // Handle the DPI import case.
    if let Literal(Lit::Str(spec)) = p.peek(0).0 {
        let spec = Spanned::new(spec, p.peek(0).1);
        p.bump();
        let property = if p.try_eat(Keyword(Kw::Context)) {
            ()
        } else if p.try_eat(Keyword(Kw::Pure)) {
            ()
        } else {
            ()
        };
        let cident = if p.peek(1).0 == Operator(Op::Assign) {
            let (n, sp) = p.eat_ident("C identifier")?;
            p.require_reported(Operator(Op::Assign))?;
            Some(Spanned::new(n, sp))
        } else {
            None
        };
        let proto = parse_subroutine_prototype(p)?;
        // TODO: Don't just discard the imported DPI magic!
        span.expand(p.last_span());
        p.add_diag(DiagBuilder2::warning("unsupported DPI import").span(span));
        return Ok(ImportDecl {
            span: span,
            items: vec![],
        });
    }

    let items = comma_list_nonempty(p, Semicolon, "import item", |p| {
        // package_ident "::" ident
        // package_ident "::" "*"
        let mut span = p.peek(0).1;
        let pkg = parse_identifier_name(p, "package name")?;
        p.require_reported(Namespace)?;
        let (tkn, sp) = p.peek(0);
        match tkn {
            // package_ident "::" "*"
            Operator(Op::Mul) => {
                p.bump();
                span.expand(p.last_span());
                Ok(ImportItem {
                    span,
                    pkg,
                    name: None,
                })
            }

            // package_ident "::" ident
            Ident(n) | EscIdent(n) => {
                p.bump();
                span.expand(p.last_span());
                Ok(ImportItem {
                    span,
                    pkg,
                    name: Some(Spanned::new(n, sp)),
                })
            }

            _ => {
                p.add_diag(
                    DiagBuilder2::error(
                        "expected identifier or `*` after `::` in import declaration",
                    )
                    .span(sp),
                );
                Err(())
            }
        }
    })?;
    p.require_reported(Semicolon)?;
    span.expand(p.last_span());
    Ok(ImportDecl {
        span: span,
        items: items,
    })
}

fn parse_assertion<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Assertion<'n>> {
    let mut span = p.peek(0).1;

    // Peek ahead after the current token to see if a "property", "sequence",
    // "#0", or "final" follows. This decides what kind of assertion we're
    // parsing.
    let null = get_name_table().intern("0", false);
    let is_property = p.peek(1).0 == Keyword(Kw::Property);
    let is_sequence = p.peek(1).0 == Keyword(Kw::Sequence);
    let is_deferred_observed = p.peek(1).0 == Hashtag && p.peek(2).0 == Literal(Number(null, None));
    let is_deferred_final = p.peek(1).0 == Keyword(Kw::Final);
    let is_deferred = is_deferred_observed || is_deferred_final;
    let deferred_mode = match is_deferred_final {
        true => AssertionDeferred::Final,
        false => AssertionDeferred::Observed,
    };

    // Handle the different combinations of keywords and lookaheads from above.

    let data = match p.peek(0).0 {
        // Concurrent Assertions
        // ---------------------

        // `assert property`
        Keyword(Kw::Assert) if is_property => {
            p.bump();
            p.bump();
            let prop = flanked(p, Paren, parse_property_spec)?;
            let action = parse_assertion_action_block(p)?;
            AssertionData::Concurrent(ConcurrentAssertion::AssertProperty(prop, action))
        }

        // `assume property`
        Keyword(Kw::Assume) if is_property => {
            p.bump();
            p.bump();
            let prop = flanked(p, Paren, parse_property_spec)?;
            let action = parse_assertion_action_block(p)?;
            AssertionData::Concurrent(ConcurrentAssertion::AssumeProperty(prop, action))
        }

        // `cover property`
        Keyword(Kw::Cover) if is_property => {
            p.bump();
            p.bump();
            let prop = flanked(p, Paren, parse_property_spec)?;
            let stmt = parse_stmt(p)?;
            AssertionData::Concurrent(ConcurrentAssertion::CoverProperty(prop, stmt))
        }

        // `cover sequence`
        Keyword(Kw::Cover) if is_sequence => {
            p.bump();
            p.bump();
            p.add_diag(DiagBuilder2::error("Don't know how to parse cover sequences").span(span));
            return Err(());
            // AssertionData::Concurrent(ConcurrentAssertion::CoverSequence)
        }

        // `expect`
        Keyword(Kw::Expect) => {
            p.bump();
            let prop = flanked(p, Paren, parse_property_spec)?;
            let action = parse_assertion_action_block(p)?;
            AssertionData::Concurrent(ConcurrentAssertion::ExpectProperty(prop, action))
        }

        // `restrict property`
        Keyword(Kw::Restrict) if is_property => {
            p.bump();
            p.bump();
            let prop = flanked(p, Paren, parse_property_spec)?;
            AssertionData::Concurrent(ConcurrentAssertion::RestrictProperty(prop))
        }

        // Immediate and Deferred Assertions
        // ---------------------------------

        // `assert`, `assert #0`, and `assert final`
        Keyword(Kw::Assert) => {
            p.bump();
            if is_deferred {
                p.bump();
                if is_deferred_observed {
                    p.bump();
                }
            }
            let expr = flanked(p, Paren, parse_expr)?;
            let action = parse_assertion_action_block(p)?;
            let a = BlockingAssertion::Assert(expr, action);
            if is_deferred {
                AssertionData::Deferred(deferred_mode, a)
            } else {
                AssertionData::Immediate(a)
            }
        }

        // `assume`, `assume #0`, and `assume final`
        Keyword(Kw::Assume) => {
            p.bump();
            if is_deferred {
                p.bump();
                if is_deferred_observed {
                    p.bump();
                }
            }
            let expr = flanked(p, Paren, parse_expr)?;
            let action = parse_assertion_action_block(p)?;
            let a = BlockingAssertion::Assume(expr, action);
            if is_deferred {
                AssertionData::Deferred(deferred_mode, a)
            } else {
                AssertionData::Immediate(a)
            }
        }

        // `cover`, `cover #0`, and `cover final`
        Keyword(Kw::Cover) => {
            p.bump();
            if is_deferred {
                p.bump();
                if is_deferred_observed {
                    p.bump();
                }
            }
            let expr = flanked(p, Paren, parse_expr)?;
            let stmt = parse_stmt(p)?;
            let a = BlockingAssertion::Cover(expr, stmt);
            if is_deferred {
                AssertionData::Deferred(deferred_mode, a)
            } else {
                AssertionData::Immediate(a)
            }
        }

        _ => {
            p.add_diag(
                DiagBuilder2::error("expected assert, assume, cover, expect, or restrict")
                    .span(span),
            );
            return Err(());
        }
    };

    span.expand(p.last_span());
    Ok(Assertion {
        span: span,
        label: None,
        data: data,
    })
}

fn parse_assertion_action_block<'n>(
    p: &mut dyn AbstractParser<'n>,
) -> ReportedResult<AssertionActionBlock<'n>> {
    if p.try_eat(Keyword(Kw::Else)) {
        Ok(AssertionActionBlock::Negative(parse_stmt(p)?))
    } else {
        let stmt = parse_stmt(p)?;
        if p.try_eat(Keyword(Kw::Else)) {
            // TODO: Ensure that `stmt` is not a NullStmt.
            Ok(AssertionActionBlock::Both(stmt, parse_stmt(p)?))
        } else {
            Ok(AssertionActionBlock::Positive(stmt))
        }
    }
}

fn parse_property_spec<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<PropSpec> {
    let mut span = p.peek(0).1;

    // TODO: Actually parse this stuff, rather than just chicken out.
    p.recover_balanced(&[CloseDelim(Paren)], false);
    return Ok(PropSpec);

    // // Parse the optional event expression.
    // let event = if p.try_eat(At) {
    //     Some(parse_event_expr(p, EventPrecedence::Min)?)
    // } else {
    //     None
    // };

    // // Parse the optional "disable iff" clause.
    // let disable = if p.try_eat(Keyword(Kw::Disable)) {
    //     p.require_reported(Keyword(Kw::Iff))?;
    //     Some(flanked(p, Paren, parse_expr)?)
    // } else {
    //     None
    // };

    // // Parse the property expression.
    // let prop = parse_propexpr(p)?;
    // Ok(PropSpec)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[allow(dead_code)]
enum PropSeqPrecedence {
    Min,
    AlEvIfAccRejSyn,
    ImplFollow, // right-associative
    Until,      // right-associative
    Iff,        // right-associative
    Or,         // left-associative
    And,        // left-associative
    NotNexttime,
    Intersect,  // left-associative
    Within,     // left-associative
    Throughout, // right-associative
    CycleDelay, // left-associative
    Brack,
    Max,
}

fn parse_propexpr<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<PropExpr<'n>> {
    parse_propexpr_prec(p, PropSeqPrecedence::Min)
}

fn parse_propexpr_prec<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<PropExpr<'n>> {
    let mut span = p.peek(0).1;

    // To parse property expressions we need a parallel parser. For certain
    // cases it is unclear if a parenthesized expression is a sequence or a
    // property expression, e.g.:
    //
    // (foo) |=> bar
    // ^^^^^ sequence or property?
    //
    // Both sequences and property expressions support parenthesis. However the
    // |=> operator is only defined for sequences on the left hand side. If the
    // parenthesis are parsed as a property and foo as a sequence, the above
    // code fails to parse since the sequence on the left has effectively become
    // a property. If the parenthesis are parsed as a sequence, all is well. To
    // resolve these kinds of issues, we need a parallel parser.
    let mut pp = ParallelParser::new();
    pp.add_greedy("sequence expression", move |p| {
        parse_propexpr_seq(p, precedence)
    });
    pp.add_greedy("property expression", move |p| {
        parse_propexpr_nonseq(p, precedence)
    });
    let data = pp.finish(p, "sequence or primary property expression")?;

    span.expand(p.last_span());
    let expr = PropExpr {
        span: span,
        data: data,
    };
    parse_propexpr_suffix(p, expr, precedence)
}

fn parse_propexpr_nonseq<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<PropExprData<'n>> {
    // Handle the trivial case of expressions introduced by a symbol or keyword.
    match p.peek(0).0 {
        // Parenthesized property expression.
        OpenDelim(Paren) => return flanked(p, Paren, parse_propexpr).map(|pe| pe.data),

        // "not" operator
        Keyword(Kw::Not) => {
            p.bump();
            let expr = parse_propexpr_prec(p, PropSeqPrecedence::NotNexttime)?;
            return Ok(PropExprData::Not(Box::new(expr)));
        }

        // Clocking event
        At => {
            p.bump();
            let ev = parse_event_expr(p, EventPrecedence::Min)?;
            let expr = parse_propexpr(p)?;
            return Ok(PropExprData::Clocked(ev, Box::new(expr)));
        }

        _ => {
            let q = p.peek(0).1;
            p.add_diag(DiagBuilder2::error("expected primary property expression").span(q));
            return Err(());
        }
    }
}

fn parse_propexpr_seq<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<PropExprData<'n>> {
    // Consume a strong, weak, or regular sequence operator.
    let (seqop, seqexpr) = match p.peek(0).0 {
        Keyword(Kw::Strong) => {
            p.bump();
            (PropSeqOp::Strong, flanked(p, Paren, parse_seqexpr)?)
        }
        Keyword(Kw::Weak) => {
            p.bump();
            (PropSeqOp::Weak, flanked(p, Paren, parse_seqexpr)?)
        }
        _ => (PropSeqOp::None, parse_seqexpr_prec(p, precedence)?),
    };

    // Handle the operators that have a sequence expression on their left hand
    // side.
    if precedence <= PropSeqPrecedence::ImplFollow {
        if let Some(op) = match p.peek(0).0 {
            Operator(Op::SeqImplOl) => Some(PropSeqBinOp::ImplOverlap),
            Operator(Op::SeqImplNol) => Some(PropSeqBinOp::ImplNonoverlap),
            Operator(Op::SeqFollowOl) => Some(PropSeqBinOp::FollowOverlap),
            Operator(Op::SeqFollowNol) => Some(PropSeqBinOp::FollowNonoverlap),
            _ => None,
        } {
            p.bump();
            let expr = parse_propexpr_prec(p, PropSeqPrecedence::ImplFollow)?;
            return Ok(PropExprData::SeqBinOp(op, seqop, seqexpr, Box::new(expr)));
        }
    }

    // Otherwise this is just a simple sequence operator.
    Ok(PropExprData::SeqOp(seqop, seqexpr))
}

fn parse_propexpr_suffix<'n>(
    p: &mut dyn AbstractParser<'n>,
    prefix: PropExpr<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<PropExpr<'n>> {
    // Handle the binary operators that have a property expression on both their
    // left and right hand side.
    if let Some((op, prec, rassoc)) = match p.peek(0).0 {
        Keyword(Kw::Or) => Some((PropBinOp::Or, PropSeqPrecedence::Or, false)),
        Keyword(Kw::And) => Some((PropBinOp::And, PropSeqPrecedence::And, false)),
        Keyword(Kw::Until) => Some((PropBinOp::Until, PropSeqPrecedence::Until, true)),
        Keyword(Kw::SUntil) => Some((PropBinOp::SUntil, PropSeqPrecedence::Until, true)),
        Keyword(Kw::UntilWith) => Some((PropBinOp::UntilWith, PropSeqPrecedence::Until, true)),
        Keyword(Kw::SUntilWith) => Some((PropBinOp::SUntilWith, PropSeqPrecedence::Until, true)),
        Keyword(Kw::Implies) => Some((PropBinOp::Impl, PropSeqPrecedence::Until, true)),
        Keyword(Kw::Iff) => Some((PropBinOp::Iff, PropSeqPrecedence::Iff, true)),
        _ => None,
    } {
        if precedence < prec || (rassoc && precedence == prec) {
            p.bump();
            let rhs = parse_propexpr_prec(p, prec)?;
            return Ok(PropExpr {
                span: Span::union(prefix.span, rhs.span),
                data: PropExprData::BinOp(op, Box::new(prefix), Box::new(rhs)),
            });
        }
    }

    Ok(prefix)
}

fn parse_seqexpr<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<SeqExpr<'n>> {
    parse_seqexpr_prec(p, PropSeqPrecedence::Min)
}

fn parse_seqexpr_prec<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<SeqExpr<'n>> {
    let mut span = p.peek(0).1;

    // See parse_propexpr_prec for an explanation of why we need a parallel
    // parser here.
    let mut pp = ParallelParser::new();
    pp.add_greedy("expression", move |p| parse_seqexpr_expr(p, precedence));
    pp.add_greedy("sequence", move |p| parse_seqexpr_nonexpr(p, precedence));
    let data = pp.finish(p, "sequence or primary property expression")?;

    span.expand(p.last_span());
    let expr = SeqExpr {
        span: span,
        data: data,
    };
    parse_seqexpr_suffix(p, expr, precedence)
}

fn parse_seqexpr_expr<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<SeqExprData<'n>> {
    // TODO: Handle all the non-trivial cases.
    let q = p.peek(0).1;
    p.add_diag(
        DiagBuilder2::error(
            "Don't know how to parse sequence expression that don't start with an expression",
        )
        .span(q),
    );
    Err(())
}

fn parse_seqexpr_nonexpr<'n>(
    p: &mut dyn AbstractParser<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<SeqExprData<'n>> {
    // If we arrive here, the only possibility left is that this sequence starts
    // with and expression or distribution.
    let expr = parse_expr(p)?;

    // Handle the case of the "throughout" operator that has an expression on
    // its left hand side.
    if precedence <= PropSeqPrecedence::Throughout && p.try_eat(Keyword(Kw::Throughout)) {
        let rhs = parse_seqexpr_prec(p, PropSeqPrecedence::Throughout)?;
        return Ok(SeqExprData::Throughout(expr, Box::new(rhs)));
    }

    // Parse the optional repetition.
    let rep = try_flanked(p, Brack, parse_seqrep)?;

    Ok(SeqExprData::Expr(expr, rep))
}

fn parse_seqexpr_suffix<'n>(
    p: &mut dyn AbstractParser<'n>,
    prefix: SeqExpr<'n>,
    precedence: PropSeqPrecedence,
) -> ReportedResult<SeqExpr<'n>> {
    // TODO: Handle all the binary operators.
    Ok(prefix)
}

fn parse_seqrep<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<SeqRep<'n>> {
    match p.peek(0).0 {
        // [*]
        // [* expr]
        Operator(Op::Mul) => {
            p.bump();
            if p.peek(0).0 == CloseDelim(Brack) {
                Ok(SeqRep::ConsecStar)
            } else {
                Ok(SeqRep::Consec(parse_expr(p)?))
            }
        }

        // [+]
        Operator(Op::Add) => {
            p.bump();
            Ok(SeqRep::ConsecPlus)
        }

        // [= expr]
        Operator(Op::Assign) => {
            p.bump();
            Ok(SeqRep::Nonconsec(parse_expr(p)?))
        }

        // [-> expr]
        Operator(Op::LogicImpl) => {
            p.bump();
            Ok(SeqRep::Goto(parse_expr(p)?))
        }

        _ => {
            let q = p.peek(0).1;
            p.add_diag(
                DiagBuilder2::error(
                    "expected sequence repetition [+], [*], [* <expr>], [= <expr>], or [-> <expr>]",
                )
                .span(q),
            );
            Err(())
        }
    }
}

fn parse_inst<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::Inst<'n>> {
    let mut span = p.peek(0).1;

    // Consume the module identifier.
    let target = parse_identifier(p, "module name")?;
    // TODO: Add support for interface instantiations.

    // Consume the optional parameter value assignment.
    let params = if p.try_eat(Hashtag) {
        parse_parameter_assignments(p)?
    } else {
        Vec::new()
    };

    // Consume the instantiations.
    let names = comma_list_nonempty(p, Semicolon, "hierarchical instance", |p| {
        let mut span = p.peek(0).1;
        let name = parse_identifier(p, "instance name")?;
        let (dims, _) = parse_optional_dimensions(p)?;
        let conns = flanked(p, Paren, parse_list_of_port_connections)?;
        span.expand(p.last_span());
        Ok(ast::InstName {
            span: span,
            name: name,
            dims: dims,
            conns: conns,
        })
    })?;

    p.require_reported(Semicolon)?;
    span.expand(p.last_span());
    Ok(ast::Inst {
        span: span,
        target: target,
        params: params,
        names: names,
    })
}

fn parse_var_decl<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<ast::VarDecl<'n>> {
    let mut span = p.peek(0).1;

    // Parse the optional `const` keyword.
    let konst = p.try_eat(Keyword(Kw::Const));

    // Parse the optional `var` keyword.
    let var = p.try_eat(Keyword(Kw::Var));

    // Parse the optional lifetime specifier.
    let lifetime = as_lifetime(p.peek(0).0);
    if lifetime.is_some() {
        p.bump();
    }

    // Branch to try the explicit and implicit type version. Note that the
    // implicit version is only allowed if the `var` keyword is present. This
    // avoids ambiguity with assign statements.
    let mut pp = ParallelParser::new();
    pp.add("explicit type", |p| {
        let ty = parse_explicit_type(p)?;
        Ok((ty, tail(p)?))
    });
    if var {
        pp.add("implicit type", |p| {
            let ty = parse_implicit_type(p)?;
            Ok((ty, tail(p)?))
        });
    }
    let (ty, names) = pp.finish(p, "explicit or implicit type")?;

    fn tail<'n>(p: &mut dyn AbstractParser<'n>) -> ReportedResult<Vec<VarDeclName<'n>>> {
        let names = comma_list_nonempty(
            p,
            Semicolon,
            "variable name",
            parse_variable_decl_assignment,
        )?;
        p.require_reported(Semicolon)?;
        Ok(names)
    }

    span.expand(p.last_span());
    Ok(ast::VarDecl {
        span: span,
        konst: konst,
        var: var,
        lifetime: lifetime,
        ty: ty,
        names: names,
    })
}

fn parse_param_decl<'n>(
    p: &mut dyn AbstractParser<'n>,
    keyword_optional: bool,
) -> ReportedResult<ast::ParamDecl<'n>> {
    let mut span = p.peek(0).1;

    // Eat the possibly optional `parameter` or `localparam` keyword. This
    // determines whether the parameter is considered local. Omitting the
    // keyword makes it non-local.
    let local = match p.peek(0) {
        (Keyword(Kw::Localparam), _) => {
            p.bump();
            true
        }
        (Keyword(Kw::Parameter), _) => {
            p.bump();
            false
        }
        (_, _) if keyword_optional => false,
        (tkn, sp) => {
            p.add_diag(
                DiagBuilder2::error(format!(
                    "expected `parameter` or `localparam`, but found {} instead",
                    tkn
                ))
                .span(sp),
            );
            return Err(());
        }
    };

    // Define a predicate that checks whether the end of a parameter list has
    // been reached. This is somewhat tricky due to the fact that the parameter
    // declaration may appear in two contexts: As a standalone statement, or
    // inside a parameter port list of a module or interface. The former is
    // trivial since it is terminated by a ";". The latter, however, is more
    // involved, since it is terminated by a "," or ")". The comma complicates
    // things, as it requires us to check beyond the next token to check if the
    // end of the list has been reached. The list terminates if after the "," a
    // "parameter", "localparam", "type", or explicit type follows.
    let predicate = FuncPredicate {
        match_func: |p| match p.peek(0).0 {
            Semicolon | CloseDelim(Paren) => true,
            Comma => match p.peek(1).0 {
                Keyword(Kw::Parameter) | Keyword(Kw::Localparam) => true,
                _ => false,
            },
            _ => false,
        },
        recover_func: |p, consume| p.recover_balanced(&[CloseDelim(Paren), Semicolon], consume),
        desc: ") or ;",
    };

    // If the next token is the `type` keyword, this is a type parameter.
    // Otherwise this is a value parameter.
    let kind = if p.try_eat(Keyword(Kw::Type)) {
        let decls = comma_list_nonempty(p, predicate, "parameter name", |p| {
            let mut span = p.peek(0).1;
            let name = parse_identifier(p, "parameter name")?;
            let ty = if p.try_eat(Operator(Op::Assign)) {
                Some(parse_explicit_type(p)?)
            } else {
                None
            };
            p.anticipate(&[Semicolon, Comma, CloseDelim(Paren)])?;
            span.expand(p.last_span());
            Ok(ast::ParamTypeDecl {
                span: span,
                name: name,
                ty: ty,
            })
        })?;
        p.anticipate(&[Semicolon, Comma, CloseDelim(Paren)])?;
        ast::ParamKind::Type(decls)
    } else {
        let decls = comma_list_nonempty(p, predicate, "parameter name", |p| {
            // Use a parallel parser to distinguish between the explicit and
            // implicit type versions of the declaration.
            let mut pp = ParallelParser::new();
            pp.add("explicit type", |p| {
                let ty = parse_explicit_type(p)?;
                tail(p, ty)
            });
            pp.add("implicit type", |p| {
                let ty = parse_implicit_type(p)?;
                tail(p, ty)
            });

            fn tail<'n>(
                p: &mut dyn AbstractParser<'n>,
                ty: Type<'n>,
            ) -> ReportedResult<ast::ParamValueDecl<'n>> {
                let mut span = p.peek(0).1;
                let name = parse_identifier(p, "parameter name")?;
                let (dims, _) = parse_optional_dimensions(p)?;
                let expr = if p.try_eat(Operator(Op::Assign)) {
                    Some(parse_expr(p)?)
                } else {
                    None
                };
                p.anticipate(&[Semicolon, Comma, CloseDelim(Paren)])?;
                span.expand(p.last_span());
                Ok(ast::ParamValueDecl {
                    span: span,
                    ty: ty,
                    name: name,
                    dims: dims,
                    expr: expr,
                })
            }

            pp.finish(p, "explicit or implicit type")
        })?;
        p.anticipate(&[Semicolon, Comma, CloseDelim(Paren)])?;
        ast::ParamKind::Value(decls)
    };

    span.expand(p.last_span());
    Ok(ParamDecl {
        span: span,
        local: local,
        kind: kind,
    })
}

fn parse_hname<'n>(p: &mut dyn AbstractParser<'n>, msg: &str) -> ReportedResult<ast::Identifier> {
    parse_identifier(p, msg)
}

#[cfg(test)]
mod tests {
    use crate::lexer::*;
    use crate::preproc::*;
    use moore_common::source::*;

    fn parse(input: &str) {
        use std::cell::Cell;
        thread_local!(static INDEX: Cell<usize> = Cell::new(0));
        let sm = get_source_manager();
        let idx = INDEX.with(|i| {
            let v = i.get();
            i.set(v + 1);
            v
        });
        let source = sm.add(&format!("test_{}.sv", idx), input);
        let pp = Preprocessor::new(source, &[], &[]);
        let lexer = Lexer::new(pp);
        super::parse(lexer).unwrap();
    }

    #[test]
    fn intf_empty() {
        parse("interface Foo; endinterface");
    }

    #[test]
    fn intf_params() {
        parse("interface Foo #(); endinterface");
        parse("interface Foo #(parameter bar = 32); endinterface");
        parse("interface Foo #(parameter bar = 32, baz = 64); endinterface");
        parse("interface Foo #(parameter bar = 32, parameter baz = 64); endinterface");
    }

    #[test]
    fn intf_header() {
        // parse("interface Foo ();")
    }
}

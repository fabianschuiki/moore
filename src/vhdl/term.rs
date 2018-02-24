// Copyright (c) 2018 Fabian Schuiki

//! Expressions

#![deny(missing_docs)]

use std::collections::HashMap;

use num::BigInt;

use common::errors::*;
use common::source::*;
use common::util::*;
use common::score::{Result, NodeRef};
use common::NodeId;

use syntax::lexer::token::Literal;
use syntax::ast::{self, Dir};
use score::*;
use hir;
use konst::ConstInt;
use add_ctx::AddContext;

/// A term.
///
/// This is a generalization of expressions and names in VHDL. It allows various
/// parts of the AST to be mapped to a common data structure, and then remapped
/// to the desired output structure. This is useful for example if the parser
/// processes a subtype indication as an expression.
#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    /// A term of the form `null`.
    Null,
    /// A term of the form `open`.
    Open,
    /// A term of the form `others`.
    Others,
    /// A term of the form `default`.
    Default,
    /// An integer literal.
    IntLit(BigInt),
    /// An unresolved name.
    Unresolved(ResolvableName),
    /// A term that refers to a definition.
    Ident(Spanned<Def>),
    /// A term that refers to a type or subtype definition.
    TypeMark(Spanned<TypeMarkRef>),
    /// A term that refers to an enum variant.
    Enum(Vec<Spanned<EnumRef>>),
    /// A term of the form `T.<name>`.
    Select(Subterm, Spanned<ResolvableName>),
    /// A term of the form `T.all`.
    SelectAll(Subterm),
    /// A term of the form `T (to|downto) T`.
    Range(Dir, Subterm, Subterm),
    /// A term of the form `T range T`.
    RangeSuffix(Subterm, Subterm),
    /// A term of the form `T range <>`.
    UnboundedRange(Subterm),
    /// A term of the form `[T] <type_mark> [T]`. The first optional subterm is
    /// the resolution indication, the second is the constraint.
    SubtypeInd(Spanned<TypeMarkRef>, Option<Subterm>, Option<Subterm>),
    /// A term of the form `(T) T`.
    PrefixParen(Subterm, Subterm),
    /// A term of the form `T (T)`.
    SuffixParen(Subterm, Subterm),
    /// A term of the form `(T,T,…)`.
    Paren(Vec<Spanned<Term>>),
    /// A term of the form `(T|T|… => T, T|T|… => T, …)`.
    Aggregate(Vec<(Vec<Spanned<Term>>, Spanned<Term>)>),
    /// A term of the form `op T`.
    Unary(Spanned<hir::UnaryOp>, Subterm),
    /// A term of the form `T op T`.
    Binary(Spanned<hir::BinaryOp>, Subterm, Subterm),
    /// A term of the form `T'T`.
    Qual(Subterm, Subterm),
    /// A term of the form `new T`.
    New(Subterm),
}

/// A subterm.
pub type Subterm = Box<Spanned<Term>>;

/// A context within which termification can occur.
pub struct TermContext<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb> {
    /// The underlying scoreboard context.
    pub ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>,
    /// The scope within which the terms will resolve their names.
    pub scope: ScopeRef,
}

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> DiagEmitter for TermContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    fn emit(&self, diag: DiagBuilder2) {
        self.ctx.emit(diag)
    }
}

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> TermContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Create a new termification context.
    pub fn new(ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>, scope: ScopeRef) -> TermContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
        TermContext {
            ctx: ctx,
            scope: scope,
        }
    }

    /// Perform term folding.
    ///
    /// This is a post-processing step that should be applied to all terms once
    /// they are constructed. Folding applies transformations to the terms, e.g.
    /// changing `Ident(Type|Subtype)` to `TypeMark`, or gobbling up subtype
    /// constraints where appropriate.
    pub fn fold(&self, term: Spanned<Term>) -> Spanned<Term> {
        let new = match term.value {
            Term::Ident(Spanned{ value: Def::Type(id), span }) => {
                Term::TypeMark(Spanned::new(id.into(), span))
            }
            Term::Ident(Spanned{ value: Def::Subtype(id), span }) => {
                Term::TypeMark(Spanned::new(id.into(), span))
            }
            other => other
        };
        Spanned::new(new, term.span)
    }

    /// Map an AST subtype indication to a term.
    pub fn termify_subtype_ind(&self, subty: &'ast ast::SubtypeInd) -> Result<Spanned<Term>> {
        let name = self.termify_compound_name(&subty.name)?;
        let res = match subty.res {
            Some(ast::ResolInd::Exprs(ref paren_elems)) => Some(self.termify_paren_elems(paren_elems)?),
            Some(ast::ResolInd::Name(ref name)) => Some(self.termify_compound_name(name)?),
            None => None,
        };
        if let Some(res) = res {
            let sp = Span::union(name.span, res.span);
            Ok(Spanned::new(Term::PrefixParen(Box::new(res), Box::new(name)), sp))
        } else {
            Ok(name)
        }
    }

    /// Map an AST expression to a term.
    pub fn termify_expr(&self, ast: &'ast ast::Expr) -> Result<Spanned<Term>> {
        let term = match ast.data {
            // Literals with optional unit.
            ast::LitExpr(ref lit, ref unit) => {
                let lit = self.termify_literal(Spanned::new(lit, ast.span))?;
                let unit = match *unit {
                    Some(ref unit_name) => Some(self.termify_compound_name(unit_name)?),
                    None => None,
                };
                if let Some(unit) = unit {
                    self.emit(
                        DiagBuilder2::bug(format!("termification of physical type `{}` not implemented", unit.span().extract()))
                        .span(unit.span())
                    );
                    return Err(());
                } else {
                    return Ok(lit);
                }
            }
            ast::NameExpr(ref name) => return self.termify_compound_name(name),
            // ast::ResolExpr(ref paren_elems, ref name) => {
            //  let name = self.termify_compound_name(name)?;
            // }
            // Ranges of the form `T to T` and `T downto T`.
            ast::BinaryExpr(ast::BinaryOp::Dir(d), ref lb, ref rb) => {
                Term::Range(d, self.termify_expr(lb)?.into(), self.termify_expr(rb)?.into())
            }
            ast::UnaryExpr(op, ref arg) => Term::Unary(
                self.ctx.lower_unary_op(Spanned::new(op, ast.span))?,
                self.termify_expr(arg)?.into(),
            ),
            ast::BinaryExpr(op, ref lhs, ref rhs) => Term::Binary(
                self.ctx.lower_binary_op(Spanned::new(op, ast.span))?,
                self.termify_expr(lhs)?.into(),
                self.termify_expr(rhs)?.into(),
            ),
            ast::NullExpr => Term::Null,
            ast::OpenExpr => Term::Open,
            ast::OthersExpr => Term::Others,
            ast::DefaultExpr => Term::Default,
            ast::ParenExpr(ref elems) => self.termify_paren_elems(elems)?.value,
            ast::QualExpr(ref name, ref arg) => Term::Qual(
                self.termify_compound_name(name)?.into(),
                self.termify_paren_elems(arg)?.into(),
            ),
            ast::NewExpr(ref expr) => Term::New(self.termify_expr(expr)?.into()),
            ref wrong => {
                self.emit(
                    DiagBuilder2::bug(format!("termification of expression `{}` not implemented", ast.span.extract()))
                    .span(ast.span)
                    .add_note(format!("{:?}", wrong))
                );
                return Err(());
            }
        };
        Ok(self.fold(Spanned::new(term, ast.span)))
    }

    /// Map an AST literal to a term.
    pub fn termify_literal(&self, ast: Spanned<&'ast Literal>) -> Result<Spanned<Term>> {
        Ok(Spanned::new(match *ast.value {
            Literal::Abstract(base, int, frac, exp) => {
                let base = match base {
                    Some(base) => match base.as_str().parse() {
                        Ok(base) => base,
                        Err(_) => {
                            self.emit(
                                DiagBuilder2::error(format!("`{}` is not a valid base for a number literal", base))
                                .span(ast.span)
                            );
                            return Err(());
                        }
                    },
                    None => 10,
                };
                let int = match BigInt::parse_bytes(int.as_str().as_bytes(), base) {
                    Some(v) => v,
                    None => {
                        self.emit(
                            DiagBuilder2::error(format!("`{}` is not a valid base-{} integer", int, base))
                            .span(ast.span)
                        );
                        return Err(());
                    }
                };

                // Parse the rest of the number.
                if frac.is_none() && exp.is_none() {
                    Term::IntLit(int)
                } else {
                    self.emit(
                        DiagBuilder2::bug("Float literals not yet supported")
                        .span(ast.span)
                    );
                    return Err(());
                }
            }
            ref wrong => {
                self.emit(
                    DiagBuilder2::bug(format!("termification of literal `{}` not implemented", ast.span.extract()))
                    .span(ast.span)
                    .add_note(format!("{:?}", wrong))
                );
                return Err(());
            }
        }, ast.span))
    }

    /// Map an AST compound name to a term.
    pub fn termify_compound_name(&self, ast: &'ast ast::CompoundName) -> Result<Spanned<Term>> {
        // Map the primary name.
        let mut term = self.fold(self.termify_name(
            self.ctx.resolvable_from_primary_name(&ast.primary)?
        )?);

        // For each name part, wrap the term in another layer. Like an onion.
        for part in &ast.parts {
            term = self.fold(match *part {
                ast::NamePart::Select(ref primary) => {
                    let n = self.ctx.resolvable_from_primary_name(primary)?;
                    let sp = Span::union(term.span, n.span);
                    Spanned::new(Term::Select(Box::new(term), n), sp)
                }
                ast::NamePart::SelectAll(span) => {
                    let sp = Span::union(term.span, span);
                    Spanned::new(Term::SelectAll(Box::new(term)), sp)
                }
                ast::NamePart::Signature(ref sig) => {
                    self.emit(
                        DiagBuilder2::bug(format!("termification of signature suffix `{}` not implemented", sig.span.extract()))
                        .span(sig.span)
                    );
                    return Err(());
                }
                ast::NamePart::Attribute(ident) => {
                    let attr = self.termify_name(Spanned::new(ident.name.into(), ident.span))?;
                    match attr.value {
                        // TODO: Enable this as soon as we handle attribute
                        // declarations.
                        // Term::Ident(Spanned { value: Def::Attr(id), span }) => {
                        //  let sp = Span::union(term.span, attr.span);
                        //  Spanned::new(Term::Attribute(Box::new(term), Spanned::new(id, span)), sp)
                        // }
                        Term::Ident(other) => {
                            self.emit(
                                DiagBuilder2::error(format!("`{}` is not an attribute name", ident.name))
                                .span(ident.span)
                                .add_note("Declared here:")
                                .span(other.span)
                            );
                            return Err(());
                        }
                        _ => unreachable!(),
                    }
                }
                ast::NamePart::Call(ref paren_elems) => {
                    let subterm = self.termify_paren_elems(paren_elems)?;
                    let sp = Span::union(term.span, subterm.span);
                    Spanned::new(Term::SuffixParen(Box::new(term), Box::new(subterm)), sp)
                }
                ast::NamePart::Range(ref expr) => {
                    if expr.data == ast::BoxExpr {
                        let sp = Span::union(term.span, expr.span);
                        Spanned::new(Term::UnboundedRange(Box::new(term)), sp)
                    } else {
                        let expr = self.termify_expr(expr)?;
                        let sp = Span::union(term.span, expr.span);
                        Spanned::new(Term::RangeSuffix(Box::new(term), Box::new(expr)), sp)
                    }
                }
            });
        }

        Ok(term)
    }

    /// Map a resolvable name to a term.
    ///
    /// This function is the bottom of the pit. Names are resolved here and
    /// mapped to the corresponding term. Calling functions may then proceed to
    /// handle the term as they see fit, usually inspecting what exact kind the
    /// term is of.
    pub fn termify_name(&self, name: Spanned<ResolvableName>) -> Result<Spanned<Term>> {
        // First resolve the name to a list of definitions.
        let mut defs = self.ctx.resolve_name(name, self.scope, false, true)?;
        if defs.is_empty() {
            return Ok(name.map(Term::Unresolved));
        }

        fn is_enum(def: &Spanned<Def>) -> bool { match def.value { Def::Enum(..) => true, _ => false }}
        let all_enum = defs.iter().all(is_enum);

        // Handle overloading. Basically if the definitions are all enum fields
        // or functions, that's fine. For everything else the name must be
        // unique.
        let first_def = defs.pop().unwrap();
        let term = match first_def.value {
            Def::Enum(id) if all_enum => {
                let mut ids = vec![Spanned::new(id, first_def.span)];
                for def in defs {
                    match def.value {
                        Def::Enum(id) => ids.push(Spanned::new(id, def.span)),
                        _ => unreachable!(),
                    }
                }
                Term::Enum(ids)
            }
            // TODO: Handle the function case.
            _ if !defs.is_empty() => {
                let mut d = DiagBuilder2::error(format!("`{}` is ambiguous", name.value)).span(name.span);
                d = d.add_note("Found the following definitions:");
                d = d.span(first_def.span());
                for def in defs {
                    d = d.span(def.span());
                }
                self.emit(d);
                return Err(());
            }
            _ => Term::Ident(first_def),
        };

        Ok(self.fold(Spanned::new(term, name.span)))
    }

    /// Map multiple parenthesis elements to a term.
    pub fn termify_paren_elems(&self, elems: &'ast ast::ParenElems) -> Result<Spanned<Term>> {
        let is_aggregate = elems.value.iter().any(|e| !e.choices.value.is_empty());
        let term = if is_aggregate {
            Term::Aggregate(elems.value.iter().map(|e| Ok((
                e.choices.value.iter().map(|c| self.termify_expr(c)).collect::<Result<Vec<_>>>()?,
                self.termify_expr(&e.expr)?
            ))).collect::<Result<Vec<_>>>()?)
        } else {
            Term::Paren(elems.value
                .iter()
                .map(|e| self.termify_expr(&e.expr))
                .collect::<Result<Vec<_>>>()?
            )
        };
        Ok(self.fold(Spanned::new(term, elems.span)))
    }

    /// Map a latent name to a term.
    pub fn termify_latent_name(&self, name: LatentName<'ast>) -> Result<Spanned<Term>> {
        match name {
            LatentName::Simple(n) => self.termify_name(n.map_into()),
            LatentName::Primary(n) => self.termify_name(self.ctx.resolvable_from_primary_name(n)?),
            LatentName::Compound(n) => self.termify_compound_name(n),
        }
    }

    /// Map a term to an expression and schedule the necessary tasks.
    pub fn term_to_expr(&self, term: Spanned<Term>) -> Result<ExprRef> {
        let ctx = AddContext::new(self.ctx, self.scope);
        ctx.add_expr_hir(self.term_to_expr_raw(term)?)
    }

    /// Map a term to an expression.
    pub fn term_to_expr_raw(&self, term: Spanned<Term>) -> Result<hir::Expr> {
        let term_span = term.span;
        let data = match term.value {
            Term::Unresolved(name) => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is unknown", name))
                    .span(term.span)
                );
                return Err(());
            }
            Term::IntLit(value) => {
                hir::ExprData::IntegerLiteral(ConstInt::new(None, value))
            }
            Term::Unary(op, arg) => {
                hir::ExprData::Unary(op, self.term_to_expr(*arg)?)
            }
            // TODO: Enable this as soon as the HIR accepts BinaryOp.
            // Term::Binary(op, lhs, rhs) => {
            //  hir::ExprData::Binary(op, self.term_to_expr(*lhs)?, self.term_to_expr(*rhs)?)
            // }
            Term::Ident(def) => {
                // TODO: If the definition is a subprogram, turn this into a
                // call expression.
                hir::ExprData::Name(def.value, def.span)
            }
            Term::Enum(defs) => {
                hir::ExprData::OverloadedName(defs.into_iter().map(|d| d.map_into()).collect())
            }
            Term::Select(term, name) => {
                hir::ExprData::Select(self.term_to_expr(*term)?, name)
            }
            Term::Paren(subterm) => {
                // A parenthesis with only one element is just a parenthesized
                // expression. If there's more than one element, this is a
                // purely positional aggregate.
                if subterm.len() == 1 {
                    return self.term_to_expr_raw(subterm.into_iter().next().unwrap());
                } else {
                    hir::ExprData::Aggregate(self.term_to_aggregate(
                        Spanned::new(Term::Paren(subterm), term.span)
                    )?.value)
                }
            }
            Term::Aggregate(..) => {
                hir::ExprData::Aggregate(self.term_to_aggregate(term)?.value)
            }
            Term::Qual(tm, term) => {
                hir::ExprData::Qualified(
                    self.term_to_type_mark(*tm)?,
                    self.term_to_expr(*term)?,
                )
            }

            // Allocators (`new` expressions) either have a type mark as their
            // argument, or a qualified expression which also provides the value
            // of the thing to allocate.
            Term::New(arg) => {
                let arg = *arg;
                match arg.value {
                    Term::Qual(tm, value) => hir::ExprData::Allocator(
                        self.term_to_type_mark(*tm)?,
                        Some(self.term_to_expr(*value)?),
                    ),
                    other => hir::ExprData::Allocator(
                        self.term_to_type_mark(Spanned::new(other, arg.span))?,
                        None,
                    ),
                }
            }

            // Function calls and cast expression look almost the same. The only
            // way to differentiate them is to look at the kind of the callee.
            Term::SuffixParen(callee, args) => {
                let callee = *callee;
                let args = self.term_to_assoc_list(*args)?;
                match callee.value {
                    Term::TypeMark(tm) => {
                        if args.value.len() != 1 {
                            self.emit(
                                DiagBuilder2::error(format!("cast `{}` must have exactly one argument", term_span.extract()))
                                .span(args.span)
                            );
                            return Err(());
                        }
                        let arg = args.value.into_iter().next().unwrap();
                        if let Some(formal) = arg.formal {
                            self.emit(
                                DiagBuilder2::error(format!("cast argument `{}` cannot have a formal part", arg.span.extract()))
                                .span(formal.span)
                            );
                        }
                        let arg = match arg.actual.value {
                            hir::AssocActual::Expr(id) => id,
                            _ => {
                                self.emit(
                                    DiagBuilder2::error(format!("`{}` is not a valid cast argument", arg.actual.span.extract()))
                                    .span(arg.actual.span)
                                );
                                return Err(());
                            }
                        };
                        hir::ExprData::Cast(tm, arg)
                    }
                    other => {
                        hir::ExprData::Call(
                            self.term_to_expr(Spanned::new(other, callee.span))?,
                            args,
                        )
                    }
                }
            }

            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid expression", term.span.extract()))
                    .span(term.span)
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        };
        Ok(hir::Expr {
            parent: self.scope,
            span: term_span,
            data: data
        })
    }

    /// Map a term to a type mark.
    pub fn term_to_type_mark(&self, term: Spanned<Term>) -> Result<Spanned<TypeMarkRef>> {
        match term.value {
            Term::TypeMark(tm) => Ok(tm),
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a type or subtype", term.span.extract()))
                    .span(term.span)
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        }
    }

    /// Perform term folding expecting to yield a type.
    ///
    /// This is a pre-processing step on terms. It is applied as soon as it is
    /// clear that a certain term should yield a type, e.g. when mapping to a
    /// subtype indication. This function performs certain precedence swaps and
    /// combines terms into higher level ones, e.g. `Term::SubtypeInd`.
    pub fn fold_term_as_type(&self, term: Spanned<Term>) -> Result<Spanned<Term>> {
        let (new, new_term) = match term.value {
            Term::Unresolved(name) => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is unknown", name))
                    .span(term.span)
                );
                return Err(());
            }
            Term::RangeSuffix(subterm, range) => {
                let subterm = self.fold_term_as_type(*subterm)?;
                let range = self.fold_term_as_type(*range)?;
                match subterm.value {
                    // Fold `TypeMark range T` to `SubtypeInd`.
                    Term::TypeMark(tm) => (true, Term::SubtypeInd(tm, None, Some(Box::new(range)))),
                    // Fold `SubtypeInd range T` to `SubtypeInd`.
                    Term::SubtypeInd(tm, resol, Some(con)) => {
                        let sp = Span::union(con.span, range.span);
                        let new_con = Spanned::new(Term::RangeSuffix(con, Box::new(range)), sp);
                        (true, Term::SubtypeInd(tm, resol, Some(Box::new(new_con))))
                    }
                    _ => (false, Term::RangeSuffix(Box::new(subterm), Box::new(range))),
                }
            }
            Term::SuffixParen(subterm, suffix) => {
                let subterm = self.fold_term_as_type(*subterm)?;
                let suffix = self.fold_term_as_type(*suffix)?;
                match subterm.value {
                    // Fold `TypeMark (T)` to `SubtypeInd`.
                    Term::TypeMark(tm) => (true, Term::SubtypeInd(tm, None, Some(Box::new(suffix)))),
                    // Fold `SubtypeInd (T)` to `SubtypeInd`.
                    Term::SubtypeInd(tm, resol, Some(con)) => {
                        let sp = Span::union(con.span, suffix.span);
                        let new_con = Spanned::new(Term::SuffixParen(con, Box::new(suffix)), sp);
                        (true, Term::SubtypeInd(tm, resol, Some(Box::new(new_con))))
                    }
                    // Fold `SubtypeInd (T)` to `SubtypeInd`.
                    Term::SubtypeInd(tm, resol, None) => {
                        (true, Term::SubtypeInd(tm, resol, Some(Box::new(suffix))))
                    }
                    _ => (false, Term::SuffixParen(Box::new(subterm), Box::new(suffix))),
                }
            }
            others => (false, others)
        };
        let new_term = Spanned::new(new_term, term.span);
        if new {
            self.fold_term_as_type(new_term)
        } else {
            Ok(new_term)
        }
    }

    /// Map a term to a subtype indication.
    pub fn term_to_subtype_ind(&self, term: Spanned<Term>) -> Result<Spanned<hir::SubtypeInd>> {
        let term = self.fold_term_as_type(term)?;
        let (tm, resol, con) = match term.value {
            Term::SubtypeInd(tm, resol, con) => (tm, resol, con),
            Term::TypeMark(tm) => (tm, None, None),
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a subtype indication", term.span.extract()))
                    .span(term.span)
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        };
        let _resol = match resol {
            Some(x) => Some(self.term_to_resolution_indication(*x)?),
            None => None,
        };
        let con = match con {
            Some(x) => Some(self.term_to_constraint(*x)?),
            None => None,
        };
        Ok(Spanned::new(hir::SubtypeInd {
            span: term.span,
            type_mark: tm,
            // TODO: Track resolution indication.
            constraint: con,
        }, term.span))
        // let id = SubtypeIndRef::new(NodeId::alloc());
        // self.ctx.set_hir(id, self.ctx.sb.arenas.hir.subtype_ind.alloc(hir));
        // Ok(Spanned::new(id, term.span))
    }

    /// Map a term to a resolution indication.
    pub fn term_to_resolution_indication(&self, term: Spanned<Term>) -> Result<Spanned<()>> {
        self.emit(
            DiagBuilder2::bug(format!("interpretation of `{}` as a resolution indication not implemented", term.span.extract()))
            .span(term.span)
        );
        Err(())
    }

    /// Map a term to a constraint.
    pub fn term_to_constraint(&self, term: Spanned<Term>) -> Result<Spanned<hir::Constraint>> {
        // Handle range constraints.
        match term.value {
            Term::Range(..) => return Ok(self.term_to_range(term)?.map(|r| hir::Constraint::Range(r))),
            _ => ()
        };

        // Unpack the optional element constraint on array constraints.
        let (term, elem) = match term.value {
            Term::RangeSuffix(subterm, con) | Term::SuffixParen(subterm, con) => (*subterm, Some(*con)),
            _ => (term, None),
        };

        // Otherwise handle the array and record constraint cases.
        match term.value {
            Term::Paren(terms) => {
                let any_records = terms.iter().any(|t| match t.value {
                    Term::SuffixParen(..) => true,
                    _ => false,
                });
                if any_records && elem.is_none() {
                    self.term_to_record_constraint(term.span, terms).map(|t| t.map_into())
                } else {
                    self.term_to_array_constraint(term.span, terms, elem).map(|t| t.map_into())
                }
            }
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid constraint", term.span.extract()))
                    .span(term.span)
                    .add_note("Did you mean a range constraint (`range ...`) or an array or record constraint (`(...)`)? See IEEE 1076-2008 section 6.3.")
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        }
    }

    /// Map a term to an array constraint.
    pub fn term_to_array_constraint(
        &self,
        span: Span,
        terms: Vec<Spanned<Term>>,
        elem: Option<Spanned<Term>>
    ) -> Result<Spanned<hir::ArrayConstraint>> {
        if terms.is_empty() {
            self.emit(
                DiagBuilder2::error(format!("array constraint cannot be empty"))
                .span(span)
            );
            return Err(());
        }
        let indices = if terms.len() == 1 && terms[0].value == Term::Open {
            vec![]
        } else {
            terms.into_iter().map(|e| self.term_to_discrete_range(e)).collect::<Result<Vec<_>>>()?
        };
        let elem = match elem {
            Some(e) => Some(self.term_to_element_constraint(e)?),
            None => None,
        };
        Ok(Spanned::new(hir::ArrayConstraint {
            span: span,
            index: indices,
            elem: elem.map(|e| Box::new(e)),
        }, span))
    }

    /// Map a term to a record constraint.
    pub fn term_to_record_constraint(
        &self,
        span: Span,
        terms: Vec<Spanned<Term>>
    ) -> Result<Spanned<hir::RecordConstraint>> {
        if terms.is_empty() {
            self.emit(
                DiagBuilder2::error(format!("record constraint cannot be empty"))
                .span(span)
            );
            return Err(());
        }
        let mut fields = Vec::new();
        let mut has_fails = false;
        let mut used_names = HashMap::new();
        for term in terms {
            // Make sure that the term is of the form `field (constraint)`.
            let (name, con) = match term.value {
                Term::SuffixParen(name, con) => (name, *con),
                _ => {
                    self.emit(
                        DiagBuilder2::error(format!("`{}` is not a valid constraint for a record element", term.span.extract()))
                        .span(term.span)
                        .add_note("Element constraints must be of the form `name (constraint)`. See IEEE 1076-2008 section 5.3.3.")
                    );
                    debugln!("It is a {:#?}", term.value);
                    has_fails = true;
                    continue;
                }
            };
            let name = match name.value {
                Term::Unresolved(ResolvableName::Ident(i)) => Spanned::new(i, name.span),
                _ => {
                    self.emit(
                        DiagBuilder2::error(format!("`{}` is not a valid record element name", name.span.extract()))
                        .span(name.span)
                    );
                    debugln!("It is a {:#?}", name.value);
                    has_fails = true;
                    continue;
                }
            };

            // Make sure a field is not constrained twice.
            if let Some(&span) = used_names.get(&name.value) {
                self.emit(
                    DiagBuilder2::error(format!("element `{}` has already been constrained", name.value))
                    .span(name.span)
                    .add_note("Previous constraint was here:")
                    .span(span)
                );
                has_fails = true;
                continue;
            } else {
                used_names.insert(name.value, name.span);
            }

            // Parse the constraint.
            fields.push((name, Box::new(self.term_to_element_constraint(con)?)));
        }
        if has_fails {
            return Err(());
        }
        Ok(Spanned::new(hir::RecordConstraint {
            span: span,
            elems: fields,
        }, span))
    }

    /// Map a term to an element constraint.
    pub fn term_to_element_constraint(&self, term: Spanned<Term>) -> Result<Spanned<hir::ElementConstraint>> {
        let con = self.term_to_constraint(term)?;
        Ok(Spanned::new(match con.value {
            hir::Constraint::Array(c) => c.into(),
            hir::Constraint::Record(c) => c.into(),
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid element constraint", con.span.extract()))
                    .span(con.span)
                    .add_note("Did you mean an array or record constraint (`(...)`)? See IEEE 1076-2008 section 6.3.")
                );
                debugln!("It is a {:#?}", con);
                return Err(());
            }
        }, con.span))
    }

    /// Map a term to a discrete range.
    pub fn term_to_discrete_range(&self, term: Spanned<Term>) -> Result<Spanned<hir::DiscreteRange>> {
        let term = self.fold_term_as_type(term)?;
        Ok(match term.value {
            Term::SubtypeInd(..) | Term::TypeMark(..) => {
                let hir = self.term_to_subtype_ind(term)?;
                let add_ctx = AddContext::new(self.ctx, self.scope);
                Spanned::new(add_ctx.add_subtype_ind_hir(hir.value)?.into(), hir.span)
            }
            Term::Range(..) => self.term_to_range(term)?.map_into(),
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid discrete range", term.span.extract()))
                    .span(term.span)
                    .add_note("A discrete range can be one of the following:")
                    .add_note("- a subtype indication of the form `[resolution] type_mark [constraint]`")
                    .add_note("- a range of the form `a to b` or `a downto b`")
                    .add_note("- a range attribute of the form `T'range`")
                    .add_note("See IEEE 1076-2008 section 5.3.2.1.")
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        })
    }

    /// Map a term to a range.
    pub fn term_to_range(&self, term: Spanned<Term>) -> Result<Spanned<hir::Range>> {
        Ok(Spanned::new(match term.value {
            // Term::Attr(..) => ...
            Term::Range(dir, lb, rb) => hir::Range::Immediate(
                dir,
                self.term_to_expr(*lb)?,
                self.term_to_expr(*rb)?
            ),
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid range", term.span.extract()))
                    .span(term.span)
                    .add_note("A range can be one of the following:")
                    .add_note("- an ascending range of the form `a to b`")
                    .add_note("- a descending range of the form `a downto b`")
                    .add_note("- a range attribute of the form `T'range`")
                    .add_note("See IEEE 1076-2008 section 5.2.1.")
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        }, term.span))
    }

    /// Map a term to a definition.
    ///
    /// This works for terms that are actually identifiers.
    pub fn term_to_ident(&self, term: Spanned<Term>) -> Result<Spanned<Def>> {
        Ok(match term.value {
            Term::Unresolved(name) => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is unknown", name))
                    .span(term.span)
                );
                return Err(());
            }
            Term::Ident(def) => def,
            Term::TypeMark(tm) => tm.map_into(),
            Term::Enum(defs) => {
                if defs.len() == 1 {
                    let e = defs.into_iter().next().unwrap();
                    e.map(|e| e.0.into())
                } else {
                    self.emit(
                        DiagBuilder2::error(format!("`{}` is ambiguous", term.span.extract()))
                        .span(term.span)
                    );
                    debugln!("Its definitions are {:#?}", defs);
                    return Err(());
                }
            }
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not an identifier", term.span.extract()))
                    .span(term.span)
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        })
    }

    /// Map a term to a label.
    ///
    /// Returns the statement the label refers to.
    pub fn term_to_label(&self, term: Spanned<Term>) -> Result<Spanned<StmtRef>> {
        let span = term.span;
        let def = self.term_to_ident(term)?;
        Ok(Spanned::new(match def.value {
            Def::Stmt(id) => id,
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a statement label", span.extract()))
                    .span(span)
                    .add_note(format!("`{}` was defined here:", span.extract()))
                    .span(def.span)
                );
                debugln!("The definition is a {:?}", def.value);
                return Err(());
            }
        }, span))
    }

    /// Map a term to a signal.
    pub fn term_to_signal(&self, term: Spanned<Term>) -> Result<Spanned<SignalRef>> {
        let span = term.span;
        let def = self.term_to_ident(term)?;
        Ok(Spanned::new(match def.value {
            Def::Signal(id) => id,
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a signal", span.extract()))
                    .span(span)
                    .add_note(format!("`{}` was defined here:", span.extract()))
                    .span(def.span)
                );
                debugln!("The definition is a {:?}", def.value);
                return Err(());
            }
        }, span))
    }

    /// Map a term to a choice.
    ///
    /// See IEEE 1076-2008 section 9.3.3.1. A choice can be a simple expression,
    /// a discrete range, an identifier, or the keyword `others`.
    pub fn term_to_choice(&self, term: Spanned<Term>) -> Result<Spanned<hir::Choice>> {
        let term_span = term.span;
        Ok(Spanned::new(match term.value {
            Term::Unresolved(ResolvableName::Ident(name)) => hir::Choice::Element(name),
            Term::Others => hir::Choice::Others,
            Term::SubtypeInd(..) |
            Term::TypeMark(..) |
            Term::Range(..) => hir::Choice::DiscreteRange(self.term_to_discrete_range(term)?.value),
            Term::IntLit(..) |
            Term::Unary(..) |
            Term::Binary(..) => hir::Choice::Expr(self.term_to_expr(term)?),
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid choice", term.span.extract()))
                    .span(term.span)
                    .add_note("A choice can be one of the following:")
                    .add_note("- an expression")
                    .add_note("- a discrete range")
                    .add_note("- an element name")
                    .add_note("- the `others` keyword")
                    .add_note("See IEEE 1076-2008 section 9.3.3.1.")
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        }, term_span))
    }

    /// Map a term to an aggregate.
    ///
    /// See IEEE 1076-2008 section 9.3.3.1.
    pub fn term_to_aggregate(&self, term: Spanned<Term>) -> Result<Spanned<AggregateRef>> {
        let fields = match term.value {
            Term::Aggregate(fields) => {
                fields
                    .into_iter()
                    .map(|(choices, expr)|{
                        let choices = choices
                            .into_iter()
                            .map(|choice| self.term_to_choice(choice))
                            .collect::<Vec<Result<_>>>()
                            .into_iter()
                            .collect::<Result<Vec<_>>>();
                        let expr = self.term_to_expr(expr);
                        Ok((choices?, expr?))
                    })
                    .collect::<Vec<Result<_>>>()
                    .into_iter()
                    .collect::<Result<Vec<_>>>()?
            }
            Term::Paren(fields) => {
                fields
                    .into_iter()
                    .map(|expr| Ok((vec![], self.term_to_expr(expr)?)))
                    .collect::<Vec<Result<_>>>()
                    .into_iter()
                    .collect::<Result<Vec<_>>>()?
            }
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid aggregate", term.span.extract()))
                    .span(term.span)
                    .add_note("See IEEE 1076-2008 section 9.3.3.1.")
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        };
        let hir = hir::Aggregate {
            parent: self.scope,
            span: term.span,
            fields: fields,
        };
        let id = AggregateRef::new(NodeId::alloc());
        self.ctx.set_hir(id, self.ctx.sb.arenas.hir.aggregate.alloc(hir));
        Ok(Spanned::new(id, term.span))
    }

    /// Map a term to an association list.
    ///
    /// See IEEE 1076-2008 section 6.5.7.
    pub fn term_to_assoc_list(&self, term: Spanned<Term>) -> Result<Spanned<hir::AssocList>> {
        let term_span = term.span;
        Ok(Spanned::new(match term.value {
            Term::Paren(fields) => fields
                .into_iter()
                .map(|term|{
                    let actual = self.term_to_assoc_actual(term)?;
                    Ok(hir::AssocElement {
                        span: actual.span,
                        formal: None,
                        actual: actual,
                    })
                })
                .collect::<Vec<Result<_>>>()
                .into_iter()
                .collect::<Result<Vec<_>>>()?,
            Term::Aggregate(fields) => fields
                .into_iter()
                .map(|(formal, actual)|{
                    if formal.len() != 1 {
                        self.emit(
                            DiagBuilder2::error("formal part of association element must be exactly one expression")
                            .span(term_span)
                        );
                        return Err(());
                    }
                    let formal = formal.into_iter().next().unwrap();
                    let formal_span = formal.span;
                    let span = Span::union(formal.span, actual.span);
                    let formal = self.term_to_expr(formal)?;
                    let actual = self.term_to_assoc_actual(actual)?;
                    Ok(hir::AssocElement {
                        span: span,
                        formal: Some(Spanned::new(formal, formal_span)),
                        actual: actual,
                    })
                })
                .collect::<Vec<Result<_>>>()
                .into_iter()
                .collect::<Result<Vec<_>>>()?,
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid association list", term.span.extract()))
                    .span(term.span)
                    .add_note("See IEEE 1076-2008 section 6.5.7.")
                );
                debugln!("It is a {:#?}", term);
                return Err(());
            }
        }, term_span))
    }

    /// Map a term to an association actual.
    pub fn term_to_assoc_actual(&self, term: Spanned<Term>) -> Result<Spanned<hir::AssocActual>> {
        let term_span = term.span;
        // TODO: Don't just treat this as an expression, but rather
        // differentiate properly between the different designators.
        let expr = self.term_to_expr(term)?;
        Ok(Spanned::new(hir::AssocActual::Expr(expr), term_span))
    }
}

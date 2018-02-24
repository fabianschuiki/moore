// Copyright (c) 2018 Fabian Schuiki

//! Object declarations
//!
//! This includes constant, signal, variable, shared variable, and file
//! declarations.

#![deny(missing_docs)]

use common::errors::*;
use common::score::Result;
use common::source::Spanned;

use add_ctx::AddContext;
use make_ctx::MakeContext;
use syntax::ast;
use hir;
use score::*;
use term::TermContext;
use ty::*;

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add a constant declaration.
    pub fn add_const_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
        where I: From<ConstDeclRef>
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        let init = self.add_optional(&decl.init, AddContext::add_expr)?;
        self.ctx.set_type_context_optional(init, TypeCtx::TypeOf(ty.into()));
        if let Some(Spanned{span, ..}) = decl.detail {
            self.emit(
                DiagBuilder2::error("expected `:=` or `;`")
                .span(span)
            );
        }
        decl.names.iter().map(|dn|{
            let (mk, id, scope) = self.make::<ConstDeclRef>(dn.span);
            mk.lower_to_hir(Box::new(move |_sbc|{
                Ok(hir::Decl {
                    parent: scope,
                    span: dn.span,
                    name: (*dn).into(),
                    decl: hir::ConstDecl {
                        ty: ty,
                        init: init,
                    }
                })
            }));
            mk.typeval(Box::new(move |tyc|{
                let hir = tyc.ctx.lazy_hir(id)?;
                // TODO: Check that the type of the init expression matches.
                tyc.ctx.lazy_typeval(hir.decl.ty)
            }));
            Ok(mk.finish().into())
        }).collect()
    }

    /// Add a signal declaration.
    pub fn add_signal_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
        where I: From<SignalDeclRef>
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        let init = self.add_optional(&decl.init, AddContext::add_expr)?;
        self.ctx.set_type_context_optional(init, TypeCtx::TypeOf(ty.into()));
        let kind = match decl.detail {
            Some(Spanned{value: ast::ObjDetail::Register, ..}) => hir::SignalKind::Register,
            Some(Spanned{value: ast::ObjDetail::Bus, ..}) => hir::SignalKind::Bus,
            Some(Spanned{span, ..}) => {
                self.emit(
                    DiagBuilder2::error("expected `:=` or `;`")
                    .span(span)
                );
                hir::SignalKind::Normal
            }
            None => hir::SignalKind::Normal,
        };
        decl.names.iter().map(|dn|{
            let (mk, id, scope) = self.make::<SignalDeclRef>(dn.span);
            mk.lower_to_hir(Box::new(move |_sbc|{
                Ok(hir::Decl {
                    parent: scope,
                    span: dn.span,
                    name: (*dn).into(),
                    decl: hir::SignalDecl {
                        ty: ty,
                        kind: kind,
                        init: init,
                    }
                })
            }));
            mk.typeval(Box::new(move |tyc|{
                let hir = tyc.ctx.lazy_hir(id)?;
                // TODO: Check that the type of the init expression matches.
                tyc.ctx.lazy_typeval(hir.decl.ty)
            }));
            Ok(mk.finish().into())
        }).collect()
    }

    /// Add a variable declaration.
    pub fn add_var_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
        where I: From<VarDeclRef>
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        let init = self.add_optional(&decl.init, AddContext::add_expr)?;
        self.ctx.set_type_context_optional(init, TypeCtx::TypeOf(ty.into()));
        if let Some(Spanned{span, ..}) = decl.detail {
            self.emit(
                DiagBuilder2::error("expected `:=` or `;`")
                .span(span)
            );
        }
        decl.names.iter().map(|dn|{
            let (mk, id, scope) = self.make::<VarDeclRef>(dn.span);
            mk.lower_to_hir(Box::new(move |_sbc|{
                Ok(hir::Decl {
                    parent: scope,
                    span: dn.span,
                    name: (*dn).into(),
                    decl: hir::VarDecl {
                        shared: decl.kind == ast::ObjKind::SharedVar,
                        ty: ty,
                        init: init,
                    }
                })
            }));
            mk.typeval(Box::new(move |tyc|{
                let hir = tyc.ctx.lazy_hir(id)?;
                // TODO: Check that the type of the init expression matches.
                tyc.ctx.lazy_typeval(hir.decl.ty)
            }));
            Ok(mk.finish().into())
        }).collect()
    }

    /// Add a file declaration.
    pub fn add_file_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
        where I: From<FileDeclRef>
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        if let Some(ref init) = decl.init {
            self.emit(
                DiagBuilder2::error("expected `;`, `open`, or `is`")
                .span(init.span)
            );
        }
        decl.names.iter().map(|dn|{
            let (mk, id, scope) = self.make::<FileDeclRef>(dn.span);
            mk.lower_to_hir(Box::new(move |sbc|{
                let ctx = AddContext::new(sbc, scope);
                let (mode, filename) = match decl.detail {
                    Some(Spanned{value: ast::ObjDetail::Open(ref mode, ref filename), ..}) => {
                        let mode = ctx.add_optional(mode, AddContext::add_expr)?;
                        let filename = ctx.add_expr(filename)?;
                        (mode, Some(filename))
                    }
                    Some(Spanned{span, ..}) => {
                        sbc.emit(
                            DiagBuilder2::error("expected `;`, `open`, or `is`")
                            .span(span)
                        );
                        (None, None)
                    }
                    None => (None, None),
                };
                Ok(hir::Decl {
                    parent: scope,
                    span: dn.span,
                    name: (*dn).into(),
                    decl: hir::FileDecl {
                        ty: ty,
                        filename: filename,
                        mode: mode,
                    }
                })
            }));
            mk.typeval(Box::new(move |tyc|{
                let hir = tyc.ctx.lazy_hir(id)?;
                // TODO: Check that the type of expressions are okay.
                tyc.ctx.lazy_typeval(hir.decl.ty)
            }));
            Ok(mk.finish().into())
        }).collect()
    }

    /// Add a subtype indication.
    pub fn add_subtype_ind(&self, ind: &'ast ast::SubtypeInd) -> Result<SubtypeIndRef> {
        let (mk, _, scope) = self.make::<SubtypeIndRef>(ind.span);
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = TermContext::new(sbc, scope);
            let term = ctx.termify_subtype_ind(ind)?;
            Ok(ctx.term_to_subtype_ind(term)?.value)
        }));
        self.schedule_subtype_ind(mk);
        Ok(mk.finish())
    }

    /// Add a subtype indication already lowered to HIR.
    pub fn add_subtype_ind_hir(&self, hir: hir::SubtypeInd) -> Result<SubtypeIndRef> {
        let (mk, _, _) = self.make::<SubtypeIndRef>(hir.span);
        mk.set_hir(hir);
        self.schedule_subtype_ind(mk);
        Ok(mk.finish())
    }

    /// Schedule subtype indication tasks.
    pub fn schedule_subtype_ind(&self, mk: MakeContext<SubtypeIndRef>) {
        let id = mk.id;
        mk.typeval(Box::new(move |tyc|{
            let hir = tyc.ctx.lazy_hir(id)?;
            let inner = tyc.ctx.intern_ty(Ty::Named(hir.type_mark.span, hir.type_mark.value));
            match hir.constraint {
                None => Ok(inner),
                Some(Spanned{ value: hir::Constraint::Range(ref con), span }) => {
                    tyc.apply_range_constraint(inner, Spanned::new(con, span))
                }
                Some(Spanned{ value: hir::Constraint::Array(ref ac), span }) => {
                    tyc.apply_array_constraint(inner, Spanned::new(ac, span))
                }
                Some(Spanned{ value: hir::Constraint::Record(ref rc), span }) => {
                    tyc.apply_record_constraint(inner, Spanned::new(rc, span))
                }
            }
        }));
    }
}

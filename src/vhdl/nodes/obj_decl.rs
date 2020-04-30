// Copyright (c) 2016-2020 Fabian Schuiki

//! Object declarations
//!
//! This includes constant, signal, variable, shared variable, and file
//! declarations.

use crate::common::errors::*;
use crate::common::score::Result;
use crate::common::source::Spanned;

use crate::add_ctx::AddContext;
use crate::hir;
use crate::score::*;
use crate::syntax::ast;
use crate::ty::*;

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add a constant declaration.
    pub fn add_const_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
    where
        I: From<ConstDeclRef>,
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        let init = self.add_optional(&decl.init, AddContext::add_expr)?;
        self.ctx
            .set_type_context_optional(init, TypeCtx::TypeOf(ty.into()));
        if let Some(Spanned { span, .. }) = decl.detail {
            self.emit(DiagBuilder2::error("expected `:=` or `;`").span(span));
        }
        decl.names
            .iter()
            .map(|dn| {
                let (mk, id, scope) = self.make::<ConstDeclRef>(dn.span);
                mk.lower_to_hir(Box::new(move |_sbc| {
                    Ok(hir::Decl {
                        parent: scope,
                        span: dn.span,
                        name: (*dn).into(),
                        decl: hir::ConstDecl { ty: ty, init: init },
                    })
                }));
                mk.typeval(Box::new(move |tyc| {
                    let hir = tyc.ctx.lazy_hir(id)?;
                    let ty = tyc.lazy_typeval(hir.decl.ty)?;
                    if let Some(init) = hir.decl.init {
                        let init_ty = tyc.lazy_typeval(init)?;
                        tyc.must_match(ty, init_ty, tyc.ctx.span(init).unwrap());
                    }
                    Ok(ty)
                }));
                Ok(mk.finish().into())
            })
            .collect()
    }

    /// Add a signal declaration.
    pub fn add_signal_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
    where
        I: From<SignalDeclRef>,
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        let init = self.add_optional(&decl.init, AddContext::add_expr)?;
        self.ctx
            .set_type_context_optional(init, TypeCtx::TypeOf(ty.into()));
        let kind = match decl.detail {
            Some(Spanned {
                value: ast::ObjDetail::Register,
                ..
            }) => hir::SignalKind::Register,
            Some(Spanned {
                value: ast::ObjDetail::Bus,
                ..
            }) => hir::SignalKind::Bus,
            Some(Spanned { span, .. }) => {
                self.emit(DiagBuilder2::error("expected `:=` or `;`").span(span));
                hir::SignalKind::Normal
            }
            None => hir::SignalKind::Normal,
        };
        decl.names
            .iter()
            .map(|dn| {
                let (mk, id, scope) = self.make::<SignalDeclRef>(dn.span);
                mk.lower_to_hir(Box::new(move |_sbc| {
                    Ok(hir::Decl {
                        parent: scope,
                        span: dn.span,
                        name: (*dn).into(),
                        decl: hir::SignalDecl {
                            ty: ty,
                            kind: kind,
                            init: init,
                        },
                    })
                }));
                mk.typeval(Box::new(move |tyc| {
                    let hir = tyc.ctx.lazy_hir(id)?;
                    let ty = tyc.lazy_typeval(hir.decl.ty)?;
                    if let Some(init) = hir.decl.init {
                        let init_ty = tyc.lazy_typeval(init)?;
                        tyc.must_match(ty, init_ty, tyc.ctx.span(init).unwrap());
                    }
                    Ok(ty)
                }));
                Ok(mk.finish().into())
            })
            .collect()
    }

    /// Add a variable declaration.
    pub fn add_var_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
    where
        I: From<VarDeclRef>,
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        let init = self.add_optional(&decl.init, AddContext::add_expr)?;
        self.ctx
            .set_type_context_optional(init, TypeCtx::TypeOf(ty.into()));
        if let Some(Spanned { span, .. }) = decl.detail {
            self.emit(DiagBuilder2::error("expected `:=` or `;`").span(span));
        }
        decl.names
            .iter()
            .map(|dn| {
                let (mk, id, scope) = self.make::<VarDeclRef>(dn.span);
                mk.lower_to_hir(Box::new(move |_sbc| {
                    Ok(hir::Decl {
                        parent: scope,
                        span: dn.span,
                        name: (*dn).into(),
                        decl: hir::VarDecl {
                            shared: decl.kind == ast::ObjKind::SharedVar,
                            ty: ty,
                            init: init,
                        },
                    })
                }));
                mk.typeval(Box::new(move |tyc| {
                    let hir = tyc.ctx.lazy_hir(id)?;
                    let ty = tyc.lazy_typeval(hir.decl.ty)?;
                    if let Some(init) = hir.decl.init {
                        let init_ty = tyc.lazy_typeval(init)?;
                        tyc.must_match(ty, init_ty, tyc.ctx.span(init).unwrap());
                    }
                    Ok(ty)
                }));
                Ok(mk.finish().into())
            })
            .collect()
    }

    /// Add a file declaration.
    pub fn add_file_decl<I>(&self, decl: &'ast ast::ObjDecl) -> Result<Vec<I>>
    where
        I: From<FileDeclRef>,
    {
        let ty = self.add_subtype_ind(&decl.subtype)?;
        if let Some(ref init) = decl.init {
            self.emit(DiagBuilder2::error("expected `;`, `open`, or `is`").span(init.span));
        }
        decl.names
            .iter()
            .map(|dn| {
                let (mk, id, scope) = self.make::<FileDeclRef>(dn.span);
                mk.lower_to_hir(Box::new(move |sbc| {
                    let ctx = AddContext::new(sbc, scope);
                    let (mode, filename) = match decl.detail {
                        Some(Spanned {
                            value: ast::ObjDetail::Open(ref mode, ref filename),
                            ..
                        }) => {
                            let mode = ctx.add_optional(mode, AddContext::add_expr)?;
                            let filename = ctx.add_expr(filename)?;
                            (mode, Some(filename))
                        }
                        Some(Spanned { span, .. }) => {
                            sbc.emit(
                                DiagBuilder2::error("expected `;`, `open`, or `is`").span(span),
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
                        },
                    })
                }));
                mk.typeval(Box::new(move |tyc| {
                    let hir = tyc.ctx.lazy_hir(id)?;
                    let ty = tyc.ctx.lazy_typeval(hir.decl.ty)?;
                    // TODO: Check that the type of expressions are okay.
                    let file_ty = tyc.ctx.intern_ty(Ty::File(Box::new(ty.clone())));
                    Ok(file_ty)
                }));
                Ok(mk.finish().into())
            })
            .collect()
    }
}

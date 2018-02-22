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
use syntax::ast;
use hir;
use score::*;

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
                tyc.ctx.ty(hir.decl.ty)
            }));
            Ok(mk.finish().into())
        }).collect()
    }

    /// Add a subtype indication.
    pub fn add_subtype_ind(&self, ind: &'ast ast::SubtypeInd) -> Result<SubtypeIndRef> {
        self.ctx.unpack_subtype_ind(ind, self.scope)
    }
}

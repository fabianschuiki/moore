// Copyright (c) 2018 Fabian Schuiki

//! Type declarations

use common::errors::*;
use common::score::{NodeRef, Result};
use common::source::Spanned;
use common::name::Name;

use num::BigInt;

use add_ctx::AddContext;
use syntax::ast;
use hir;
use score::*;
use term::{Term, TermContext};

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add a type declaration.
    pub fn add_type_decl(&self, decl: &'ast ast::TypeDecl) -> Result<TypeDeclRef> {
        let (mk, id, scope) = self.make(decl.span);
        self.ctx.define(scope, decl.name.map_into(), Def::Type(id))?;
        mk.lower_to_hir(Box::new(move |sbc| {
            let ctx = AddContext::new(sbc, scope);
            Ok(hir::TypeDecl {
                parent: scope,
                name: decl.name,
                data: ctx.add_optional(&decl.data, |ctx, d| ctx.add_type_data(id, decl.name, d))?,
            })
        }));
        mk.typeck(Box::new(move |tyc| {
            let _hir = tyc.ctx.lazy_hir(id)?;
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a type definition.
    pub fn add_type_data(
        &self,
        id: TypeDeclRef,
        name: Spanned<Name>,
        data: &'ast Spanned<ast::TypeData>,
    ) -> Result<Spanned<hir::TypeData>> {
        let td = match data.value {
            // Integer, real, and physical types.
            ast::RangeType(ref range_expr, ref units) => {
                let (dir, lb, rb) = match range_expr.data {
                    ast::BinaryExpr(
                        Spanned {
                            value: ast::BinaryOp::Dir(dir),
                            ..
                        },
                        ref lb_expr,
                        ref rb_expr,
                    ) => {
                        // let ctx = AddContext::new(self, self.scope);
                        let lb = self.add_expr(lb_expr)?;
                        let rb = self.add_expr(rb_expr)?;
                        // let lb = ExprRef::alloc();
                        // let rb = ExprRef::alloc();
                        // self.ctx.set_ast(lb, (self.scope.into(), lb_expr.as_ref()));
                        // self.ctx.set_ast(rb, (self.scope.into(), rb_expr.as_ref()));
                        (dir, lb, rb)
                    }
                    _ => {
                        self.emit(
                            DiagBuilder2::error("Invalid range expression").span(range_expr.span),
                        );
                        return Err(());
                    }
                };
                if let Some(ref units) = *units {
                    // Determine the primary unit.
                    let mut prim_iter = units
                        .iter()
                        .enumerate()
                        .filter(|&(_, &(_, ref expr))| expr.is_none())
                        .map(|(index, &(name, _))| (index, name));
                    let primary = match prim_iter.next() {
                        Some(u) => u,
                        None => {
                            self.emit(
                                DiagBuilder2::error(format!("physical type `{}` has no primary unit", name.value))
                                .span(name.span)
                                .add_note("A physical type must have a primary unit of the form `<name>;`. See IEEE 1076-2008 section 5.2.4.")
                            );
                            return Err(());
                        }
                    };
                    let mut had_fails = false;
                    for (_, n) in prim_iter {
                        self.emit(
                            DiagBuilder2::error(format!("physical type `{}` has multiple primary units", name.value))
                            .span(n.span)
                            .add_note("A physical type cannot have multiple primary units. See IEEE 1076-2008 section 5.2.4.")
                        );
                        had_fails = true;
                    }
                    if had_fails {
                        return Err(());
                    }
                    debugln!("primary unit {:#?}", primary);

                    // Determine the units and how they are defined with respect
                    // to each other.
                    let term_ctx = TermContext::new(self.ctx, self.scope);
                    let table = units
                        .iter()
                        .map(|&(unit_name, ref expr)| {
                            let rel = if let Some(ref expr) = *expr {
                                let term = term_ctx.termify_expr(expr)?;
                                let (value, unit) = match term.value {
                                    Term::PhysLit(value, unit) => (value, unit),
                                    _ => {
                                        self.emit(
                                            DiagBuilder2::error(format!(
                                                "`{}` is not a valid secondary unit",
                                                term.span.extract()
                                            )).span(term.span),
                                        );
                                        debugln!("It is a {:#?}", term.value);
                                        return Err(());
                                    }
                                };
                                if unit.value.unwrap_old().0 != id {
                                    self.emit(
                                        DiagBuilder2::error(format!(
                                            "`{}` is not a unit in the physical type `{}`",
                                            term.span.extract(),
                                            name.value
                                        )).span(term.span)
                                            .add_note(format!(
                                                "`{}` has been declared here:",
                                                term.span.extract()
                                            ))
                                            .span(unit.span),
                                    );
                                }
                                Some((value, unit.value.unwrap_old().1))
                            } else {
                                None
                            };
                            Ok((Spanned::new(unit_name.name, unit_name.span), rel))
                        })
                        .collect::<Vec<Result<_>>>()
                        .into_iter()
                        .collect::<Result<Vec<_>>>()?;

                    // Determine the scale of each unit with respect to the
                    // primary unit.
                    let scale_table = table
                        .iter()
                        .map(|&(name, ref rel)| {
                            let mut abs = BigInt::from(1);
                            let mut rel_to = rel.as_ref();
                            while let Some(&(ref scale, index)) = rel_to {
                                abs = abs * scale;
                                rel_to = table[index].1.as_ref();
                            }
                            (name, abs, rel.clone())
                        })
                        .collect::<Vec<_>>();

                    hir::TypeData::Physical(dir, lb, rb, scale_table, primary.0)
                } else {
                    hir::TypeData::Range(dir, lb, rb)
                }
            }

            // Enumeration types.
            ast::EnumType(ref elems) => {
                let mut lits = Vec::new();
                for elem in &elems.value {
                    // Unpack the element. Make sure it only consists of an
                    // expression that is either an identifier or a character
                    // literal.
                    let lit = if !elem.choices.value.is_empty() {
                        None
                    } else {
                        match elem.expr.data {
                            ast::NameExpr(ast::CompoundName {
                                primary: ast::PrimaryName { kind, span, .. },
                                ref parts,
                                ..
                            }) if parts.is_empty() =>
                            {
                                match kind {
                                    ast::PrimaryNameKind::Ident(n) => {
                                        Some(hir::EnumLit::Ident(Spanned::new(n, span)))
                                    }
                                    ast::PrimaryNameKind::Char(c) => {
                                        Some(hir::EnumLit::Char(Spanned::new(c, span)))
                                    }
                                    _ => None,
                                }
                            }
                            _ => None,
                        }
                    };

                    // If the unpacking was successful, add the literal to the list
                    // of enumeration literals.
                    if let Some(lit) = lit {
                        lits.push(lit);
                    } else {
                        self.emit(
                            DiagBuilder2::error("not an enumeration literal")
                                .span(elem.span)
                                .add_note("expected an identifier or character literal"),
                        );
                        continue;
                    }
                }
                hir::TypeData::Enum(lits)
            }

            ast::AccessType(ref subty) => hir::TypeData::Access(self.add_subtype_ind(subty)?),

            ast::ArrayType(ref indices, ref elem_subty) => {
                // Ensure that we have at least on index, and ensure that there
                // are no stray choices (`expr|expr =>`) in the list. Then map
                // each index into its own node, unpack the element subtype, and
                // we're done.
                assert!(indices.value.len() > 0);
                let indices = self.ctx
                    .sanitize_paren_elems_as_exprs(&indices.value, "an array type index")
                    .into_iter()
                    .map(|index| {
                        let id = ArrayTypeIndexRef::alloc();
                        self.ctx.set_ast(id, (self.scope, index));
                        id
                    })
                    .collect();
                let ctx = TermContext::new(self.ctx, self.scope);
                let subty = ctx.termify_subtype_ind(elem_subty)?;
                let elem_subty = ctx.term_to_subtype_ind(subty)?.value;
                let elem_subty = self.add_subtype_ind_hir(elem_subty)?;
                hir::TypeData::Array(indices, elem_subty)
            }

            ast::FileType(ref name) => {
                let ctx = TermContext::new(self.ctx, self.scope);
                let term = ctx.termify_compound_name(name)?;
                let tm = ctx.term_to_type_mark(term)?;
                hir::TypeData::File(tm)
            }

            ast::RecordType(ref fields) => {
                let fields = fields
                    .iter()
                    .flat_map(|&(ref names, ref subty)| {
                        let subty = self.add_subtype_ind(subty);
                        names
                            .iter()
                            .map(move |name| Ok((Spanned::new(name.name, name.span), subty?)))
                    })
                    .collect::<Result<Vec<_>>>()?;
                hir::TypeData::Record(fields)
            }

            ast::ProtectedType(..) => {
                self.emit(DiagBuilder2::fatal("protected types not implemented").span(name.span));
                return Err(());
            }
        };
        Ok(Spanned::new(td, data.span))
    }
}

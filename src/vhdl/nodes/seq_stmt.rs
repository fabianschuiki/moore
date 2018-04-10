// Copyright (c) 2018 Fabian Schuiki

//! Sequential statements

use std::iter::FromIterator;

use common::errors::*;
use common::util::{HasSpan, HasDesc};
use common::score::Result;
use common::source::Spanned;
use common::name::Name;

use add_ctx::AddContext;
use syntax::ast;
use hir;
use score::*;
use term::TermContext;


impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add multiple sequential statements.
    pub fn add_seq_stmts<I,B>(&self, stmts: I, container_name: &str) -> Result<B>
        where I: IntoIterator<Item=&'ast ast::Stmt>, B: FromIterator<SeqStmtRef>
    {
        let mut had_fails = false;
        let result = {
            let iter = stmts.into_iter().filter_map(|stmt|{
                match self.add_seq_stmt(stmt, container_name) {
                    Ok(i) => Some(i),
                    Err(()) => { had_fails = true; None },
                }
            });
            iter.collect()
        };
        if had_fails {
            Err(())
        } else {
            Ok(result)
        }
    }

    /// Add a sequential statement.
    pub fn add_seq_stmt(&self, stmt: &'ast ast::Stmt, container_name: &str) -> Result<SeqStmtRef> {
        match stmt.data {
            ast::WaitStmt {..} =>
                self.add_wait_stmt(stmt).map(Into::into),
            ast::AssertStmt {..} =>
                self.add_assert_stmt(stmt).map(Into::into),
            ast::ReportStmt {..} =>
                self.add_report_stmt(stmt).map(Into::into),
            ast::AssignStmt {kind: ast::AssignKind::Signal, ..} |
            ast::SelectAssignStmt {kind: ast::AssignKind::Signal, ..} =>
                self.add_sig_assign_stmt(stmt).map(Into::into),
            ast::AssignStmt {kind: ast::AssignKind::Var, ..} |
            ast::SelectAssignStmt {kind: ast::AssignKind::Var, ..} =>
                self.add_var_assign_stmt(stmt).map(Into::into),
            ast::InstOrCallStmt {..} =>
                self.add_call_stmt(stmt).map(Into::into),
            ast::IfStmt {..} =>
                self.add_if_stmt(stmt).map(Into::into),
            ast::CaseStmt {..} =>
                self.add_case_stmt(stmt).map(Into::into),
            ast::LoopStmt {..} =>
                self.add_loop_stmt(stmt).map(Into::into),
            ast::NexitStmt {..} =>
                self.add_nexit_stmt(stmt).map(Into::into),
            ast::ReturnStmt {..} =>
                self.add_return_stmt(stmt).map(Into::into),
            ast::NullStmt =>
                self.add_null_stmt(stmt).map(Into::into),
            ref wrong => {
                self.emit(
                    DiagBuilder2::error(format!("a {} cannot appear in {}", wrong.desc(), container_name))
                    .span(stmt.human_span())
                    .add_note(format!("Only sequential statements are allowed in {}. See IEEE 1076-2008 section 10.", container_name))
                );
                Err(())
            }
        }
    }

    /// Add a wait statement.
    pub fn add_wait_stmt(&self, stmt: &'ast ast::Stmt) -> Result<WaitStmtRef> {
        let (mk, id, scope) = self.make(stmt.span);
        let (on, until, time) = match stmt.data {
            ast::WaitStmt { ref on, ref until, ref time } => (on, until, time),
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let sens = ctx.add_optional(on, |ctx, sens| ctx.add_sensitivity_list(sens.as_ref().map(|s| s.iter())));
            let cond = ctx.add_optional(until, AddContext::add_expr);
            let timeout = ctx.add_optional(time, AddContext::add_expr);
            let (sens, cond, timeout) = (sens?, cond?, timeout?);
            sbc.set_type_context_optional(cond, sbc.builtin_boolean_type());
            sbc.set_type_context_optional(timeout, sbc.builtin_time_type());
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::WaitStmt {
                    sens: sens,
                    cond: cond,
                    timeout: timeout,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let _hir = tyc.ctx.lazy_hir(id)?;
            // hir.stmt.cond.map(|id| tyc.must_match(tyc.ctx.lazy_typeval(id), tyc.ctx.builtin_boolean_type()));
            // hir.stmt.timeout.map(|id| tyc.must_match(tyc.ctx.lazy_typeval(id), tyc.ctx.builtin_time_type()));
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add an assert statement.
    pub fn add_assert_stmt(&self, stmt: &'ast ast::Stmt) -> Result<AssertStmtRef> {
        let (mk, id, scope) = self.make(stmt.span);
        let (cond, report, severity) = match stmt.data {
            ast::AssertStmt { ref cond, ref report, ref severity } => (cond, report, severity),
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let cond = ctx.add_expr(cond);
            let report = ctx.add_optional(report, AddContext::add_expr);
            let severity = ctx.add_optional(severity, AddContext::add_expr);
            let (cond, report, severity) = (cond?, report?, severity?);
            sbc.set_type_context(cond, TypeCtx::Type(sbc.builtin_boolean_type()));
            sbc.set_type_context_optional(report, sbc.builtin_string_type());
            sbc.set_type_context_optional(severity, sbc.builtin_severity_type());
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::AssertStmt {
                    cond: cond,
                    report: report,
                    severity: severity,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let _hir = tyc.ctx.lazy_hir(id)?;
            // tyc.must_match(tyc.ctx.lazy_typeval(hir.stmt.cond), tyc.ctx.builtin_boolean_type());
            // hir.stmt.report.map(|id| tyc.must_match(tyc.ctx.lazy_typeval(id), tyc.ctx.builtin_string_type()));
            // hir.stmt.severity.map(|id| tyc.must_match(tyc.ctx.lazy_typeval(id), tyc.ctx.builtin_severity_type()));
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a report statement.
    pub fn add_report_stmt(&self, stmt: &'ast ast::Stmt) -> Result<ReportStmtRef> {
        let (mk, id, scope) = self.make(stmt.span);
        let (report, severity) = match stmt.data {
            ast::ReportStmt { ref msg, ref severity } => (msg, severity),
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let report = ctx.add_expr(report);
            let severity = ctx.add_optional(severity, AddContext::add_expr);
            let (report, severity) = (report?, severity?);
            sbc.set_type_context(report, sbc.builtin_string_type());
            sbc.set_type_context_optional(severity, sbc.builtin_severity_type());
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::ReportStmt {
                    report: report,
                    severity: severity,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let _hir = tyc.ctx.lazy_hir(id)?;
            // tyc.must_match(tyc.ctx.lazy_typeval(hir.stmt.report), tyc.ctx.builtin_string_type());
            // hir.stmt.severity.map(|id| tyc.must_match(tyc.ctx.lazy_typeval(id), tyc.ctx.builtin_severity_type()));
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a sig_assign statement.
    pub fn add_sig_assign_stmt(&self, stmt: &'ast ast::Stmt) -> Result<SigAssignStmtRef> {
        self.unimp(stmt)
    }

    /// Add a var_assign statement.
    pub fn add_var_assign_stmt(&self, stmt: &'ast ast::Stmt) -> Result<VarAssignStmtRef> {
        let (mk, id, scope) = self.make::<VarAssignStmtRef>(stmt.span);
        enum Kind<'ast> {
            Simple(&'ast ast::Expr),
            Cond(Vec<(&'ast ast::Expr, &'ast ast::Expr)>, Option<&'ast ast::Expr>),
            Sel {
                matching: bool,
                disc: &'ast ast::Expr,
                exprs: Vec<(&'ast ast::Expr, &'ast Spanned<Vec<ast::Expr>>)>,
            },
        };
        let (target, kind) = match stmt.data {
            ast::AssignStmt {
                ref target,
                mode: Spanned {
                    value: ast::AssignMode::Normal(None, ref waves),
                    ..
                },
                ..
            } => (target, match self.unpack_cond_or_uncond_waves(waves)? {
                CondOrUncond::Cond(conds, None) => Kind::Cond(
                    self.unpack_cond_waves_as_exprs(conds)?,
                    None,
                ),
                CondOrUncond::Cond(conds, Some(otherwise)) => Kind::Cond(
                    self.unpack_cond_waves_as_exprs(conds)?,
                    Some(self.unpack_wave_as_expr(otherwise)?),
                ),
                CondOrUncond::Uncond(wave) => Kind::Simple(
                    self.unpack_wave_as_expr(wave)?,
                ),
            }),
            ast::SelectAssignStmt {
                ref select,
                qm,
                ref target,
                mode: ast::SelectAssignMode::Normal(None),
                ref waves,
                ..
            } => (target, Kind::Sel {
                matching: qm,
                disc: select,
                exprs: self.unpack_sel_waves_as_exprs(waves)?
            }),
            _ => {
                self.emit(
                    DiagBuilder2::error(format!("invalid variable assignment"))
                    .span(stmt.span)
                );
                return Err(());
            }
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let target = ctx.add_target(target);
            let kind = match kind {
                Kind::Simple(expr) => {
                    let expr = ctx.add_expr(expr);
                    hir::VarAssignKind::Simple(expr?)
                },
                Kind::Cond(ref conds, ref otherwise) => {
                    let conds = conds.into_iter()
                        .map(|&(e,c)|{
                            let e = ctx.add_expr(e);
                            let c = ctx.add_expr(c);
                            Ok((e?, c?))
                        })
                        .collect::<Vec<Result<_>>>()
                        .into_iter()
                        .collect::<Result<Vec<_>>>();
                    let otherwise = match *otherwise {
                        Some(o) => Some(ctx.add_expr(o)?),
                        None => None,
                    };
                    hir::VarAssignKind::Cond(hir::Cond{
                        when: conds?,
                        other: otherwise,
                    })
                },
                Kind::Sel { matching, ref disc, ref exprs } => {
                    let disc = ctx.add_expr(disc);
                    let exprs = exprs.into_iter()
                        .map(|&(e, ref c)|{
                            let e = ctx.add_expr(e);
                            let c = ctx.add_choices(c.as_ref().map(|i| i.iter()));
                            Ok((e?, c?))
                        })
                        .collect::<Vec<Result<_>>>()
                        .into_iter()
                        .collect::<Result<Vec<_>>>();
                    hir::VarAssignKind::Sel(hir::Sel{
                        matching: matching,
                        disc: disc?,
                        when: exprs?,
                    })
                }
            };
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::VarAssignStmt {
                    target: target?,
                    kind: kind,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let _hir = tyc.ctx.lazy_hir(id)?;
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a call statement.
    pub fn add_call_stmt(&self, stmt: &'ast ast::Stmt) -> Result<CallStmtRef> {
        self.unimp(stmt)
    }

    /// Add an if statement.
    pub fn add_if_stmt(&self, stmt: &'ast ast::Stmt) -> Result<IfStmtRef> {
        let (mk, id, scope) = self.make::<IfStmtRef>(stmt.span);
        let (branches, otherwise) = match stmt.data {
            ast::IfStmt { ref conds, ref alt } => (conds, alt),
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let branches = branches.iter().map(|&(ref expr, ref body)|
                Ok((ctx.add_expr(expr)?, ctx.add_seq_stmts(&body.stmts, "an if branch")?))
            ).collect::<Result<Vec<_>>>();
            let otherwise = ctx.add_optional(otherwise, |ctx, ast| ctx.add_seq_stmts(&ast.stmts, "an if branch"));
            let (branches, otherwise) = (branches?, otherwise?);
            for &(cond, _) in &branches {
                sbc.set_type_context(cond, sbc.builtin_boolean_type());
            }
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::IfStmt {
                    branches: branches,
                    otherwise: otherwise,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let hir = tyc.ctx.lazy_hir(id)?;
            for &(_cond, _) in &hir.stmt.branches {
                // tyc.must_match(tyc.lazy_typeval(cond), tyc.ctx.builtin_boolean_type());
            }
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a case statement.
    pub fn add_case_stmt(&self, stmt: &'ast ast::Stmt) -> Result<CaseStmtRef> {
        let (mk, id, scope) = self.make::<CaseStmtRef>(stmt.span);
        let (matching, switch, cases) = match stmt.data {
            ast::CaseStmt { qm, ref switch, ref cases } => (qm, switch, cases),
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let switch = ctx.add_expr(switch);
            let cases = cases.iter().map(|&(ref choices, ref body)|{
                let choices = ctx.add_choices(choices.as_ref().map(|c| c.iter()));
                let stmts = ctx.add_seq_stmts(&body.stmts, "a case branch");
                Ok((choices?, stmts?))
            }).collect::<Vec<Result<_>>>().into_iter().collect::<Result<Vec<_>>>();
            // The above trick of calling collect() twice achieves the
            // following: On the first pass, the results are collected into a
            // vector. This ensures that diagnostics for all cases are emitted.
            // Then we re-collect the vector, but this time into a result, which
            // will stop at the first `Err`.
            let (switch, cases) = (switch?, cases?);
            for &(ref _choices, _) in &cases {
                // TODO: Set the type context for each choice.
                // for choice in choices {
                //     sbc.set_type_context(choice, switch);
                // }
            }
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::CaseStmt {
                    matching: matching,
                    switch: switch,
                    cases: cases,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let hir = tyc.ctx.lazy_hir(id)?;
            let _switch_ty = tyc.lazy_typeval(hir.stmt.switch)?;
            for &(ref _choices, ref stmts) in &hir.stmt.cases {
                // tyc.typeck_choices(choices, switch_ty);
                tyc.typeck_slice(stmts);
            }
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a while loop statement.
    #[allow(unused_variables)]
    pub fn add_loop_stmt(&self, stmt: &'ast ast::Stmt) -> Result<LoopStmtRef> {
        let (mk, id, scope) = self.make::<LoopStmtRef>(stmt.span);
        let (scheme, body) = match stmt.data {
            ast::LoopStmt { ref scheme, ref body } => (scheme, body),
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            // TODO: Make a subscope here! No clue how...
            let ctx = AddContext::new(sbc, scope);
            let scheme = (|| match *scheme {
                ast::LoopScheme::Loop =>
                    Ok(hir::LoopScheme::Loop),
                ast::LoopScheme::While(ref cond) =>
                    Ok(hir::LoopScheme::While(ctx.add_expr(cond)?)),
                ast::LoopScheme::For(name, ref range) =>
                    Ok(hir::LoopScheme::For(name.into(), ctx.add_discrete_range(range)?)),
            })();
            let stmts = ctx.add_seq_stmts(&body.stmts, "a loop body");
            let (scheme, stmts) = (scheme?, stmts?);
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::LoopStmt {
                    scheme: scheme,
                    stmts: stmts,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let hir = tyc.ctx.lazy_hir(id)?;
            // TODO: Check the types of the loop scheme.
            tyc.typeck_slice(&hir.stmt.stmts);
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a next statement.
    pub fn add_nexit_stmt(&self, stmt: &'ast ast::Stmt) -> Result<NexitStmtRef> {
        let (mk, id, scope) = self.make::<NexitStmtRef>(stmt.span);
        let (mode, target, cond) = match stmt.data {
            ast::NexitStmt { mode, ref target, ref cond } => (mode, target, cond),
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let mode = match mode {
                ast::NexitMode::Next => hir::NexitMode::Next,
                ast::NexitMode::Exit => hir::NexitMode::Exit,
            };
            let target = ctx.add_optional(target, AddContext::add_label);
            let cond = ctx.add_optional(cond, AddContext::add_expr);
            let (target, cond) = (target?, cond?);
            let target = match target {
                Some(Spanned{ value: StmtRef::Seq(SeqStmtRef::Loop(id)), span }) => Some(Spanned::new(id, span)),
                Some(Spanned{ span, .. }) => {
                    sbc.emit(
                        DiagBuilder2::error(format!("`{}` is not a loop", span.extract()))
                        .span(span)
                    );
                    return Err(());
                },
                None => None
            };
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::NexitStmt {
                    mode: mode,
                    target: target,
                    cond: cond,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let _hir = tyc.ctx.lazy_hir(id)?;
            // tyc.must_match(tyc.lazy_typeval(hir.stmt.cond), tyc.ctx.builtin_boolean_type());
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a return statement.
    pub fn add_return_stmt(&self, stmt: &'ast ast::Stmt) -> Result<ReturnStmtRef> {
        let (mk, id, scope) = self.make::<ReturnStmtRef>(stmt.span);
        let expr = match stmt.data {
            ast::ReturnStmt(ref expr) => expr,
            _ => unreachable!(),
        };
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = AddContext::new(sbc, scope);
            let expr = ctx.add_optional(expr, AddContext::add_expr)?;
            // TODO: Set a type context for the expression based on the outer
            // function signature.
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::ReturnStmt {
                    expr: expr,
                }
            })
        }));
        mk.typeck(Box::new(move |tyc|{
            let _hir = tyc.ctx.lazy_hir(id)?;
            // TODO: Check the type of the expression.
            Ok(())
        }));
        Ok(mk.finish())
    }

    /// Add a null statement.
    pub fn add_null_stmt(&self, stmt: &'ast ast::Stmt) -> Result<NullStmtRef> {
        let (mk, _id, scope) = self.make::<NullStmtRef>(stmt.span);
        mk.lower_to_hir(Box::new(move |_|{
            Ok(hir::Stmt {
                parent: scope,
                span: stmt.span,
                label: stmt.label,
                stmt: hir::NullStmt,
            })
        }));
        mk.typeck(Box::new(|_| Ok(())));
        Ok(mk.finish())
    }

    /// Add a sensitivity list.
    pub fn add_sensitivity_list<I>(
        &self,
        ast: Spanned<I>,
    ) -> Result<Spanned<hir::SensitivityList>>
        where I: IntoIterator<Item=&'ast ast::CompoundName>
    {
        let ctx = TermContext::new(self.ctx, self.scope);
        let signals = ast.value
            .into_iter()
            .map(|ast|{
                let term = ctx.termify_compound_name(ast)?;
                ctx.term_to_signal(term)
            })
            .collect::<Vec<Result<_>>>()
            .into_iter()
            .collect::<Result<Vec<_>>>()?;
        Ok(Spanned::new(signals, ast.span))
    }

    /// Add a label.
    ///
    /// Immediately resolves the label name and returns the corresponding
    /// statement.
    pub fn add_label(&self, ast: &'ast Spanned<Name>) -> Result<Spanned<StmtRef>> {
        let ctx = TermContext::new(self.ctx, self.scope);
        let term = ctx.termify_name(ast.map_into())?;
        ctx.term_to_label(term)
    }

    /// Add a target variable.
    ///
    /// This is an target for a variable assignment.
    pub fn add_target(&self, ast: &'ast Spanned<ast::AssignTarget>) -> Result<Spanned<hir::Target>> {
        let ctx = TermContext::new(self.ctx, self.scope);
        Ok(Spanned::new(match ast.value {
            ast::AssignTarget::Name(ref name) => {
                let term = ctx.termify_compound_name(name)?;
                hir::Target::Name(ctx.term_to_expr(term)?)
            }
            ast::AssignTarget::Aggregate(ref agg) => {
                let term = ctx.termify_paren_elems(agg)?;
                hir::Target::Aggregate(ctx.term_to_aggregate(term)?.value)
            }
        }, ast.span))
    }

    /// Unpack a slice of waves.
    ///
    /// Ensures that either the waves are all unconditional, or all have a
    /// condition except for the optional last one.
    fn unpack_cond_or_uncond_waves(&self, ast: &'ast [ast::CondWave]) -> Result<CondOrUncond<'ast>> {
        assert!(!ast.is_empty());
        let any_cond = ast.iter().any(|w| w.1.is_some());
        if any_cond {
            // Cut away the optional trailing else without condition.
            let (slice, otherwise) = match *ast.last().unwrap() {
                ast::CondWave(ref wave, None) => (&ast[..ast.len()-2], Some(wave)),
                _ => (&ast[..], None),
            };
            let conds = slice
                .into_iter()
                .map(|&ast::CondWave(ref wave, ref cond)|{
                    match *cond {
                        Some(ref cond) => Ok((wave, cond)),
                        None => {
                            self.emit(
                                DiagBuilder2::error(format!("`{}` missing a `when` condition", wave.span.extract()))
                                .span(wave.span)
                                .add_note("Either all or none of the waveforms or expressions in the assignment can have a `when` condition.")
                            );
                            Err(())
                        }
                    }
                })
                .collect::<Vec<Result<_>>>()
                .into_iter()
                .collect::<Result<Vec<_>>>()?;
            Ok(CondOrUncond::Cond(conds, otherwise))
        } else {
            if ast.len() != 1 {
                self.emit(
                    DiagBuilder2::error(format!("more than one waveform or expression"))
                    .span(ast[0].0.span)
                    .add_note("An unconditional assignment must have exactly one waveform or expression.")
                );
                Err(())
            } else {
                Ok(CondOrUncond::Uncond(&ast[0].0))
            }
        }
    }

    /// Unpack a sequence of conditional waves as expressions.
    fn unpack_cond_waves_as_exprs<I>(&self, ast: I) -> Result<Vec<(&'ast ast::Expr, &'ast ast::Expr)>>
        where I: IntoIterator<Item=(&'ast ast::Wave, &'ast ast::Expr)>
    {
        ast.into_iter().map(|(w,c)| Ok((self.unpack_wave_as_expr(w)?, c)))
            .collect::<Vec<Result<_>>>()
            .into_iter()
            .collect::<Result<Vec<_>>>()
    }

    /// Unpack a wave as expression.
    ///
    /// This is useful for variable assignments to ensure that the right hand
    /// side is not a signal waveform.
    fn unpack_wave_as_expr(&self, ast: &'ast ast::Wave) -> Result<&'ast ast::Expr> {
        if let Some(ref v) = ast.elems {
            if v.len() == 1 && v[0].1.is_none() {
                return Ok(&v[0].0);
            }
        }
        self.emit(
            DiagBuilder2::error(format!("`{}` is not a valid expression", ast.span.extract()))
            .span(ast.span)
        );
        Err(())
    }

    /// Unpack a sequence of selected waves as expressions.
    fn unpack_sel_waves_as_exprs<I>(&self, ast: I) -> Result<Vec<(&'ast ast::Expr, &'ast Spanned<Vec<ast::Expr>>)>>
        where I: IntoIterator<Item=&'ast ast::SelectWave>
    {
        ast.into_iter().map(|sw| Ok((self.unpack_wave_as_expr(&sw.0)?, &sw.1)))
            .collect::<Vec<Result<_>>>()
            .into_iter()
            .collect::<Result<Vec<_>>>()
    }
}

/// A conditional or unconditional slice of waves.
///
/// These are used for signal and variable assignments. Note that for variables
/// further checking needs to be performed to ensure that the wave is actually
/// just an expression.
enum CondOrUncond<'ast> {
    /// A conditional slice of waves. Consists of wave-condition pairs, and an
    /// optional unconditional wave.
    Cond(Vec<(&'ast ast::Wave, &'ast ast::Expr)>, Option<&'ast ast::Wave>),
    /// An unconditional wave.
    Uncond(&'ast ast::Wave),
}

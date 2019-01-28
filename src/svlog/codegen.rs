// Copyright (c) 2016-2019 Fabian Schuiki

//! This module implements LLHD code generation.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{Type, TypeKind},
    value::{Value, ValueKind},
    ParamEnv, ParamEnvSource,
};
use llhd::Context as LlhdContext;
use num::Zero;
use std::{collections::HashMap, ops::Deref};

/// A code generator.
///
/// Use this struct to emit LLHD code for nodes in a [`Context`].
pub struct CodeGenerator<'gcx, C> {
    /// The compilation context.
    cx: C,
    /// The LLHD module to be populated.
    into: llhd::Module,
    /// Tables holding mappings and interned values.
    tables: Tables<'gcx>,
}

impl<'gcx, C> CodeGenerator<'gcx, C> {
    /// Create a new code generator.
    pub fn new(cx: C) -> Self {
        CodeGenerator {
            cx,
            into: llhd::Module::new(),
            tables: Default::default(),
        }
    }

    /// Finalize code generation and return the generated LLHD module.
    pub fn finalize(self) -> llhd::Module {
        self.into
    }
}

#[derive(Default)]
struct Tables<'gcx> {
    module_defs: HashMap<NodeEnvId, Result<llhd::EntityRef>>,
    module_types: HashMap<NodeEnvId, llhd::Type>,
    interned_types: HashMap<Type<'gcx>, Result<llhd::Type>>,
    interned_values: HashMap<Value<'gcx>, Result<llhd::Const>>,
}

impl<'gcx, C> Deref for CodeGenerator<'gcx, C> {
    type Target = C;

    fn deref(&self) -> &C {
        &self.cx
    }
}

impl<'a, 'gcx, C: Context<'gcx>> CodeGenerator<'gcx, &'a C> {
    /// Emit the code for a module and all its dependent modules.
    pub fn emit_module(&mut self, id: NodeId) -> Result<llhd::EntityRef> {
        self.emit_module_with_env(id, self.default_param_env())
    }

    /// Emit the code for a module and all its dependent modules.
    pub fn emit_module_with_env(&mut self, id: NodeId, env: ParamEnv) -> Result<llhd::EntityRef> {
        if let Some(x) = self.tables.module_defs.get(&(id, env)) {
            return x.clone();
        }
        let hir = match self.hir_of(id)? {
            HirNode::Module(m) => m,
            _ => panic!("expected {:?} to be a module", id),
        };
        debug!("emit module `{}` with {:?}", hir.name, env);

        // Determine entity type and port names.
        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        let mut input_tys = Vec::new();
        let mut output_tys = Vec::new();
        let mut port_id_to_name = HashMap::new();
        for &port_id in hir.ports {
            let port = match self.hir_of(port_id)? {
                HirNode::Port(p) => p,
                _ => unreachable!(),
            };
            let ty = self.type_of(port_id, env)?;
            debug!(
                "port {}.{} has type {:?}",
                hir.name.value, port.name.value, ty
            );
            let ty = self.emit_type(ty)?;
            let ty = match port.dir {
                ast::PortDir::Ref => llhd::pointer_ty(ty),
                _ => llhd::signal_ty(ty),
            };
            match port.dir {
                ast::PortDir::Input | ast::PortDir::Ref => {
                    input_tys.push(ty);
                    inputs.push(port_id);
                }
                ast::PortDir::Output => {
                    output_tys.push(ty);
                    outputs.push(port_id);
                }
                ast::PortDir::Inout => {
                    input_tys.push(ty.clone());
                    output_tys.push(ty);
                    inputs.push(port_id);
                    outputs.push(port_id);
                }
            }
            port_id_to_name.insert(port_id, port.name);
        }

        // Pick an entity name.
        let mut entity_name: String = hir.name.value.into();
        if env != self.default_param_env() {
            entity_name.push_str(&format!(".param{}", env.0));
        }

        // Create entity.
        let ty = llhd::entity_ty(input_tys, output_tys.clone());
        let mut ent = llhd::Entity::new(entity_name, ty.clone());
        self.tables.module_types.insert((id, env), ty);

        // Assign proper port names and collect ports into a lookup table.
        let mut values = HashMap::<NodeId, llhd::ValueRef>::new();
        for (index, port_id) in inputs.into_iter().enumerate() {
            ent.inputs_mut()[index].set_name(port_id_to_name[&port_id].value);
            values.insert(port_id, ent.input(index).into());
        }
        for (index, &port_id) in outputs.iter().enumerate() {
            ent.outputs_mut()[index].set_name(port_id_to_name[&port_id].value);
            values.insert(port_id, ent.output(index).into());
        }

        self.emit_module_block(id, env, &hir.block, &mut ent, &mut values)?;

        // Assign default values to undriven output ports.
        for port_id in outputs {
            let driven = {
                let value = &values[&port_id];
                ent.insts().any(|inst| match inst.kind() {
                    llhd::DriveInst(target, ..) => target == value,
                    llhd::InstanceInst(_, _, _, ref driven) => driven.contains(value),
                    _ => false,
                })
            };
            if driven {
                continue;
            }
            let hir = match self.hir_of(port_id)? {
                HirNode::Port(p) => p,
                _ => unreachable!(),
            };
            let default_value = self.emit_const(if let Some(default) = hir.default {
                self.constant_value_of(default, env)?
            } else {
                self.type_default_value(self.type_of(port_id, env)?)
            })?;
            let inst = llhd::Inst::new(
                None,
                llhd::DriveInst(values[&port_id].clone(), default_value.into(), None),
            );
            ent.add_inst(inst, llhd::InstPosition::End);
        }

        let result = Ok(self.into.add_entity(ent));
        self.tables.module_defs.insert((id, env), result.clone());
        result
    }

    /// Emit the code for the contents of a module.
    pub fn emit_module_block(
        &mut self,
        id: NodeId,
        env: ParamEnv,
        hir: &hir::ModuleBlock,
        ent: &mut llhd::Entity,
        values: &mut HashMap<NodeId, llhd::ValueRef>,
    ) -> Result<()> {
        // Emit declarations.
        for &decl_id in &hir.decls {
            let hir = match self.hir_of(decl_id)? {
                HirNode::VarDecl(x) => x,
                _ => unreachable!(),
            };
            let ty = self.emit_type(self.type_of(decl_id, env)?)?;
            let init = match hir.init {
                Some(expr) => Some(self.emit_const(self.constant_value_of(expr, env)?)?.into()),
                None => None,
            };
            let inst = llhd::Inst::new(Some(hir.name.value.into()), llhd::SignalInst(ty, init));
            let id = ent.add_inst(inst, llhd::InstPosition::End);
            values.insert(decl_id, id.into());
        }

        // Emit instantiations.
        for &inst_id in &hir.insts {
            let hir = match self.hir_of(inst_id)? {
                HirNode::Inst(x) => x,
                _ => unreachable!(),
            };
            let target_hir = match self.hir_of(hir.target)? {
                HirNode::InstTarget(x) => x,
                _ => unreachable!(),
            };
            let resolved = match self.gcx().find_module(target_hir.name.value) {
                Some(id) => id,
                None => {
                    self.emit(
                        DiagBuilder2::error(format!(
                            "unknown module or interface `{}`",
                            target_hir.name.value
                        ))
                        .span(target_hir.name.span),
                    );
                    return Err(());
                }
            };
            let inst_env = self.param_env(ParamEnvSource::ModuleInst {
                module: resolved,
                inst: inst_id,
                env,
                pos: &target_hir.pos_params,
                named: &target_hir.named_params,
            })?;
            trace!("{:?} = {:#?}", inst_env, self.param_env_data(inst_env));
            trace!("pos_ports = {:#?}", hir.pos_ports);
            trace!("named_ports = {:#?}", hir.named_ports);
            trace!("has_wildcard_port = {:#?}", hir.has_wildcard_port);
            // let port_mapping = self.port_mapping(PortMappingSource::ModuleInst {
            //     module: resolved,
            //     inst: inst_id,
            //     env: inst_env,
            //     pos: &target_hir.pos_ports,
            //     named: &target_hir.named_ports,
            // })?;
            let target = self.emit_module_with_env(resolved, inst_env)?;
            let ty = self.tables.module_types[&(resolved, inst_env)].clone();
            let inst = llhd::Inst::new(
                Some(hir.name.value.into()),
                llhd::InstanceInst(ty, target.into(), vec![], vec![]),
            );
            ent.add_inst(inst, llhd::InstPosition::End);
        }

        // Emit generate blocks.
        for &gen_id in &hir.gens {
            let hir = match self.hir_of(gen_id)? {
                HirNode::Gen(x) => x,
                _ => unreachable!(),
            };
            #[allow(unreachable_patterns)]
            match hir.kind {
                hir::GenKind::If {
                    cond,
                    ref main_body,
                    ref else_body,
                } => {
                    let k = self.constant_value_of(cond, env)?;
                    if k.is_false() {
                        if let Some(else_body) = else_body {
                            self.emit_module_block(id, env, else_body, ent, values)?;
                        }
                    } else {
                        self.emit_module_block(id, env, main_body, ent, values)?;
                    }
                }
                hir::GenKind::For {
                    ref init,
                    cond,
                    step,
                    ref body,
                } => {
                    let mut local_env = env;
                    for &i in init {
                        local_env = self.execute_genvar_init(i, local_env)?;
                    }
                    while self.constant_value_of(cond, local_env)?.is_true() {
                        self.emit_module_block(id, local_env, body, ent, values)?;
                        local_env = self.execute_genvar_step(step, local_env)?;
                    }
                }
                _ => return self.unimp_msg("code generation for", hir),
            }
        }

        // Emit and instantiate procedures.
        for &proc_id in &hir.procs {
            use llhd::Context as LlhdContext;
            let prok = self.emit_procedure(proc_id, env)?;
            let ty = llhd::ModuleContext::new(&self.into)
                .ty(&prok.into())
                .clone();
            let acc = self.accessed_nodes(proc_id)?;
            let inputs = acc.read.iter().map(|id| values[id].clone()).collect();
            let outputs = acc.written.iter().map(|id| values[id].clone()).collect();
            let inst = llhd::Inst::new(None, llhd::InstanceInst(ty, prok.into(), inputs, outputs));
            ent.add_inst(inst, llhd::InstPosition::End);
        }

        Ok(())
    }

    /// Emit the code for a procedure.
    fn emit_procedure(&mut self, id: NodeId, env: ParamEnv) -> Result<llhd::ProcessRef> {
        let hir = match self.hir_of(id)? {
            HirNode::Proc(x) => x,
            _ => unreachable!(),
        };

        // Find the accessed nodes.
        let acc = self.accessed_nodes(hir.stmt)?;
        trace!("process accesses {:#?}", acc);
        let mut inputs = vec![];
        let mut outputs = vec![];
        for &id in &acc.read {
            inputs.push((id, llhd::signal_ty(self.emit_type(self.type_of(id, env)?)?)));
        }
        for &id in &acc.written {
            outputs.push((id, llhd::signal_ty(self.emit_type(self.type_of(id, env)?)?)));
        }
        trace!("process inputs = {:#?}", inputs);
        trace!("process outputs = {:#?}", outputs);

        // Create process and entry block.
        let mut prok = llhd::Process::new(
            format!("{:?}", id),
            llhd::entity_ty(
                inputs.iter().map(|(_, ty)| ty.clone()).collect(),
                outputs.iter().map(|(_, ty)| ty.clone()).collect(),
            ),
        );
        let entry_blk = prok
            .body_mut()
            .add_block(llhd::Block::new(None), llhd::BlockPosition::Begin);

        // Create a mapping from read/written nodes to process parameters and
        // emit statements.
        let mut values = HashMap::new();
        for (&(id, _), arg) in inputs
            .iter()
            .zip(prok.inputs())
            .chain(outputs.iter().zip(prok.outputs()))
        {
            values.insert(id, arg.as_ref().into());
        }
        let final_blk = self.emit_stmt(hir.stmt, env, &mut prok, entry_blk, &mut values)?;

        // Emit epilogue.
        match hir.kind {
            ast::ProcedureKind::Initial => {
                prok.body_mut().add_inst(
                    llhd::Inst::new(None, llhd::HaltInst),
                    llhd::InstPosition::BlockEnd(final_blk),
                );
            }
            ast::ProcedureKind::Always
            | ast::ProcedureKind::AlwaysComb
            | ast::ProcedureKind::AlwaysLatch
            | ast::ProcedureKind::AlwaysFf => {
                prok.body_mut().add_inst(
                    llhd::Inst::new(None, llhd::BranchInst(llhd::BranchKind::Uncond(entry_blk))),
                    llhd::InstPosition::BlockEnd(final_blk),
                );
            }
            _ => (),
        }
        Ok(self.into.add_process(prok))
    }

    /// Map a type to an LLHD type (interned).
    fn emit_type(&mut self, ty: Type<'gcx>) -> Result<llhd::Type> {
        if let Some(x) = self.tables.interned_types.get(ty) {
            x.clone()
        } else {
            let x = self.emit_type_uninterned(ty);
            self.tables.interned_types.insert(ty, x.clone());
            x
        }
    }

    /// Map a type to an LLHD type.
    fn emit_type_uninterned(&mut self, ty: Type<'gcx>) -> Result<llhd::Type> {
        #[allow(unreachable_patterns)]
        Ok(match *ty {
            TypeKind::Void => llhd::void_ty(),
            TypeKind::Bit(_) => llhd::int_ty(1),
            TypeKind::Int(width, _) => llhd::int_ty(width),
            TypeKind::Named(_, _, ty) => self.emit_type(ty)?,
            _ => unimplemented!(),
        })
    }

    /// Map a value to an LLHD constant (interned).
    fn emit_const(&mut self, value: Value<'gcx>) -> Result<llhd::Const> {
        if let Some(x) = self.tables.interned_values.get(value) {
            x.clone()
        } else {
            let x = self.emit_const_uninterned(value);
            self.tables.interned_values.insert(value, x.clone());
            x
        }
    }

    /// Map a value to an LLHD constant.
    fn emit_const_uninterned(&mut self, value: Value<'gcx>) -> Result<llhd::Const> {
        match (value.ty, &value.kind) {
            (&TypeKind::Int(width, _), &ValueKind::Int(ref k)) => {
                Ok(llhd::const_int(width, k.clone()))
            }
            (&TypeKind::Time, &ValueKind::Time(ref k)) => {
                Ok(llhd::const_time(k.clone(), Zero::zero(), Zero::zero()))
            }
            (&TypeKind::Bit(_), &ValueKind::Int(ref k)) => Ok(llhd::const_int(1, k.clone())),
            _ => panic!("invalid type/value combination {:#?}", value),
        }
    }

    /// Emit the code for a statement.
    fn emit_stmt(
        &mut self,
        stmt_id: NodeId,
        env: ParamEnv,
        prok: &mut llhd::Process,
        mut block: llhd::BlockRef,
        values: &mut HashMap<NodeId, llhd::ValueRef>,
    ) -> Result<llhd::BlockRef> {
        let hir = match self.hir_of(stmt_id)? {
            HirNode::Stmt(x) => x,
            _ => unreachable!(),
        };
        #[allow(unreachable_patterns)]
        match hir.kind {
            hir::StmtKind::Null => (),
            hir::StmtKind::Block(ref ids) => {
                for &id in ids {
                    block = self.emit_stmt(id, env, prok, block, values)?;
                }
            }
            hir::StmtKind::Assign { lhs, rhs, kind } => {
                let rhs_value = self.emit_rvalue(rhs, env, prok, block, values)?;
                match kind {
                    hir::AssignKind::Block(ast::AssignOp::Identity) => {
                        self.emit_blocking_assign(lhs, rhs_value, env, prok, block, values)?;
                    }
                    _ => {
                        return self
                            .unimp_msg(format!("code generation for assignment {:?} in", kind), hir)
                    }
                }
            }
            hir::StmtKind::Timed {
                control: hir::TimingControl::Delay(expr_id),
                stmt,
            } => {
                let resume_blk = prok
                    .body_mut()
                    .add_block(llhd::Block::new(None), llhd::BlockPosition::End);
                let duration = self.emit_rvalue(expr_id, env, prok, block, values)?.into();
                prok.body_mut().add_inst(
                    llhd::Inst::new(None, llhd::WaitInst(resume_blk, Some(duration), vec![])),
                    llhd::InstPosition::BlockEnd(block),
                );
                block = self.emit_stmt(stmt, env, prok, resume_blk, values)?;
            }
            hir::StmtKind::Timed {
                control: hir::TimingControl::ExplicitEvent(expr_id),
                stmt,
            } => {
                let expr_hir = match self.hir_of(expr_id)? {
                    HirNode::EventExpr(x) => x,
                    _ => unreachable!(),
                };
                trace!("would now emit event checking code for {:#?}", expr_hir);

                // Store initial values of the expressions the event is
                // sensitive to.
                let init_blk = prok.body_mut().add_block(
                    llhd::Block::new(Some("init".into())),
                    llhd::BlockPosition::End,
                );
                prok.body_mut().add_inst(
                    llhd::Inst::new(
                        None,
                        llhd::BranchInst(llhd::BranchKind::Uncond(init_blk.into())),
                    ),
                    llhd::InstPosition::BlockEnd(block),
                );
                let mut init_values = vec![];
                for event in &expr_hir.events {
                    init_values.push(self.emit_rvalue(event.expr, env, prok, init_blk, values)?);
                }

                // Wait for any of the inputs to those expressions to change.
                let check_blk = prok.body_mut().add_block(
                    llhd::Block::new(Some("check".into())),
                    llhd::BlockPosition::End,
                );
                let mut trigger_on = vec![];
                for event in &expr_hir.events {
                    let acc = self.accessed_nodes(event.expr)?;
                    for id in &acc.read {
                        trigger_on.push(values[&id].clone());
                    }
                }
                prok.body_mut().add_inst(
                    llhd::Inst::new(None, llhd::WaitInst(check_blk, None, trigger_on)),
                    llhd::InstPosition::BlockEnd(init_blk),
                );

                // Check if any of the events happened and produce a single bit
                // value that represents this.
                let mut event_cond = None;
                for (event, init_value) in expr_hir.events.iter().zip(init_values.into_iter()) {
                    trace!(
                        "would now emit check if {:?} changed according to {:#?}",
                        init_value,
                        event
                    );
                    let now_value = self.emit_rvalue(event.expr, env, prok, check_blk, values)?;
                    let mut trigger = self.emit_event_trigger(
                        event.edge, init_value, now_value, env, prok, check_blk, values,
                    )?;
                    for &iff in &event.iff {
                        let iff_value = self.emit_rvalue(iff, env, prok, check_blk, values)?;
                        trigger = prok
                            .body_mut()
                            .add_inst(
                                llhd::Inst::new(
                                    Some("iff".into()),
                                    llhd::BinaryInst(
                                        llhd::BinaryOp::And,
                                        llhd::int_ty(1),
                                        trigger,
                                        iff_value,
                                    ),
                                ),
                                llhd::InstPosition::BlockEnd(check_blk),
                            )
                            .into();
                    }
                    event_cond = Some(match event_cond {
                        Some(chain) => prok
                            .body_mut()
                            .add_inst(
                                llhd::Inst::new(
                                    Some("event_or".into()),
                                    llhd::BinaryInst(
                                        llhd::BinaryOp::Or,
                                        llhd::int_ty(1),
                                        chain,
                                        trigger,
                                    ),
                                ),
                                llhd::InstPosition::BlockEnd(check_blk),
                            )
                            .into(),
                        None => trigger,
                    });
                }

                // If the event happened, branch to a new block which will
                // contain the subsequent statements. Otherwise jump back up to
                // the initial block.
                block = match event_cond {
                    Some(event_cond) => {
                        let event_blk = prok.body_mut().add_block(
                            llhd::Block::new(Some("event".into())),
                            llhd::BlockPosition::End,
                        );
                        prok.body_mut().add_inst(
                            llhd::Inst::new(
                                None,
                                llhd::BranchInst(llhd::BranchKind::Cond(
                                    event_cond,
                                    event_blk.into(),
                                    init_blk.into(),
                                )),
                            ),
                            llhd::InstPosition::BlockEnd(check_blk),
                        );
                        event_blk
                    }
                    None => check_blk,
                };

                // Emit the actual statement.
                block = self.emit_stmt(stmt, env, prok, block, values)?;
            }
            hir::StmtKind::Expr(expr_id) => {
                self.emit_rvalue(expr_id, env, prok, block, values)?;
            }
            hir::StmtKind::If {
                cond,
                main_stmt,
                else_stmt,
            } => {
                let main_blk = prok.body_mut().add_block(
                    llhd::Block::new(Some("if_true".into())),
                    llhd::BlockPosition::End,
                );
                let else_blk = prok.body_mut().add_block(
                    llhd::Block::new(Some("if_false".into())),
                    llhd::BlockPosition::End,
                );
                let cond = self.emit_rvalue(cond, env, prok, block, values)?;
                prok.body_mut().add_inst(
                    llhd::Inst::new(
                        None,
                        llhd::BranchInst(llhd::BranchKind::Cond(
                            cond,
                            main_blk.into(),
                            else_blk.into(),
                        )),
                    ),
                    llhd::InstPosition::BlockEnd(block),
                );
                let final_blk = prok.body_mut().add_block(
                    llhd::Block::new(Some("if_exit".into())),
                    llhd::BlockPosition::End,
                );
                let main_blk = self.emit_stmt(main_stmt, env, prok, main_blk, values)?;
                prok.body_mut().add_inst(
                    llhd::Inst::new(
                        None,
                        llhd::BranchInst(llhd::BranchKind::Uncond(final_blk.into())),
                    ),
                    llhd::InstPosition::BlockEnd(main_blk),
                );
                let else_blk = match else_stmt {
                    Some(else_stmt) => self.emit_stmt(else_stmt, env, prok, else_blk, values)?,
                    None => else_blk,
                };
                prok.body_mut().add_inst(
                    llhd::Inst::new(
                        None,
                        llhd::BranchInst(llhd::BranchKind::Uncond(final_blk.into())),
                    ),
                    llhd::InstPosition::BlockEnd(else_blk),
                );
                block = final_blk;
            }
            hir::StmtKind::Loop { kind, body } => {
                let body_blk = prok.body_mut().add_block(
                    llhd::Block::new(Some("loop_body".into())),
                    llhd::BlockPosition::End,
                );
                let exit_blk = prok.body_mut().add_block(
                    llhd::Block::new(Some("loop_exit".into())),
                    llhd::BlockPosition::End,
                );

                // Emit the loop initialization.
                let repeat_var = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(count) => {
                        let ty = self.type_of(count, env)?;
                        let lty = self.emit_type(ty)?;
                        let count = self.emit_rvalue(count, env, prok, block, values)?;
                        let var: llhd::ValueRef = prok
                            .body_mut()
                            .add_inst(
                                llhd::Inst::new(
                                    Some("loop_count".into()),
                                    llhd::VariableInst(lty.clone()),
                                ),
                                llhd::InstPosition::BlockEnd(block),
                            )
                            .into();
                        prok.body_mut().add_inst(
                            llhd::Inst::new(None, llhd::StoreInst(lty, count, var.clone())),
                            llhd::InstPosition::BlockEnd(block),
                        );
                        Some((var, ty))
                    }
                    hir::LoopKind::While(_) => None,
                    hir::LoopKind::Do(_) => None,
                    hir::LoopKind::For(init, _, _) => {
                        block = self.emit_stmt(init, env, prok, block, values)?;
                        None
                    }
                };

                // Emit the loop prologue.
                prok.body_mut().add_inst(
                    llhd::Inst::new(
                        None,
                        llhd::BranchInst(llhd::BranchKind::Uncond(body_blk.into())),
                    ),
                    llhd::InstPosition::BlockEnd(block),
                );
                block = body_blk;
                let enter_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let lty = self.emit_type(ty)?;
                        let value = prok
                            .body_mut()
                            .add_inst(
                                llhd::Inst::new(None, llhd::LoadInst(lty.clone(), repeat_var)),
                                llhd::InstPosition::BlockEnd(block),
                            )
                            .into();
                        Some(
                            prok.body_mut()
                                .add_inst(
                                    llhd::Inst::new(
                                        None,
                                        llhd::CompareInst(
                                            llhd::CompareOp::Neq,
                                            lty.clone(),
                                            value,
                                            llhd::const_zero(&lty).into(),
                                        ),
                                    ),
                                    llhd::InstPosition::BlockEnd(block),
                                )
                                .into(),
                        )
                    }
                    hir::LoopKind::While(cond) => {
                        Some(self.emit_rvalue(cond, env, prok, block, values)?)
                    }
                    hir::LoopKind::Do(_) => None,
                    hir::LoopKind::For(_, cond, _) => {
                        Some(self.emit_rvalue(cond, env, prok, block, values)?)
                    }
                };
                if let Some(enter_cond) = enter_cond {
                    let entry_blk = prok.body_mut().add_block(
                        llhd::Block::new(Some("loop_continue".into())),
                        llhd::BlockPosition::End,
                    );
                    prok.body_mut().add_inst(
                        llhd::Inst::new(
                            None,
                            llhd::BranchInst(llhd::BranchKind::Cond(
                                enter_cond,
                                entry_blk.into(),
                                exit_blk.into(),
                            )),
                        ),
                        llhd::InstPosition::BlockEnd(block),
                    );
                    block = entry_blk;
                }

                // Emit the loop body.
                block = self.emit_stmt(body, env, prok, block, values)?;

                // Emit the epilogue.
                let continue_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let lty = self.emit_type(ty)?;
                        let value = prok
                            .body_mut()
                            .add_inst(
                                llhd::Inst::new(
                                    None,
                                    llhd::LoadInst(lty.clone(), repeat_var.clone()),
                                ),
                                llhd::InstPosition::BlockEnd(block),
                            )
                            .into();
                        let value = prok
                            .body_mut()
                            .add_inst(
                                llhd::Inst::new(
                                    None,
                                    llhd::BinaryInst(
                                        llhd::BinaryOp::Sub,
                                        lty.clone(),
                                        value,
                                        self.const_one_for_type(ty)?,
                                    ),
                                ),
                                llhd::InstPosition::BlockEnd(block),
                            )
                            .into();
                        prok.body_mut().add_inst(
                            llhd::Inst::new(None, llhd::StoreInst(lty, value, repeat_var)),
                            llhd::InstPosition::BlockEnd(block),
                        );
                        None
                    }
                    hir::LoopKind::While(_) => None,
                    hir::LoopKind::Do(cond) => {
                        Some(self.emit_rvalue(cond, env, prok, block, values)?)
                    }
                    hir::LoopKind::For(_, _, step) => {
                        self.emit_rvalue(step, env, prok, block, values)?;
                        None
                    }
                };
                prok.body_mut().add_inst(
                    llhd::Inst::new(
                        None,
                        llhd::BranchInst(match continue_cond {
                            Some(cond) => {
                                llhd::BranchKind::Cond(cond, body_blk.into(), exit_blk.into())
                            }
                            None => llhd::BranchKind::Uncond(body_blk.into()),
                        }),
                    ),
                    llhd::InstPosition::BlockEnd(block),
                );
                block = exit_blk;
            }
            _ => return self.unimp_msg("code generation for", hir),
        }
        Ok(block)
    }

    /// Emit the code for an lvalue.
    fn emit_lvalue(
        &mut self,
        expr_id: NodeId,
        env: ParamEnv,
        _prok: &mut llhd::Process,
        _block: llhd::BlockRef,
        values: &mut HashMap<NodeId, llhd::ValueRef>,
    ) -> Result<llhd::ValueRef> {
        let hir = match self.hir_of(expr_id)? {
            HirNode::Expr(x) => x,
            _ => unreachable!(),
        };
        match hir.kind {
            hir::ExprKind::Ident(_) => {
                let binding = self.hir_of(self.resolve_node(expr_id, env)?)?;
                match binding {
                    HirNode::VarDecl(decl) => return Ok(values[&decl.id].clone()),
                    HirNode::Port(port) => return Ok(values[&port.id].clone()),
                    _ => (),
                }
                self.emit(
                    DiagBuilder2::error(format!("{} cannot be assigned to", binding.desc_full()))
                        .span(hir.span())
                        .add_note(format!("{} declared here", binding.desc_full()))
                        .span(binding.human_span()),
                );
                return Err(());
            }
            _ => (),
        }
        self.emit(
            DiagBuilder2::error(format!("{} cannot be assigned to", hir.desc_full()))
                .span(hir.span()),
        );
        Err(())
    }

    /// Emit the code for an lvalue.
    fn emit_rvalue(
        &mut self,
        expr_id: NodeId,
        env: ParamEnv,
        prok: &mut llhd::Process,
        block: llhd::BlockRef,
        values: &mut HashMap<NodeId, llhd::ValueRef>,
    ) -> Result<llhd::ValueRef> {
        let hir = match self.hir_of(expr_id)? {
            HirNode::Expr(x) => x,
            _ => unreachable!(),
        };
        #[allow(unreachable_patterns)]
        match hir.kind {
            hir::ExprKind::IntConst(_) | hir::ExprKind::TimeConst(_) => self
                .emit_const(self.constant_value_of(expr_id, env)?)
                .map(Into::into),
            hir::ExprKind::Ident(_) => {
                let binding = self.resolve_node(expr_id, env)?;
                let value = values[&binding].clone();
                let ty = self.emit_type(self.type_of(expr_id, env)?)?;
                let inst = llhd::Inst::new(None, llhd::ProbeInst(ty, value));
                Ok(prok
                    .body_mut()
                    .add_inst(inst, llhd::InstPosition::BlockEnd(block))
                    .into())
            }
            hir::ExprKind::Unary(op, arg) => match op {
                hir::UnaryOp::BitNot | hir::UnaryOp::LogicNot => {
                    let ty = self.emit_type(self.type_of(expr_id, env)?)?;
                    let value = self.emit_rvalue(arg, env, prok, block, values)?;
                    let inst =
                        llhd::Inst::new(None, llhd::UnaryInst(llhd::UnaryOp::Not, ty, value));
                    Ok(prok
                        .body_mut()
                        .add_inst(inst, llhd::InstPosition::BlockEnd(block))
                        .into())
                }
                hir::UnaryOp::PreInc => {
                    self.emit_incdec(arg, env, llhd::BinaryOp::Add, false, prok, block, values)
                }
                hir::UnaryOp::PreDec => {
                    self.emit_incdec(arg, env, llhd::BinaryOp::Sub, false, prok, block, values)
                }
                hir::UnaryOp::PostInc => {
                    self.emit_incdec(arg, env, llhd::BinaryOp::Add, true, prok, block, values)
                }
                hir::UnaryOp::PostDec => {
                    self.emit_incdec(arg, env, llhd::BinaryOp::Sub, true, prok, block, values)
                }
                _ => self.unimp_msg("code generation for", hir),
            },
            hir::ExprKind::Binary(op, lhs, rhs) => {
                let ty = self.emit_type(self.type_of(lhs, env)?)?;
                let lhs = self.emit_rvalue(lhs, env, prok, block, values)?;
                let rhs = self.emit_rvalue(rhs, env, prok, block, values)?;
                let inst = match op {
                    hir::BinaryOp::Add => llhd::BinaryInst(llhd::BinaryOp::Add, ty, lhs, rhs),
                    hir::BinaryOp::Sub => llhd::BinaryInst(llhd::BinaryOp::Sub, ty, lhs, rhs),
                    hir::BinaryOp::Eq => llhd::CompareInst(llhd::CompareOp::Eq, ty, lhs, rhs),
                    hir::BinaryOp::Neq => llhd::CompareInst(llhd::CompareOp::Neq, ty, lhs, rhs),
                    hir::BinaryOp::Lt => llhd::CompareInst(llhd::CompareOp::Ult, ty, lhs, rhs),
                    hir::BinaryOp::Leq => llhd::CompareInst(llhd::CompareOp::Ule, ty, lhs, rhs),
                    hir::BinaryOp::Gt => llhd::CompareInst(llhd::CompareOp::Ugt, ty, lhs, rhs),
                    hir::BinaryOp::Geq => llhd::CompareInst(llhd::CompareOp::Uge, ty, lhs, rhs),
                    hir::BinaryOp::LogicAnd => llhd::BinaryInst(llhd::BinaryOp::And, ty, lhs, rhs),
                    hir::BinaryOp::LogicOr => llhd::BinaryInst(llhd::BinaryOp::Or, ty, lhs, rhs),
                    _ => return self.unimp_msg("code generation for", hir),
                };
                Ok(prok
                    .body_mut()
                    .add_inst(
                        llhd::Inst::new(None, inst),
                        llhd::InstPosition::BlockEnd(block),
                    )
                    .into())
            }
            _ => self.unimp_msg("code generation for", hir),
        }
    }

    /// Emit the code for a post-increment or -decrement operation.
    fn emit_incdec(
        &mut self,
        expr_id: NodeId,
        env: ParamEnv,
        op: llhd::BinaryOp,
        postfix: bool,
        prok: &mut llhd::Process,
        block: llhd::BlockRef,
        values: &mut HashMap<NodeId, llhd::ValueRef>,
    ) -> Result<llhd::ValueRef> {
        let ty = self.type_of(expr_id, env)?;
        let now = self.emit_rvalue(expr_id, env, prok, block, values)?;
        let next: llhd::ValueRef = prok
            .body_mut()
            .add_inst(
                llhd::Inst::new(
                    None,
                    llhd::BinaryInst(
                        op,
                        self.emit_type(ty)?,
                        now.clone(),
                        self.const_one_for_type(ty)?,
                    ),
                ),
                llhd::InstPosition::BlockEnd(block),
            )
            .into();
        self.emit_blocking_assign(expr_id, next.clone(), env, prok, block, values)?;
        match postfix {
            true => Ok(now),
            false => Ok(next),
        }
    }

    /// Emit a blocking assignment to a variable or signal.
    fn emit_blocking_assign(
        &mut self,
        lvalue_id: NodeId,
        rvalue: llhd::ValueRef,
        env: ParamEnv,
        prok: &mut llhd::Process,
        block: llhd::BlockRef,
        values: &mut HashMap<NodeId, llhd::ValueRef>,
    ) -> Result<()> {
        let lvalue = self.emit_lvalue(lvalue_id, env, prok, block, values)?;
        let (lty, rty) = {
            let ctx = llhd::ModuleContext::new(&self.into);
            let ctx = llhd::ProcessContext::new(&ctx, prok);
            (ctx.ty(&lvalue), ctx.ty(&rvalue))
        };
        let inst = match *lty {
            llhd::SignalType(..) => llhd::DriveInst(lvalue, rvalue, None),
            llhd::PointerType(..) => llhd::StoreInst(rty, rvalue, lvalue),
            ref t => panic!("value of type `{}` cannot be driven", t),
        };
        let inst = llhd::Inst::new(None, inst);
        prok.body_mut()
            .add_inst(inst, llhd::InstPosition::BlockEnd(block));
        Ok(())
    }

    /// Emit the code to check if a certain edge occurred between two values.
    fn emit_event_trigger(
        &mut self,
        edge: ast::EdgeIdent,
        prev: llhd::ValueRef,
        now: llhd::ValueRef,
        _env: ParamEnv,
        prok: &mut llhd::Process,
        block: llhd::BlockRef,
        _values: &mut HashMap<NodeId, llhd::ValueRef>,
    ) -> Result<llhd::ValueRef> {
        let ty = llhd::ProcessContext::new(&llhd::ModuleContext::new(&self.into), prok).ty(&now);

        // Check if a posedge happened.
        let posedge = match edge {
            ast::EdgeIdent::Posedge | ast::EdgeIdent::Edge => {
                let prev_eq_0 = prok
                    .body_mut()
                    .add_inst(
                        llhd::Inst::new(
                            None,
                            llhd::CompareInst(
                                llhd::CompareOp::Eq,
                                ty.clone(),
                                prev.clone(),
                                llhd::const_zero(&ty).into(),
                            ),
                        ),
                        llhd::InstPosition::BlockEnd(block),
                    )
                    .into();
                let now_neq_0 = prok
                    .body_mut()
                    .add_inst(
                        llhd::Inst::new(
                            None,
                            llhd::CompareInst(
                                llhd::CompareOp::Neq,
                                ty.clone(),
                                now.clone(),
                                llhd::const_zero(&ty).into(),
                            ),
                        ),
                        llhd::InstPosition::BlockEnd(block),
                    )
                    .into();
                Some(
                    prok.body_mut()
                        .add_inst(
                            llhd::Inst::new(
                                Some("posedge".into()),
                                llhd::BinaryInst(
                                    llhd::BinaryOp::And,
                                    llhd::int_ty(1),
                                    prev_eq_0,
                                    now_neq_0,
                                ),
                            ),
                            llhd::InstPosition::BlockEnd(block),
                        )
                        .into(),
                )
            }
            _ => None,
        };

        // Check if a negedge happened.
        let negedge = match edge {
            ast::EdgeIdent::Negedge | ast::EdgeIdent::Edge => {
                let now_eq_0 = prok
                    .body_mut()
                    .add_inst(
                        llhd::Inst::new(
                            None,
                            llhd::CompareInst(
                                llhd::CompareOp::Eq,
                                ty.clone(),
                                now.clone(),
                                llhd::const_zero(&ty).into(),
                            ),
                        ),
                        llhd::InstPosition::BlockEnd(block),
                    )
                    .into();
                let prev_neq_0 = prok
                    .body_mut()
                    .add_inst(
                        llhd::Inst::new(
                            None,
                            llhd::CompareInst(
                                llhd::CompareOp::Neq,
                                ty.clone(),
                                prev.clone(),
                                llhd::const_zero(&ty).into(),
                            ),
                        ),
                        llhd::InstPosition::BlockEnd(block),
                    )
                    .into();
                Some(
                    prok.body_mut()
                        .add_inst(
                            llhd::Inst::new(
                                Some("negedge".into()),
                                llhd::BinaryInst(
                                    llhd::BinaryOp::And,
                                    llhd::int_ty(1),
                                    now_eq_0,
                                    prev_neq_0,
                                ),
                            ),
                            llhd::InstPosition::BlockEnd(block),
                        )
                        .into(),
                )
            }
            _ => None,
        };

        // Combine the two edge triggers, or emit an implicit edge check if none
        // of the above edges was checked.
        Ok(match (posedge, negedge) {
            (Some(a), Some(b)) => prok
                .body_mut()
                .add_inst(
                    llhd::Inst::new(
                        Some("edge".into()),
                        llhd::BinaryInst(llhd::BinaryOp::Or, llhd::int_ty(1), a, b),
                    ),
                    llhd::InstPosition::BlockEnd(block),
                )
                .into(),
            (Some(a), None) => a,
            (None, Some(b)) => b,
            (None, None) => prok
                .body_mut()
                .add_inst(
                    llhd::Inst::new(
                        Some("impledge".into()),
                        llhd::CompareInst(llhd::CompareOp::Neq, ty, prev, now),
                    ),
                    llhd::InstPosition::BlockEnd(block),
                )
                .into(),
        })
    }

    /// Emit the value `1` for a type.
    fn const_one_for_type(&mut self, ty: Type<'gcx>) -> Result<llhd::ValueRef> {
        use num::one;
        match *ty {
            TypeKind::Void | TypeKind::Time => panic!("no unit-value for type {:?}", ty),
            TypeKind::Bit(..) | TypeKind::Int(..) => Ok(self
                .emit_const(self.intern_value(value::make_int(ty, one())))?
                .into()),
            TypeKind::Named(_, _, ty) => self.const_one_for_type(ty),
        }
    }

    /// Execute the initialization step of a generate loop.
    fn execute_genvar_init(&mut self, id: NodeId, env: ParamEnv) -> Result<ParamEnv> {
        let hir = self.hir_of(id)?;
        match hir {
            HirNode::GenvarDecl(_) => (),
            _ => unreachable!(),
        }
        Ok(env)
    }

    /// Execute the iteration step of a generate loop.
    fn execute_genvar_step(&mut self, id: NodeId, env: ParamEnv) -> Result<ParamEnv> {
        let hir = self.hir_of(id)?;
        let mut env_data = self.param_env_data(env).clone();
        let next = match hir {
            HirNode::Expr(expr) => match expr.kind {
                hir::ExprKind::Unary(op, target_id) => {
                    let target_id = self.resolve_node(target_id, env)?;
                    let current_value = self.constant_value_of(target_id, env)?;
                    let next_value = match current_value.kind {
                        ValueKind::Int(ref v) => match op {
                            hir::UnaryOp::PostInc | hir::UnaryOp::PreInc => Some(v + 1),
                            hir::UnaryOp::PostDec | hir::UnaryOp::PreDec => Some(v - 1),
                            _ => None,
                        }
                        .map(|v| value::make_int(current_value.ty, v)),
                        _ => unreachable!(),
                    };
                    next_value.map(|v| (target_id, v))
                }
                _ => None,
            },
            _ => None,
        };
        match next {
            Some((target_id, next_value)) => {
                env_data.set_value(target_id, self.intern_value(next_value));
                return Ok(self.intern_param_env(env_data));
            }
            None => {
                self.emit(
                    DiagBuilder2::error(format!(
                        "{} is not a valid genvar iteration step",
                        hir.desc_full()
                    ))
                    .span(hir.human_span()),
                );
                Err(())
            }
        }
    }
}

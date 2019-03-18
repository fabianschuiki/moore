// Copyright (c) 2016-2019 Fabian Schuiki

//! This module implements LLHD code generation.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{bit_size_of_type, Type, TypeKind},
    value::{Value, ValueKind},
    ParamEnv, ParamEnvSource, PortMappingSource,
};
use num::{
    traits::{cast::ToPrimitive, sign::Signed},
    BigInt, One, Zero,
};
use std::{collections::HashMap, ops::Deref, ops::DerefMut};

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
    interned_types: HashMap<(Type<'gcx>, ParamEnv), Result<llhd::Type>>,
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
            let ty = self.emit_type(ty, env)?;
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
        let mut ent = llhd::Entity::new(entity_name.clone(), ty.clone());
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

        self.emit_module_block(id, env, &hir.block, &mut ent, &mut values, &entity_name)?;

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
        name_prefix: &str,
    ) -> Result<()> {
        // Emit declarations.
        for &decl_id in &hir.decls {
            let hir = match self.hir_of(decl_id)? {
                HirNode::VarDecl(x) => x,
                _ => unreachable!(),
            };
            let ty = self.emit_type(self.type_of(decl_id, env)?, env)?;
            let init = match hir.init {
                Some(expr) => Some(self.emit_const(self.constant_value_of(expr, env)?)?.into()),
                None => None,
            };
            let inst = llhd::Inst::new(Some(hir.name.value.into()), llhd::SignalInst(ty, init));
            let id = ent.add_inst(inst, llhd::InstPosition::End);
            values.insert(decl_id, id.into());
        }

        // Emit assignments.
        for &assign_id in &hir.assigns {
            let mut gen = EntityGenerator {
                gen: self,
                ent: ent,
                values: values,
            };
            let hir = match gen.hir_of(assign_id)? {
                HirNode::Assign(x) => x,
                _ => unreachable!(),
            };
            let lhs = gen.emit_lvalue(hir.lhs, env)?;
            let rhs = gen.emit_rvalue_mode(hir.rhs, env, Mode::Value)?;
            gen.emit_nameless_inst(llhd::DriveInst(lhs, rhs, None));
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
            let port_mapping = self.port_mapping(PortMappingSource::ModuleInst {
                module: resolved,
                inst: inst_id,
                env: inst_env,
                pos: &hir.pos_ports,
                named: &hir.named_ports,
            })?;
            trace!("port_mapping = {:#?}", port_mapping);
            let mut inputs = Vec::new();
            let mut outputs = Vec::new();
            let resolved_hir = match self.hir_of(resolved)? {
                HirNode::Module(x) => x,
                _ => unreachable!(),
            };
            for &port_id in resolved_hir.ports {
                let port = match self.hir_of(port_id)? {
                    HirNode::Port(p) => p,
                    _ => unreachable!(),
                };
                let mapping = port_mapping.find(port_id);
                let (is_input, is_output) = match port.dir {
                    ast::PortDir::Input | ast::PortDir::Ref => (true, false),
                    ast::PortDir::Output => (false, true),
                    ast::PortDir::Inout => (true, true),
                };
                if let Some(mapping) = mapping {
                    let mut gen = EntityGenerator {
                        gen: self,
                        ent,
                        values,
                    };
                    if is_input {
                        inputs.push(gen.emit_rvalue_mode(mapping.0, mapping.1, Mode::Signal)?);
                    }
                    if is_output {
                        outputs.push(gen.emit_lvalue(mapping.0, mapping.1)?);
                    }
                } else {
                    unimplemented!("unconnected port");
                }
            }
            trace!("inputs = {:#?}", inputs);
            trace!("outputs = {:#?}", outputs);
            let target = self.emit_module_with_env(resolved, inst_env)?;
            let ty = self.tables.module_types[&(resolved, inst_env)].clone();
            let inst = llhd::Inst::new(
                Some(hir.name.value.into()),
                llhd::InstanceInst(ty, target.into(), inputs, outputs),
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
                            self.emit_module_block(id, env, else_body, ent, values, name_prefix)?;
                        }
                    } else {
                        self.emit_module_block(id, env, main_body, ent, values, name_prefix)?;
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
                        self.emit_module_block(id, local_env, body, ent, values, name_prefix)?;
                        local_env = self.execute_genvar_step(step, local_env)?;
                    }
                }
                _ => return self.unimp_msg("code generation for", hir),
            }
        }

        // Emit and instantiate procedures.
        for &proc_id in &hir.procs {
            use llhd::Context as LlhdContext;
            let prok = self.emit_procedure(proc_id, env, name_prefix)?;
            let ty = llhd::ModuleContext::new(&self.into)
                .ty(&prok.into())
                .clone();
            let acc = self.accessed_nodes(proc_id)?;
            let lookup_value = |&id| match values.get(&id) {
                Some(v) => v.clone(),
                None => {
                    self.emit(
                        DiagBuilder2::bug(format!(
                            "{} used as input/output of {}, but no value has been emitted",
                            self.hir_of(id).unwrap().desc_full(),
                            self.hir_of(proc_id).unwrap().desc_full(),
                        ))
                        .span(self.span(id)),
                    );
                    panic!("no value emitted for {:?}", id);
                }
            };
            let inputs = acc.read.iter().map(lookup_value).collect();
            let outputs = acc.written.iter().map(lookup_value).collect();
            let inst = llhd::Inst::new(None, llhd::InstanceInst(ty, prok.into(), inputs, outputs));
            ent.add_inst(inst, llhd::InstPosition::End);
        }

        Ok(())
    }

    /// Emit the code for a procedure.
    fn emit_procedure(
        &mut self,
        id: NodeId,
        env: ParamEnv,
        name_prefix: &str,
    ) -> Result<llhd::ProcessRef> {
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
            inputs.push((
                id,
                llhd::signal_ty(self.emit_type(self.type_of(id, env)?, env)?),
            ));
        }
        for &id in &acc.written {
            outputs.push((
                id,
                llhd::signal_ty(self.emit_type(self.type_of(id, env)?, env)?),
            ));
        }
        trace!("process inputs = {:#?}", inputs);
        trace!("process outputs = {:#?}", outputs);

        // Create process and entry block.
        let proc_name = format!(
            "{}.{}.{}.{}",
            name_prefix,
            match hir.kind {
                ast::ProcedureKind::Initial => "initial",
                ast::ProcedureKind::Always => "always",
                ast::ProcedureKind::AlwaysComb => "always_comb",
                ast::ProcedureKind::AlwaysLatch => "always_latch",
                ast::ProcedureKind::AlwaysFf => "always_ff",
                ast::ProcedureKind::Final => "final",
            },
            id.as_usize(),
            env.0,
        );
        let mut prok = llhd::Process::new(
            proc_name,
            llhd::entity_ty(
                inputs.iter().map(|(_, ty)| ty.clone()).collect(),
                outputs.iter().map(|(_, ty)| ty.clone()).collect(),
            ),
        );
        let entry_blk = prok
            .body_mut()
            .add_block(llhd::Block::new(None), llhd::BlockPosition::Begin);

        // Create a mapping from read/written nodes to process parameters.
        let mut values = HashMap::new();
        for (&(id, _), arg) in inputs
            .iter()
            .zip(prok.inputs())
            .chain(outputs.iter().zip(prok.outputs()))
        {
            values.insert(id, arg.as_ref().into());
        }
        let mut pg = ProcessGenerator {
            gen: self,
            prok: &mut prok,
            pos: llhd::InstPosition::BlockEnd(entry_blk),
            values: &mut values,
        };

        // Emit prologue and determine which basic block to jump back to.
        let head_blk = match hir.kind {
            ast::ProcedureKind::AlwaysComb => {
                let body_blk = pg.add_named_block("body");
                let check_blk = pg.add_named_block("check");
                pg.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(body_blk)));
                pg.append_to_block(check_blk);
                let trigger_on = inputs
                    .iter()
                    .map(|(id, _)| pg.emitted_value(*id).clone())
                    .collect();
                pg.emit_nameless_inst(llhd::WaitInst(body_blk, None, trigger_on));
                pg.append_to_block(body_blk);
                check_blk
            }
            _ => entry_blk,
        };

        // Emit the main statement.
        pg.emit_stmt(hir.stmt, env)?;

        // Emit epilogue.
        match hir.kind {
            ast::ProcedureKind::Initial => {
                pg.emit_nameless_inst(llhd::HaltInst);
            }
            ast::ProcedureKind::Always
            | ast::ProcedureKind::AlwaysComb
            | ast::ProcedureKind::AlwaysLatch
            | ast::ProcedureKind::AlwaysFf => {
                pg.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(head_blk)));
            }
            _ => (),
        }
        Ok(self.into.add_process(prok))
    }

    /// Map a type to an LLHD type (interned).
    fn emit_type(&mut self, ty: Type<'gcx>, env: ParamEnv) -> Result<llhd::Type> {
        if let Some(x) = self.tables.interned_types.get(&(ty, env)) {
            x.clone()
        } else {
            let x = self.emit_type_uninterned(ty, env);
            self.tables.interned_types.insert((ty, env), x.clone());
            x
        }
    }

    /// Map a type to an LLHD type.
    fn emit_type_uninterned(&mut self, ty: Type<'gcx>, env: ParamEnv) -> Result<llhd::Type> {
        #[allow(unreachable_patterns)]
        Ok(match *ty {
            TypeKind::Void => llhd::void_ty(),
            TypeKind::Bit(_) => llhd::int_ty(1),
            TypeKind::Int(width, _) => llhd::int_ty(width),
            TypeKind::Named(_, _, ty) => self.emit_type(ty, env)?,
            TypeKind::Struct(id) => {
                let fields = match self.hir_of(id)? {
                    HirNode::Type(hir::Type {
                        kind: hir::TypeKind::Struct(ref fields),
                        ..
                    }) => fields,
                    _ => unreachable!(),
                };
                let mut types = vec![];
                for &field_id in fields {
                    types.push(self.emit_type(self.type_of(field_id, env)?, env)?);
                }
                llhd::struct_ty(types)
            }
            TypeKind::PackedArray(size, ty) => llhd::array_ty(size, self.emit_type(ty, env)?),
            _ => unimplemented!("emit type {:?}", ty),
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

    /// Emit the value `1` for a type.
    fn const_one_for_type(&mut self, ty: Type<'gcx>) -> Result<llhd::ValueRef> {
        use num::one;
        match *ty {
            TypeKind::Bit(..) | TypeKind::Int(..) => Ok(self
                .emit_const(self.intern_value(value::make_int(ty, one())))?
                .into()),
            TypeKind::Named(_, _, ty) => self.const_one_for_type(ty),
            _ => panic!("no unit-value for type {:?}", ty),
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

/// A code generator for entities.
struct EntityGenerator<'a, 'gcx, C> {
    /// The global code generator.
    gen: &'a mut CodeGenerator<'gcx, C>,
    /// The entity into which instructions are emitted.
    ent: &'a mut llhd::Entity,
    /// The emitted values.
    values: &'a mut HashMap<NodeId, llhd::ValueRef>,
}

impl<'a, 'gcx, C> Deref for EntityGenerator<'a, 'gcx, C> {
    type Target = CodeGenerator<'gcx, C>;

    fn deref(&self) -> &CodeGenerator<'gcx, C> {
        &self.gen
    }
}

impl<'a, 'gcx, C> DerefMut for EntityGenerator<'a, 'gcx, C> {
    fn deref_mut(&mut self) -> &mut CodeGenerator<'gcx, C> {
        &mut self.gen
    }
}

impl<'a, 'b, 'gcx, C> ExprGenerator<'a, 'gcx, C> for EntityGenerator<'b, 'gcx, &'a C>
where
    C: Context<'gcx> + 'a,
{
    type AsStmtGen = DummyStmtGenerator<'b, 'gcx, &'a C>;

    fn emit_inst(&mut self, inst: llhd::Inst) -> llhd::InstRef {
        self.ent.add_inst(inst, llhd::InstPosition::End)
    }

    fn emitted_value(&self, node_id: NodeId) -> &llhd::ValueRef {
        &self.values[&node_id]
    }

    fn set_emitted_value(&mut self, node_id: NodeId, value: llhd::ValueRef) {
        self.values.insert(node_id, value);
    }

    fn with_llhd_context<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&dyn llhd::Context) -> R,
    {
        let ctx = llhd::ModuleContext::new(&self.gen.into);
        let ctx = llhd::EntityContext::new(&ctx, self.ent);
        f(&ctx)
    }
}

/// A code generator for processes.
struct ProcessGenerator<'a, 'gcx, C> {
    /// The global code generator.
    gen: &'a mut CodeGenerator<'gcx, C>,
    /// The process into which instructions are emitted.
    prok: &'a mut llhd::Process,
    /// The current insertion point for new instructions.
    pos: llhd::InstPosition,
    /// The emitted values.
    values: &'a mut HashMap<NodeId, llhd::ValueRef>,
}

impl<'a, 'gcx, C> Deref for ProcessGenerator<'a, 'gcx, C> {
    type Target = CodeGenerator<'gcx, C>;

    fn deref(&self) -> &CodeGenerator<'gcx, C> {
        &self.gen
    }
}

impl<'a, 'gcx, C> DerefMut for ProcessGenerator<'a, 'gcx, C> {
    fn deref_mut(&mut self) -> &mut CodeGenerator<'gcx, C> {
        &mut self.gen
    }
}

impl<'a, 'b, 'gcx, C> ExprGenerator<'a, 'gcx, C> for ProcessGenerator<'b, 'gcx, &'a C>
where
    C: Context<'gcx> + 'a,
{
    type AsStmtGen = Self;

    fn as_stmt_gen(&mut self) -> Option<&mut Self::AsStmtGen> {
        Some(self)
    }

    fn emit_inst(&mut self, inst: llhd::Inst) -> llhd::InstRef {
        self.prok.body_mut().add_inst(inst, self.pos)
    }

    fn emitted_value(&self, node_id: NodeId) -> &llhd::ValueRef {
        &self.values[&node_id]
    }

    fn set_emitted_value(&mut self, node_id: NodeId, value: llhd::ValueRef) {
        self.values.insert(node_id, value);
    }

    fn with_llhd_context<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&dyn llhd::Context) -> R,
    {
        let ctx = llhd::ModuleContext::new(&self.gen.into);
        let ctx = llhd::ProcessContext::new(&ctx, self.prok);
        f(&ctx)
    }
}

impl<'a, 'b, 'gcx, C> StmtGenerator<'a, 'gcx, C> for ProcessGenerator<'b, 'gcx, &'a C>
where
    C: Context<'gcx> + 'a,
{
    fn set_insertion_point(&mut self, pos: llhd::InstPosition) {
        self.pos = pos;
    }

    fn insertion_point(&self) -> llhd::InstPosition {
        self.pos
    }

    fn add_block(&mut self, block: llhd::Block, pos: llhd::BlockPosition) -> llhd::BlockRef {
        self.prok.body_mut().add_block(block, pos)
    }
}

/// A generator for expressions.
///
/// This trait is implemented by everything that can accept the code emitted for
/// an expression. This most prominently also includes entities, which have no
/// means for control flow.
trait ExprGenerator<'a, 'gcx, C>
where
    Self: DerefMut<Target = CodeGenerator<'gcx, &'a C>>,
    C: Context<'gcx> + 'a,
{
    type AsStmtGen: StmtGenerator<'a, 'gcx, C>;

    /// Try to convert to a statement generator.
    ///
    /// Returns `Some` if `self` can emit code for statements, `None` otherwise.
    /// This function is useful for certain expressions such as `x++` which do
    /// mutate state and have to emit certain sequential statements.
    fn as_stmt_gen(&mut self) -> Option<&mut Self::AsStmtGen> {
        None
    }

    /// Emit an instruction.
    fn emit_inst(&mut self, inst: llhd::Inst) -> llhd::InstRef;

    /// Get a value emitted for a node.
    ///
    /// Panics if no value has been emitted.
    fn emitted_value(&self, node_id: NodeId) -> &llhd::ValueRef;

    /// Set the value emitted for a node.
    fn set_emitted_value(&mut self, node_id: NodeId, value: llhd::ValueRef);

    /// Resolve an LLHD value reference.
    fn with_llhd_context<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&dyn llhd::Context) -> R;

    /// Get the type of an LLHD value.
    fn llhd_type(&self, value: &llhd::ValueRef) -> llhd::Type {
        self.with_llhd_context(|ctx| ctx.ty(value))
    }

    /// Emit a nameless instruction.
    ///
    /// Constructs an instruction and calls [`emit_inst`].
    fn emit_nameless_inst(&mut self, inst: llhd::InstKind) -> llhd::InstRef {
        self.emit_inst(llhd::Inst::new(None, inst))
    }

    /// Emit a named instruction.
    ///
    /// Constructs an instruction and calls [`emit_inst`].
    fn emit_named_inst(&mut self, name: impl Into<String>, inst: llhd::InstKind) -> llhd::InstRef {
        self.emit_inst(llhd::Inst::new(Some(name.into()), inst))
    }

    /// Emit the code for an rvalue.
    fn emit_rvalue(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<llhd::ValueRef> {
        self.emit_rvalue_mode(expr_id, env, Mode::Value)
    }

    /// Emit the code for an rvalue.
    fn emit_rvalue_mode(
        &mut self,
        expr_id: NodeId,
        env: ParamEnv,
        mode: Mode,
    ) -> Result<llhd::ValueRef> {
        let hir = match self.hir_of(expr_id)? {
            HirNode::Expr(x) => x,
            _ => unreachable!(),
        };
        #[allow(unreachable_patterns)]
        let (value, actual_mode) = match hir.kind {
            hir::ExprKind::IntConst(..)
            | hir::ExprKind::UnsizedConst(..)
            | hir::ExprKind::TimeConst(_) => {
                let k = self.constant_value_of(expr_id, env)?;
                (self.emit_const(k).map(Into::into)?, Mode::Value)
            }
            hir::ExprKind::Ident(name) => {
                let binding = self.resolve_node(expr_id, env)?;
                let (value, is_const) = match self.is_constant(binding)? {
                    true => {
                        let k = self.constant_value_of(binding, env)?;
                        (self.emit_const(k)?.into(), true)
                    }
                    false => (self.emitted_value(binding).clone(), false),
                };
                let ty = self.llhd_type(&value);
                let is_signal = match *ty {
                    llhd::SignalType(_) => true,
                    _ => false,
                };
                // We currently just assume that the value above is a signal.
                // As soon as we have actual variable declarations, this will
                // need some more cleverness.
                match (mode, is_signal, is_const) {
                    (Mode::Value, true, _) => {
                        let ty = ty.unwrap_signal().clone();
                        (
                            self.emit_named_inst(format!("{}", name), llhd::ProbeInst(ty, value))
                                .into(),
                            Mode::Value,
                        )
                    }
                    (Mode::Value, false, false) => {
                        // let ty = ty.as_pointer().clone(); // TODO: fix this
                        let ty = match *ty {
                            llhd::PointerType(ref ty) => ty.clone(),
                            _ => panic!("not a pointer"),
                        };
                        (
                            self.emit_named_inst(format!("{}", name), llhd::LoadInst(ty, value))
                                .into(),
                            Mode::Value,
                        )
                    }
                    (Mode::Value, false, true) => (value, Mode::Value),
                    (Mode::Signal, true, _) => (value, Mode::Signal),
                    (Mode::Signal, false, _) => (value, Mode::Value),
                }
            }
            hir::ExprKind::Unary(op, arg) => (
                match op {
                    hir::UnaryOp::Pos => self.emit_rvalue(arg, env)?,
                    hir::UnaryOp::Neg => {
                        let ty = self.type_of(expr_id, env)?;
                        let ty = self.emit_type(ty, env)?;
                        let zero = llhd::const_zero(&ty).into();
                        let arg = self.emit_rvalue(arg, env)?;
                        self.emit_nameless_inst(llhd::BinaryInst(
                            llhd::BinaryOp::Sub,
                            ty,
                            zero,
                            arg,
                        ))
                        .into()
                    }
                    hir::UnaryOp::BitNot | hir::UnaryOp::LogicNot => {
                        let ty = self.type_of(expr_id, env)?;
                        let ty = self.emit_type(ty, env)?;
                        let value = self.emit_rvalue(arg, env)?;
                        self.emit_nameless_inst(llhd::UnaryInst(llhd::UnaryOp::Not, ty, value))
                            .into()
                    }
                    hir::UnaryOp::PreInc => {
                        self.emit_incdec(arg, env, llhd::BinaryOp::Add, false)?
                    }
                    hir::UnaryOp::PreDec => {
                        self.emit_incdec(arg, env, llhd::BinaryOp::Sub, false)?
                    }
                    hir::UnaryOp::PostInc => {
                        self.emit_incdec(arg, env, llhd::BinaryOp::Add, true)?
                    }
                    hir::UnaryOp::PostDec => {
                        self.emit_incdec(arg, env, llhd::BinaryOp::Sub, true)?
                    }
                    hir::UnaryOp::RedAnd => {
                        self.emit_reduction(arg, env, llhd::BinaryOp::And, false)?
                    }
                    hir::UnaryOp::RedNand => {
                        self.emit_reduction(arg, env, llhd::BinaryOp::And, true)?
                    }
                    hir::UnaryOp::RedOr => {
                        self.emit_reduction(arg, env, llhd::BinaryOp::Or, false)?
                    }
                    hir::UnaryOp::RedNor => {
                        self.emit_reduction(arg, env, llhd::BinaryOp::Or, true)?
                    }
                    hir::UnaryOp::RedXor => {
                        self.emit_reduction(arg, env, llhd::BinaryOp::Xor, false)?
                    }
                    hir::UnaryOp::RedXnor => {
                        self.emit_reduction(arg, env, llhd::BinaryOp::Xor, true)?
                    }
                    _ => return self.unimp_msg("code generation for", hir),
                },
                Mode::Value,
            ),
            hir::ExprKind::Binary(op, lhs, rhs) => {
                let ty = self.type_of(lhs, env)?;
                let ty = self.emit_type(ty, env)?;
                let lhs = self.emit_rvalue(lhs, env)?;
                let rhs = self.emit_rvalue(rhs, env)?;
                let inst = match op {
                    hir::BinaryOp::Add => llhd::BinaryInst(llhd::BinaryOp::Add, ty, lhs, rhs),
                    hir::BinaryOp::Sub => llhd::BinaryInst(llhd::BinaryOp::Sub, ty, lhs, rhs),
                    hir::BinaryOp::Mul => llhd::BinaryInst(llhd::BinaryOp::Mul, ty, lhs, rhs),
                    hir::BinaryOp::Div => llhd::BinaryInst(llhd::BinaryOp::Div, ty, lhs, rhs),
                    hir::BinaryOp::Mod => llhd::BinaryInst(llhd::BinaryOp::Mod, ty, lhs, rhs),
                    hir::BinaryOp::Eq => llhd::CompareInst(llhd::CompareOp::Eq, ty, lhs, rhs),
                    hir::BinaryOp::Neq => llhd::CompareInst(llhd::CompareOp::Neq, ty, lhs, rhs),
                    hir::BinaryOp::Lt => llhd::CompareInst(llhd::CompareOp::Ult, ty, lhs, rhs),
                    hir::BinaryOp::Leq => llhd::CompareInst(llhd::CompareOp::Ule, ty, lhs, rhs),
                    hir::BinaryOp::Gt => llhd::CompareInst(llhd::CompareOp::Ugt, ty, lhs, rhs),
                    hir::BinaryOp::Geq => llhd::CompareInst(llhd::CompareOp::Uge, ty, lhs, rhs),
                    hir::BinaryOp::LogicAnd | hir::BinaryOp::BitAnd => {
                        llhd::BinaryInst(llhd::BinaryOp::And, ty, lhs, rhs)
                    }
                    hir::BinaryOp::LogicOr | hir::BinaryOp::BitOr => {
                        llhd::BinaryInst(llhd::BinaryOp::Or, ty, lhs, rhs)
                    }
                    hir::BinaryOp::BitXor => llhd::BinaryInst(llhd::BinaryOp::Xor, ty, lhs, rhs),
                    hir::BinaryOp::BitNand => {
                        let v = self.emit_nameless_inst(llhd::BinaryInst(
                            llhd::BinaryOp::And,
                            ty.clone(),
                            lhs,
                            rhs,
                        ));
                        llhd::UnaryInst(llhd::UnaryOp::Not, ty, v.into())
                    }
                    hir::BinaryOp::BitNor => {
                        let v = self.emit_nameless_inst(llhd::BinaryInst(
                            llhd::BinaryOp::Or,
                            ty.clone(),
                            lhs,
                            rhs,
                        ));
                        llhd::UnaryInst(llhd::UnaryOp::Not, ty, v.into())
                    }
                    hir::BinaryOp::BitXnor => {
                        let v = self.emit_nameless_inst(llhd::BinaryInst(
                            llhd::BinaryOp::Xor,
                            ty.clone(),
                            lhs,
                            rhs,
                        ));
                        llhd::UnaryInst(llhd::UnaryOp::Not, ty, v.into())
                    }
                    hir::BinaryOp::LogicShL => {
                        self.emit_shift_operator(llhd::ShiftDir::Left, false, ty, lhs, rhs)
                    }
                    hir::BinaryOp::LogicShR => {
                        self.emit_shift_operator(llhd::ShiftDir::Right, false, ty, lhs, rhs)
                    }
                    hir::BinaryOp::ArithShL => {
                        self.emit_shift_operator(llhd::ShiftDir::Left, true, ty, lhs, rhs)
                    }
                    hir::BinaryOp::ArithShR => {
                        self.emit_shift_operator(llhd::ShiftDir::Right, true, ty, lhs, rhs)
                    }
                    _ => {
                        error!("{:#?}", hir);
                        return self.unimp_msg("code generation for", hir);
                    }
                };
                (self.emit_nameless_inst(inst).into(), Mode::Value)
            }
            hir::ExprKind::Field(target_id, field_name) => {
                let (_, index, _) = self.resolve_field_access(expr_id, env)?;
                let target = self.emit_rvalue_mode(target_id, env, Mode::Value)?;
                (
                    self.emit_named_inst(
                        format!(
                            "{}.{}",
                            self.with_llhd_context(|ctx| ctx
                                .try_value(&target)
                                .and_then(|v| v.name())
                                .map(String::from))
                                .unwrap_or_else(|| "struct".into()),
                            field_name
                        ),
                        llhd::ExtractInst(
                            self.llhd_type(&target),
                            target,
                            llhd::SliceMode::Element(index),
                        ),
                    )
                    .into(),
                    Mode::Value,
                )
            }
            hir::ExprKind::Index(target_id, mode) => {
                let target = self.emit_rvalue_mode(target_id, env, Mode::Value)?;
                (self.emit_index_access(target, env, mode)?, Mode::Value)
            }
            hir::ExprKind::Ternary(cond, true_expr, false_expr) => {
                let gen = match self.as_stmt_gen() {
                    Some(gen) => gen,
                    None => {
                        let hir = self.hir_of(expr_id)?;
                        self.emit(
                            DiagBuilder2::error(format!(
                                "ternary operator only supported in processes or functions",
                            ))
                            .span(hir.human_span()),
                        );
                        return Err(());
                    }
                };
                let ty = gen.type_of(expr_id, env)?;
                let ty = gen.emit_type(ty, env)?;
                let true_blk = gen.add_named_block("ternary_true");
                let false_blk = gen.add_named_block("ternary_false");
                let result_var: llhd::ValueRef = gen
                    .emit_named_inst("ternary", llhd::VariableInst(ty.clone()))
                    .into();
                let cond = gen.emit_rvalue(cond, env)?;
                gen.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Cond(
                    cond,
                    true_blk.into(),
                    false_blk.into(),
                )));
                let final_blk = gen.add_named_block("ternary_exit");
                gen.append_to_block(true_blk);
                let value = gen.emit_rvalue(true_expr, env)?;
                gen.emit_nameless_inst(llhd::StoreInst(ty.clone(), result_var.clone(), value));
                gen.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(
                    final_blk.into(),
                )));
                gen.append_to_block(false_blk);
                let value = gen.emit_rvalue(false_expr, env)?;
                gen.emit_nameless_inst(llhd::StoreInst(ty.clone(), result_var.clone(), value));
                gen.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(
                    final_blk.into(),
                )));
                gen.append_to_block(final_blk);
                (
                    self.emit_nameless_inst(llhd::LoadInst(ty, result_var))
                        .into(),
                    Mode::Value,
                )
            }
            hir::ExprKind::Builtin(_) => {
                let k = self.constant_value_of(expr_id, env)?;
                (self.emit_const(k)?.into(), Mode::Value)
            }
            _ => return self.unimp_msg("code generation for", hir),
        };
        match (mode, actual_mode) {
            (Mode::Signal, Mode::Value) => {
                let ty = self.llhd_type(&value);
                let sig = self.emit_nameless_inst(llhd::SignalInst(ty, None));
                self.emit_nameless_inst(llhd::DriveInst(sig.clone().into(), value, None));
                Ok(sig.into())
            }
            (Mode::Value, Mode::Signal) => unreachable!(),
            _ => Ok(value),
        }
    }

    /// Emit the code for an lvalue.
    fn emit_lvalue(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<llhd::ValueRef> {
        let hir = match self.hir_of(expr_id)? {
            HirNode::Expr(x) => x,
            _ => unreachable!(),
        };
        match hir.kind {
            hir::ExprKind::Ident(_) => {
                let binding = self.hir_of(self.resolve_node(expr_id, env)?)?;
                match binding {
                    HirNode::VarDecl(decl) => return Ok(self.emitted_value(decl.id).clone()),
                    HirNode::Port(port) => return Ok(self.emitted_value(port.id).clone()),
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
            hir::ExprKind::Field(target, field_name) => {
                let (_, field_index, _) = self.resolve_field_access(expr_id, env)?;
                let target_val = self.emit_lvalue(target, env)?;
                let extracted = self.emit_named_inst(
                    format!(
                        "{}.{}",
                        self.with_llhd_context(|ctx| ctx
                            .try_value(&target_val)
                            .and_then(|v| v.name().map(String::from)))
                            .unwrap_or_else(|| "struct".into()),
                        field_name
                    ),
                    llhd::ExtractInst(
                        self.llhd_type(&target_val),
                        target_val,
                        llhd::SliceMode::Element(field_index),
                    ),
                );
                return Ok(extracted.into());
            }
            hir::ExprKind::Index(target_id, mode) => {
                let target = self.emit_lvalue(target_id, env)?;
                return self.emit_index_access(target, env, mode);
            }
            _ => (),
        }
        self.emit(
            DiagBuilder2::error(format!("{} cannot be assigned to", hir.desc_full()))
                .span(hir.span()),
        );
        Err(())
    }

    /// Emit the code for a post-increment or -decrement operation.
    fn emit_incdec(
        &mut self,
        expr_id: NodeId,
        env: ParamEnv,
        op: llhd::BinaryOp,
        postfix: bool,
    ) -> Result<llhd::ValueRef> {
        let ty = self.type_of(expr_id, env)?;
        let now = self.emit_rvalue(expr_id, env)?;
        let llty = self.emit_type(ty, env)?;
        let one = self.const_one_for_type(ty)?;
        let next: llhd::ValueRef = self
            .emit_nameless_inst(llhd::BinaryInst(op, llty, now.clone(), one))
            .into();
        match self.as_stmt_gen() {
            Some(gen) => {
                gen.emit_blocking_assign(expr_id, next.clone(), env)?;
                match postfix {
                    true => Ok(now),
                    false => Ok(next),
                }
            }
            None => {
                let hir = self.hir_of(expr_id)?;
                self.emit(
                    DiagBuilder2::error(format!(
                        "inc/dec operator can only be used in processes, tasks, and functions",
                    ))
                    .span(hir.human_span()),
                );
                Err(())
            }
        }
    }

    /// Emit the code to index into an integer or array.
    fn emit_index_access(
        &mut self,
        target: llhd::ValueRef,
        env: ParamEnv,
        mode: hir::IndexMode,
    ) -> Result<llhd::ValueRef> {
        let basename = self
            .with_llhd_context(|ctx| {
                ctx.try_value(&target)
                    .and_then(|v| v.name().map(String::from))
            })
            .unwrap_or_else(|| "".into());
        let target_ty = self.llhd_type(&target);
        let shift = match mode {
            hir::IndexMode::One(index) => self.emit_rvalue(index, env)?,
            hir::IndexMode::Many(ast::RangeMode::RelativeUp, base, _delta) => {
                self.emit_rvalue(base, env)?
            }
            hir::IndexMode::Many(ast::RangeMode::RelativeDown, base, delta) => {
                let base = self.emit_rvalue(base, env)?;
                let delta = self.emit_rvalue(delta, env)?;
                let ty = self.llhd_type(&base);
                self.emit_nameless_inst(llhd::BinaryInst(llhd::BinaryOp::Sub, ty, base, delta))
                    .into()
            }
            hir::IndexMode::Many(ast::RangeMode::Absolute, lhs, rhs) => {
                let lhs_int = self.constant_int_value_of(lhs, env)?;
                let rhs_int = self.constant_int_value_of(rhs, env)?;
                let base = std::cmp::min(lhs_int, rhs_int).clone().to_usize().unwrap();
                let length = ((lhs_int - rhs_int).abs() + BigInt::one())
                    .to_usize()
                    .unwrap();
                return Ok(self
                    .emit_named_inst(
                        format!("{}.const_slice", basename),
                        llhd::ExtractInst(
                            self.llhd_type(&target),
                            target,
                            llhd::SliceMode::Slice(base, length),
                        ),
                    )
                    .into());
            }
        };
        let single_element_ty = |ty: &llhd::Type| -> llhd::Type {
            match **ty {
                llhd::IntType(_) => llhd::int_ty(1),
                llhd::ArrayType(_, ref ty) => ty.clone(),
                _ => panic!("variable index access into target of type {}", ty),
            }
        };
        let dummy = match *target_ty {
            llhd::PointerType(ref ty) => self
                .emit_named_inst("dummy", llhd::VariableInst(single_element_ty(ty)))
                .into(),
            llhd::SignalType(ref ty) => self
                .emit_named_inst("dummy", llhd::SignalInst(single_element_ty(ty), None))
                .into(),
            _ => llhd::const_zero(&single_element_ty(&target_ty)).into(),
        };
        let shifted = self
            .emit_nameless_inst(llhd::ShiftInst(
                llhd::ShiftDir::Right,
                target_ty.clone(),
                target,
                dummy,
                shift,
            ))
            .into();
        let sliced = match mode {
            hir::IndexMode::One(_) => self
                .emit_named_inst(
                    format!("{}.element", basename),
                    llhd::ExtractInst(target_ty, shifted, llhd::SliceMode::Element(0)),
                )
                .into(),
            hir::IndexMode::Many(_, _, delta) => {
                let delta = self.constant_int_value_of(delta, env)?.to_usize().unwrap();
                self.emit_named_inst(
                    format!("{}.slice", basename),
                    llhd::ExtractInst(target_ty, shifted, llhd::SliceMode::Slice(0, delta)),
                )
                .into()
            }
        };
        Ok(sliced)
    }

    /// Emit the code to perform a reduction operation.
    fn emit_reduction(
        &mut self,
        target: NodeId,
        env: ParamEnv,
        op: llhd::BinaryOp,
        negate: bool,
    ) -> Result<llhd::ValueRef> {
        let input_ty = self.type_of(target, env)?;
        let input_bits = bit_size_of_type(self.cx, input_ty, env)?;
        let input_ty = self.emit_type(input_ty, env)?;
        let input_value = self.emit_rvalue(target, env)?;
        let mut result: llhd::ValueRef = self
            .emit_nameless_inst(llhd::ExtractInst(
                input_ty.clone(),
                input_value.clone(),
                llhd::SliceMode::Element(0),
            ))
            .into();
        let bit_ty = self.llhd_type(&result);
        for i in 1..input_bits {
            let bit = self
                .emit_nameless_inst(llhd::ExtractInst(
                    input_ty.clone(),
                    input_value.clone(),
                    llhd::SliceMode::Element(i),
                ))
                .into();
            result = self
                .emit_nameless_inst(llhd::BinaryInst(op, bit_ty.clone(), result, bit))
                .into();
        }
        if negate {
            Ok(self
                .emit_nameless_inst(llhd::UnaryInst(llhd::UnaryOp::Not, bit_ty, result))
                .into())
        } else {
            Ok(result)
        }
    }

    /// Emit a binary shift operator.
    fn emit_shift_operator(
        &mut self,
        dir: llhd::ShiftDir,
        arith: bool,
        ty: llhd::Type,
        lhs: llhd::ValueRef,
        rhs: llhd::ValueRef,
    ) -> llhd::InstKind {
        let insert = match *ty {
            llhd::IntType(w) if arith && dir == llhd::ShiftDir::Right => self
                .emit_nameless_inst(llhd::ExtractInst(
                    ty.clone(),
                    lhs.clone(),
                    llhd::SliceMode::Element(w - 1),
                ))
                .into(),
            llhd::IntType(_) => llhd::const_int(1, num::zero()).into(),
            _ => panic!(
                "shift operator on target of type {}; target is {:?}",
                ty, lhs
            ),
        };
        llhd::ShiftInst(dir, ty, lhs, insert, rhs)
    }
}

/// A generator for statements.
///
/// This trait is implemented by everything that can accept the code emitted for
/// a statement. This excludes entities which have no means for control flow.
trait StmtGenerator<'a, 'gcx, C>: ExprGenerator<'a, 'gcx, C>
where
    C: Context<'gcx> + 'a,
{
    /// Change the insertion point for new instructions.
    fn set_insertion_point(&mut self, pos: llhd::InstPosition);

    /// Get the insertion point for new instructions.
    fn insertion_point(&self) -> llhd::InstPosition;

    /// Add a block.
    fn add_block(&mut self, block: llhd::Block, pos: llhd::BlockPosition) -> llhd::BlockRef;

    /// Append new instructions at the end of a block.
    fn append_to_block(&mut self, block: llhd::BlockRef) {
        self.set_insertion_point(llhd::InstPosition::BlockEnd(block));
    }

    /// Add a nameless block.
    fn add_nameless_block(&mut self) -> llhd::BlockRef {
        self.add_block(llhd::Block::new(None), llhd::BlockPosition::End)
    }

    /// Add a named block.
    fn add_named_block(&mut self, name: impl Into<String>) -> llhd::BlockRef {
        self.add_block(
            llhd::Block::new(Some(name.into())),
            llhd::BlockPosition::End,
        )
    }

    /// Emit the code for a statement.
    fn emit_stmt(&mut self, stmt_id: NodeId, env: ParamEnv) -> Result<()> {
        match self.hir_of(stmt_id)? {
            HirNode::Stmt(x) => self.emit_stmt_regular(stmt_id, x, env),
            HirNode::VarDecl(x) => self.emit_stmt_var_decl(stmt_id, x, env),
            _ => unreachable!(),
        }
    }

    /// Emit the code for a statement, given its HIR.
    fn emit_stmt_regular(
        &mut self,
        _stmt_id: NodeId,
        hir: &hir::Stmt,
        env: ParamEnv,
    ) -> Result<()> {
        #[allow(unreachable_patterns)]
        match hir.kind {
            hir::StmtKind::Null => (),
            hir::StmtKind::Block(ref ids) => {
                for &id in ids {
                    self.emit_stmt(id, env)?;
                }
            }
            hir::StmtKind::Assign { lhs, rhs, kind } => {
                let rhs_value = self.emit_rvalue(rhs, env)?;
                match kind {
                    hir::AssignKind::Block(ast::AssignOp::Identity) => {
                        self.emit_blocking_assign(lhs, rhs_value, env)?;
                    }
                    hir::AssignKind::Block(op) => {
                        let lhs_value = self.emit_rvalue(lhs, env)?;
                        let ty = self.type_of(lhs, env)?;
                        let ty = self.emit_type(ty, env)?;
                        let binop = |op| -> llhd::InstKind {
                            llhd::BinaryInst(op, ty.clone(), lhs_value.clone(), rhs_value.clone())
                        };
                        let mut shift = |dir, arith| -> llhd::InstKind {
                            self.emit_shift_operator(
                                dir,
                                arith,
                                ty.clone(),
                                lhs_value.clone(),
                                rhs_value.clone(),
                            )
                        };
                        let inst = match op {
                            ast::AssignOp::Identity => unreachable!(),
                            ast::AssignOp::Add => binop(llhd::BinaryOp::Add),
                            ast::AssignOp::Sub => binop(llhd::BinaryOp::Sub),
                            ast::AssignOp::Mul => binop(llhd::BinaryOp::Mul),
                            ast::AssignOp::Div => binop(llhd::BinaryOp::Div),
                            ast::AssignOp::Mod => binop(llhd::BinaryOp::Mod),
                            ast::AssignOp::BitAnd => binop(llhd::BinaryOp::And),
                            ast::AssignOp::BitOr => binop(llhd::BinaryOp::Or),
                            ast::AssignOp::BitXor => binop(llhd::BinaryOp::Xor),
                            ast::AssignOp::LogicShL => shift(llhd::ShiftDir::Left, false),
                            ast::AssignOp::LogicShR => shift(llhd::ShiftDir::Right, false),
                            ast::AssignOp::ArithShL => shift(llhd::ShiftDir::Left, true),
                            ast::AssignOp::ArithShR => shift(llhd::ShiftDir::Right, true),
                        };
                        let value = self.emit_nameless_inst(inst).into();
                        self.emit_blocking_assign(lhs, value, env)?;
                    }
                    hir::AssignKind::Nonblock => {
                        let lhs_value = self.emit_lvalue(lhs, env)?;
                        let delay = llhd::const_time(num::zero(), 1, 0).into();
                        self.emit_nameless_inst(llhd::DriveInst(lhs_value, rhs_value, Some(delay)));
                    }
                    hir::AssignKind::NonblockDelay(delay) => {
                        let lhs_value = self.emit_lvalue(lhs, env)?;
                        let delay = self.emit_rvalue(delay, env)?;
                        self.emit_nameless_inst(llhd::DriveInst(lhs_value, rhs_value, Some(delay)));
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
                let resume_blk = self.add_nameless_block();
                let duration = self.emit_rvalue(expr_id, env)?.into();
                self.emit_nameless_inst(llhd::WaitInst(resume_blk, Some(duration), vec![]));
                self.append_to_block(resume_blk);
                self.emit_stmt(stmt, env)?;
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
                let init_blk = self.add_named_block("init");
                self.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(
                    init_blk.into(),
                )));
                self.append_to_block(init_blk);
                let mut init_values = vec![];
                for event in &expr_hir.events {
                    init_values.push(self.emit_rvalue(event.expr, env)?);
                }

                // Wait for any of the inputs to those expressions to change.
                let check_blk = self.add_named_block("check");
                let mut trigger_on = vec![];
                for event in &expr_hir.events {
                    let acc = self.accessed_nodes(event.expr)?;
                    for &id in &acc.read {
                        trigger_on.push(self.emitted_value(id).clone());
                    }
                }
                self.emit_nameless_inst(llhd::WaitInst(check_blk, None, trigger_on));
                self.append_to_block(check_blk);

                // Check if any of the events happened and produce a single bit
                // value that represents this.
                let mut event_cond = None;
                for (event, init_value) in expr_hir.events.iter().zip(init_values.into_iter()) {
                    trace!(
                        "would now emit check if {:?} changed according to {:#?}",
                        init_value,
                        event
                    );
                    let now_value = self.emit_rvalue(event.expr, env)?;
                    let mut trigger = self.emit_event_trigger(event.edge, init_value, now_value)?;
                    for &iff in &event.iff {
                        let iff_value = self.emit_rvalue(iff, env)?;
                        trigger = self
                            .emit_named_inst(
                                "iff",
                                llhd::BinaryInst(
                                    llhd::BinaryOp::And,
                                    llhd::int_ty(1),
                                    trigger,
                                    iff_value,
                                ),
                            )
                            .into();
                    }
                    event_cond = Some(match event_cond {
                        Some(chain) => self
                            .emit_named_inst(
                                "event_or",
                                llhd::BinaryInst(
                                    llhd::BinaryOp::Or,
                                    llhd::int_ty(1),
                                    chain,
                                    trigger,
                                ),
                            )
                            .into(),
                        None => trigger,
                    });
                }

                // If the event happened, branch to a new block which will
                // contain the subsequent statements. Otherwise jump back up to
                // the initial block.
                if let Some(event_cond) = event_cond {
                    let event_blk = self.add_named_block("event");
                    self.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Cond(
                        event_cond,
                        event_blk.into(),
                        init_blk.into(),
                    )));
                    self.append_to_block(event_blk);
                }

                // Emit the actual statement.
                self.emit_stmt(stmt, env)?;
            }
            hir::StmtKind::Expr(expr_id) => {
                self.emit_rvalue(expr_id, env)?;
            }
            hir::StmtKind::If {
                cond,
                main_stmt,
                else_stmt,
            } => {
                let main_blk = self.add_named_block("if_true");
                let else_blk = self.add_named_block("if_false");
                let cond = self.emit_rvalue(cond, env)?;
                self.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Cond(
                    cond,
                    main_blk.into(),
                    else_blk.into(),
                )));
                let final_blk = self.add_named_block("if_exit");
                self.append_to_block(main_blk);
                self.emit_stmt(main_stmt, env)?;
                self.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(
                    final_blk.into(),
                )));
                self.append_to_block(else_blk);
                if let Some(else_stmt) = else_stmt {
                    self.emit_stmt(else_stmt, env)?;
                };
                self.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(
                    final_blk.into(),
                )));
                self.append_to_block(final_blk);
            }
            hir::StmtKind::Loop { kind, body } => {
                let body_blk = self.add_named_block("loop_body");
                let exit_blk = self.add_named_block("loop_exit");

                // Emit the loop initialization.
                let repeat_var = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(count) => {
                        let ty = self.type_of(count, env)?;
                        let lty = self.emit_type(ty, env)?;
                        let count = self.emit_rvalue(count, env)?;
                        let var: llhd::ValueRef = self
                            .emit_named_inst("loop_count", llhd::VariableInst(lty.clone()))
                            .into();
                        self.emit_nameless_inst(llhd::StoreInst(lty, var.clone(), count));
                        Some((var, ty))
                    }
                    hir::LoopKind::While(_) => None,
                    hir::LoopKind::Do(_) => None,
                    hir::LoopKind::For(init, _, _) => {
                        self.emit_stmt(init, env)?;
                        None
                    }
                };

                // Emit the loop prologue.
                self.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Uncond(
                    body_blk.into(),
                )));
                self.append_to_block(body_blk);
                let enter_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let lty = self.emit_type(ty, env)?;
                        let value = self
                            .emit_nameless_inst(llhd::LoadInst(lty.clone(), repeat_var))
                            .into();
                        Some(
                            self.emit_nameless_inst(llhd::CompareInst(
                                llhd::CompareOp::Neq,
                                lty.clone(),
                                value,
                                llhd::const_zero(&lty).into(),
                            ))
                            .into(),
                        )
                    }
                    hir::LoopKind::While(cond) => Some(self.emit_rvalue(cond, env)?),
                    hir::LoopKind::Do(_) => None,
                    hir::LoopKind::For(_, cond, _) => Some(self.emit_rvalue(cond, env)?),
                };
                if let Some(enter_cond) = enter_cond {
                    let entry_blk = self.add_named_block("loop_continue");
                    self.emit_nameless_inst(llhd::BranchInst(llhd::BranchKind::Cond(
                        enter_cond,
                        entry_blk.into(),
                        exit_blk.into(),
                    )));
                    self.append_to_block(entry_blk);
                }

                // Emit the loop body.
                self.emit_stmt(body, env)?;

                // Emit the epilogue.
                let continue_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let lty = self.emit_type(ty, env)?;
                        let value = self
                            .emit_nameless_inst(llhd::LoadInst(lty.clone(), repeat_var.clone()))
                            .into();
                        let one = self.const_one_for_type(ty)?;
                        let value = self
                            .emit_nameless_inst(llhd::BinaryInst(
                                llhd::BinaryOp::Sub,
                                lty.clone(),
                                value,
                                one,
                            ))
                            .into();
                        self.emit_nameless_inst(llhd::StoreInst(lty, repeat_var, value));
                        None
                    }
                    hir::LoopKind::While(_) => None,
                    hir::LoopKind::Do(cond) => Some(self.emit_rvalue(cond, env)?),
                    hir::LoopKind::For(_, _, step) => {
                        self.emit_rvalue(step, env)?;
                        None
                    }
                };
                self.emit_nameless_inst(llhd::BranchInst(match continue_cond {
                    Some(cond) => llhd::BranchKind::Cond(cond, body_blk.into(), exit_blk.into()),
                    None => llhd::BranchKind::Uncond(body_blk.into()),
                }));
                self.append_to_block(exit_blk);
            }
            hir::StmtKind::InlineGroup { ref stmts, .. } => {
                for &stmt in stmts {
                    self.emit_stmt(stmt, env)?;
                }
            }
            _ => return self.unimp_msg("code generation for", hir),
        }
        Ok(())
    }

    /// Emit the code for a variable declaration statement, given its HIR.
    fn emit_stmt_var_decl(
        &mut self,
        decl_id: NodeId,
        hir: &hir::VarDecl,
        env: ParamEnv,
    ) -> Result<()> {
        let ty = self.type_of(decl_id, env)?;
        let ty = self.emit_type(ty, env)?;
        let id = self.emit_named_inst(hir.name.value, llhd::VariableInst(ty.clone()));
        self.set_emitted_value(decl_id, id.into());
        if let Some(expr) = hir.init {
            let k = self.constant_value_of(expr, env)?;
            let k = self.emit_const(k)?;
            self.emit_nameless_inst(llhd::StoreInst(ty, id.into(), k.into()));
        }
        Ok(())
    }

    /// Emit the code to check if a certain edge occurred between two values.
    fn emit_event_trigger(
        &mut self,
        edge: ast::EdgeIdent,
        prev: llhd::ValueRef,
        now: llhd::ValueRef,
    ) -> Result<llhd::ValueRef> {
        let ty = self.llhd_type(&now);

        // Check if a posedge happened.
        let posedge = match edge {
            ast::EdgeIdent::Posedge | ast::EdgeIdent::Edge => {
                let prev_eq_0 = self
                    .emit_nameless_inst(llhd::CompareInst(
                        llhd::CompareOp::Eq,
                        ty.clone(),
                        prev.clone(),
                        llhd::const_zero(&ty).into(),
                    ))
                    .into();
                let now_neq_0 = self
                    .emit_nameless_inst(llhd::CompareInst(
                        llhd::CompareOp::Neq,
                        ty.clone(),
                        now.clone(),
                        llhd::const_zero(&ty).into(),
                    ))
                    .into();
                Some(
                    self.emit_named_inst(
                        "posedge",
                        llhd::BinaryInst(
                            llhd::BinaryOp::And,
                            llhd::int_ty(1),
                            prev_eq_0,
                            now_neq_0,
                        ),
                    )
                    .into(),
                )
            }
            _ => None,
        };

        // Check if a negedge happened.
        let negedge = match edge {
            ast::EdgeIdent::Negedge | ast::EdgeIdent::Edge => {
                let now_eq_0 = self
                    .emit_nameless_inst(llhd::CompareInst(
                        llhd::CompareOp::Eq,
                        ty.clone(),
                        now.clone(),
                        llhd::const_zero(&ty).into(),
                    ))
                    .into();
                let prev_neq_0 = self
                    .emit_nameless_inst(llhd::CompareInst(
                        llhd::CompareOp::Neq,
                        ty.clone(),
                        prev.clone(),
                        llhd::const_zero(&ty).into(),
                    ))
                    .into();
                Some(
                    self.emit_named_inst(
                        "negedge",
                        llhd::BinaryInst(
                            llhd::BinaryOp::And,
                            llhd::int_ty(1),
                            now_eq_0,
                            prev_neq_0,
                        ),
                    )
                    .into(),
                )
            }
            _ => None,
        };

        // Combine the two edge triggers, or emit an implicit edge check if none
        // of the above edges was checked.
        Ok(match (posedge, negedge) {
            (Some(a), Some(b)) => self
                .emit_named_inst(
                    "edge",
                    llhd::BinaryInst(llhd::BinaryOp::Or, llhd::int_ty(1), a, b),
                )
                .into(),
            (Some(a), None) => a,
            (None, Some(b)) => b,
            (None, None) => self
                .emit_named_inst(
                    "impledge",
                    llhd::CompareInst(llhd::CompareOp::Neq, ty, prev, now),
                )
                .into(),
        })
    }

    /// Emit a blocking assignment to a variable or signal.
    fn emit_blocking_assign(
        &mut self,
        lvalue_id: NodeId,
        rvalue: llhd::ValueRef,
        env: ParamEnv,
    ) -> Result<()> {
        let lvalue = self.emit_lvalue(lvalue_id, env)?;
        let lty = self.llhd_type(&lvalue);
        let rty = self.llhd_type(&rvalue);
        match *lty {
            llhd::SignalType(..) => {
                let one_epsilon = llhd::const_time(num::zero(), num::zero(), num::one());
                self.emit_nameless_inst(llhd::DriveInst(
                    lvalue,
                    rvalue,
                    Some(one_epsilon.clone().into()),
                ));
                // Emit a wait statement to allow for the assignment to take
                // effect.
                let blk = self.add_nameless_block();
                self.emit_nameless_inst(llhd::WaitInst(blk, Some(one_epsilon.into()), vec![]));
                self.append_to_block(blk);
            }
            llhd::PointerType(..) => {
                self.emit_nameless_inst(llhd::StoreInst(rty, lvalue, rvalue));
            }
            ref t => panic!("value of type `{}` cannot be driven", t),
        }
        Ok(())
    }
}

struct DummyStmtGenerator<'a, 'gcx, C>(std::marker::PhantomData<(&'a (), &'gcx (), C)>);

impl<'a, 'gcx, C> Deref for DummyStmtGenerator<'a, 'gcx, C> {
    type Target = CodeGenerator<'gcx, C>;

    fn deref(&self) -> &CodeGenerator<'gcx, C> {
        unreachable!()
    }
}

impl<'a, 'gcx, C> DerefMut for DummyStmtGenerator<'a, 'gcx, C> {
    fn deref_mut(&mut self) -> &mut CodeGenerator<'gcx, C> {
        unreachable!()
    }
}

impl<'a, 'b, 'gcx, C> ExprGenerator<'a, 'gcx, C> for DummyStmtGenerator<'b, 'gcx, &'a C>
where
    C: Context<'gcx> + 'a,
{
    type AsStmtGen = Self;

    fn emit_inst(&mut self, _inst: llhd::Inst) -> llhd::InstRef {
        unreachable!()
    }

    fn emitted_value(&self, _node_id: NodeId) -> &llhd::ValueRef {
        unreachable!()
    }

    fn set_emitted_value(&mut self, _node_id: NodeId, _value: llhd::ValueRef) {
        unreachable!()
    }

    fn with_llhd_context<F, R>(&self, _f: F) -> R
    where
        F: FnOnce(&dyn llhd::Context) -> R,
    {
        unreachable!()
    }
}

impl<'a, 'b, 'gcx, C> StmtGenerator<'a, 'gcx, C> for DummyStmtGenerator<'b, 'gcx, &'a C>
where
    C: Context<'gcx> + 'a,
{
    fn set_insertion_point(&mut self, _pos: llhd::InstPosition) {
        unreachable!()
    }

    fn insertion_point(&self) -> llhd::InstPosition {
        unreachable!()
    }

    fn add_block(&mut self, _block: llhd::Block, _pos: llhd::BlockPosition) -> llhd::BlockRef {
        unreachable!()
    }
}

/// An rvalue emission mode.
///
/// Upon code emission, rvalues may be emitted either as direct values,
/// pointers, or signals. This enum is used to communicate the intent to the
/// corresopnding functions.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Mode {
    Value,
    // Pointer,
    Signal,
}

// Copyright (c) 2016-2019 Fabian Schuiki

//! This module implements LLHD code generation.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{Type, TypeKind},
    value::{Value, ValueKind},
    ParamEnv, ParamEnvSource,
};
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
    module_defs: HashMap<NodeEnvId, Result<llhd::value::EntityRef>>,
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
    pub fn emit_module(&mut self, id: NodeId) -> Result<llhd::value::EntityRef> {
        self.emit_module_with_env(id, self.default_param_env())
    }

    /// Emit the code for a module and all its dependent modules.
    pub fn emit_module_with_env(
        &mut self,
        id: NodeId,
        env: ParamEnv,
    ) -> Result<llhd::value::EntityRef> {
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
        let mut port_map = HashMap::new();
        for (index, port_id) in inputs.into_iter().enumerate() {
            ent.inputs_mut()[index].set_name(port_id_to_name[&port_id].value);
            port_map.insert(port_id, ent.input(index));
        }
        for (index, &port_id) in outputs.iter().enumerate() {
            ent.outputs_mut()[index].set_name(port_id_to_name[&port_id].value);
            port_map.insert(port_id, ent.output(index));
        }

        // Emit instantiations.
        for &inst_id in hir.insts {
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
            debug!("{:?} = {:#?}", inst_env, self.param_env_data(inst_env));
            let target = self.emit_module_with_env(resolved, inst_env)?;
            let ty = self.tables.module_types[&(resolved, inst_env)].clone();
            let inst = llhd::Inst::new(
                Some(hir.name.value.into()),
                llhd::InstanceInst(ty, target.into(), vec![], vec![]),
            );
            ent.add_inst(inst, llhd::InstPosition::End);
        }

        // Emit declarations.
        for &decl_id in hir.decls {
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
            ent.add_inst(inst, llhd::InstPosition::End);
        }

        // Assign default values to undriven output ports.
        for port_id in outputs {
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
                llhd::DriveInst(port_map[&port_id].into(), default_value.into(), None),
            );
            ent.add_inst(inst, llhd::InstPosition::End);
        }

        // Emit and instantiate procedures.
        for &proc_id in hir.procs {
            let _prok = self.emit_procedure(proc_id, env)?;
            // TODO: instantiate procedure and wire up relevant signals
        }

        let result = Ok(self.into.add_entity(ent));
        self.tables.module_defs.insert((id, env), result.clone());
        result
    }

    /// Emit the code for a procedure.
    fn emit_procedure(&mut self, id: NodeId, env: ParamEnv) -> Result<llhd::value::ProcessRef> {
        // Create process and entry block.
        let mut prok = llhd::Process::new(format!("{:?}", id), llhd::entity_ty(vec![], vec![]));
        let entry_blk = prok
            .body_mut()
            .add_block(llhd::Block::new(None), llhd::block::BlockPosition::Begin);
        let hir = match self.hir_of(id)? {
            HirNode::Proc(x) => x,
            _ => unreachable!(),
        };

        // Emit statements.
        let final_blk = self.emit_stmt(hir.stmt, env, &mut prok, entry_blk)?;

        // Emit epilogue.
        match hir.kind {
            ast::ProcedureKind::Initial => {
                prok.body_mut().add_inst(
                    llhd::Inst::new(None, llhd::HaltInst),
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
            (&TypeKind::Bit(_), &ValueKind::Int(ref k)) => Ok(llhd::const_int(1, k.clone())),
            _ => panic!("invalid type/value combination {:#?}", value),
        }
    }

    /// Emit the code for a statement.
    fn emit_stmt(
        &mut self,
        stmt_id: NodeId,
        _env: ParamEnv,
        _prok: &mut llhd::Process,
        block: llhd::value::BlockRef,
    ) -> Result<llhd::value::BlockRef> {
        let hir = match self.hir_of(stmt_id)? {
            _ => unreachable!(),
        };
        Ok(block)
    }
}

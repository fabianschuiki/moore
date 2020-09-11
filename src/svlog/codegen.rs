// Copyright (c) 2016-2020 Fabian Schuiki

//! This module implements LLHD code generation.

use crate::{
    crate_prelude::*,
    hir::{AccessedNode, HirNode},
    port_list::PortList,
    resolver::InstTarget,
    ty::UnpackedType,
    value::{Value, ValueKind},
    ParamEnv,
};
use num::{BigInt, One, ToPrimitive, Zero};
use std::{
    collections::{HashMap, HashSet},
    iter::{once, repeat},
    ops::{Deref, DerefMut},
    rc::Rc,
};

/// A code generator.
///
/// Use this struct to emit LLHD code for nodes in a [`Context`].
pub struct CodeGenerator<'gcx, C> {
    /// The compilation context.
    cx: C,
    /// The LLHD module to be populated.
    into: llhd::ir::Module,
    /// Tables holding mappings and interned values.
    tables: Tables<'gcx>,
}

impl<'gcx, C> CodeGenerator<'gcx, C> {
    /// Create a new code generator.
    pub fn new(cx: C) -> Self {
        CodeGenerator {
            cx,
            into: llhd::ir::Module::new(),
            tables: Default::default(),
        }
    }

    /// Finalize code generation and return the generated LLHD module.
    pub fn finalize(self) -> llhd::ir::Module {
        self.into
    }
}

#[derive(Default)]
struct Tables<'gcx> {
    module_defs: HashMap<NodeEnvId, Result<Rc<EmittedModule<'gcx>>>>,
    module_signatures: HashMap<NodeEnvId, (llhd::ir::UnitName, llhd::ir::Signature)>,
    interned_types: HashMap<&'gcx UnpackedType<'gcx>, Result<llhd::Type>>,
}

impl<'gcx, C> Deref for CodeGenerator<'gcx, C> {
    type Target = C;

    fn deref(&self) -> &C {
        &self.cx
    }
}

impl<'a, 'gcx, C: Context<'gcx>> CodeGenerator<'gcx, &'a C> {
    /// Emit the code for a module and all its dependent modules.
    pub fn emit_module(&mut self, id: NodeId) -> Result<Rc<EmittedModule<'gcx>>> {
        self.emit_module_with_env(id, self.default_param_env())
    }

    /// Emit the code for a module and all its dependent modules.
    pub fn emit_module_with_env(
        &mut self,
        id: NodeId,
        env: ParamEnv,
    ) -> Result<Rc<EmittedModule<'gcx>>> {
        if let Some(x) = self.tables.module_defs.get(&id.env(env)) {
            return x.clone();
        }
        let hir = match self.hir_of(id)? {
            HirNode::Module(m) => m,
            _ => panic!("expected {:?} to be a module", id),
        };
        info!("Emit module `{}` with {:?}", hir.name, env);

        // Emit detailed port information if requested.
        if self.sess().has_verbosity(Verbosity::PORTS) {
            emit_port_details(self.cx, hir, env);
        }

        // Determine entity type and port names.
        let ports = self.determine_module_ports(&hir.ports_new.int, env)?;

        // Pick an entity name.
        let mut entity_name: String = hir.name.value.into();
        if env != self.default_param_env() {
            entity_name.push_str(&format!(".param{}", env.0));
        }
        let name = llhd::ir::UnitName::Global(entity_name.clone());

        // Create entity.
        let mut ent =
            llhd::ir::UnitData::new(llhd::ir::UnitKind::Entity, name.clone(), ports.sig.clone());
        let mut builder = llhd::ir::UnitBuilder::new_anonymous(&mut ent);
        self.tables
            .module_signatures
            .insert(id.env(env), (name, ports.sig.clone()));
        let mut values = HashMap::new();
        let mut gen = UnitGenerator {
            gen: self,
            builder: &mut builder,
            values: &mut values,
            interned_consts: Default::default(),
            interned_lvalues: Default::default(),
            interned_rvalues: Default::default(),
            shadows: Default::default(),
        };

        // Assign proper port names and collect ports into a lookup table.
        for (index, port) in ports.inputs.iter().enumerate() {
            let arg = gen.builder.input_arg(index);
            gen.builder.set_name(arg, port.name.clone());
            gen.values.insert(port.accnode, arg);
        }
        for (index, port) in ports.outputs.iter().enumerate() {
            let arg = gen.builder.output_arg(index);
            gen.builder.set_name(arg, port.name.clone());
            gen.values.insert(port.accnode, arg);
        }

        debug!("  Ports:");
        for (node, value) in gen.values.iter() {
            debug!(
                "    {:?} = {:?} (type {})",
                node,
                value,
                gen.llhd_type(*value)
            );
        }

        // Emit the actual contents of the entity.
        gen.emit_module_block(id, env, &hir.block, &entity_name)?;

        // Assign default values to undriven output ports.
        for port in ports.outputs.iter() {
            let value = gen.values[&port.accnode];
            let driven = gen
                .builder
                .all_insts()
                .any(|inst| match gen.builder[inst].opcode() {
                    llhd::ir::Opcode::Drv => gen.builder[inst].args()[0] == value,
                    llhd::ir::Opcode::Inst => gen.builder[inst].output_args().contains(&value),
                    _ => false,
                });
            if driven {
                continue;
            }
            let default_value = gen.emit_const(
                if let Some(default) = port.default {
                    gen.constant_value_of(default, env)
                } else {
                    gen.type_default_value(port.ty)
                },
                env,
                port.port.span(),
            )?;
            let zero_time = llhd::value::TimeValue::new(num::zero(), 0, 0);
            let zero_time = gen.builder.ins().const_time(zero_time);
            gen.builder
                .ins()
                .drv(gen.values[&port.accnode], default_value, zero_time);
        }

        let unit = self.into.add_unit(ent);
        let result = Ok(Rc::new(EmittedModule { unit, ports }));
        self.tables.module_defs.insert(id.env(env), result.clone());
        result
    }

    fn determine_module_ports(
        &mut self,
        ports: &'gcx [port_list::IntPort<'gcx>],
        env: ParamEnv,
    ) -> Result<ModuleIntf<'gcx>> {
        debug!("Determining ports with {:?}", env);
        let mut sig = llhd::ir::Signature::new();
        let mut inputs = vec![];
        let mut outputs = vec![];

        // Go through the ports and expand each to one or more entity inputs and
        // outputs.
        for port in ports {
            let ty = self.type_of_int_port(Ref(port), env);
            debug!("  Port `{}` has type `{}`", port.name, ty);

            // Distinguish interfaces and regular ports.
            if let Some(intf) = ty.resolve_full().core.get_interface() {
                trace!("    Expanding interface {:?}", intf);

                // If a modport was specified, make a list of directions for
                // each port by name.
                let mut dirs = HashMap::new();
                for port in intf.modport.iter().flat_map(|modport| modport.ports.iter()) {
                    match port.data {
                        ast::ModportPortData::Simple { dir, ref port } => {
                            for port_name in port {
                                if port_name.expr.is_none() {
                                    dirs.insert(port_name.name.value, dir.value);
                                }
                            }
                        }
                    }
                }
                trace!("    Modport-derived directions: {:?}", dirs);

                let signals = self.determine_interface_signals(intf, &ty.dims)?;
                for signal in signals {
                    let llty = llhd::signal_ty(self.emit_type(signal.ty)?);
                    let name = format!("{}.{}", port.name, signal.name);
                    trace!("    Signal `{}` of type `{}` / `{}`", name, signal.ty, llty);
                    let port = ModulePort {
                        port,
                        ty: signal.ty,
                        name,
                        accnode: AccessedNode::Intf(port.id, signal.decl_id),
                        default: signal.default,
                        kind: ModulePortKind::IntfSignal {
                            intf: intf.ast,
                            env: intf.env,
                            decl_id: signal.decl_id,
                        },
                    };
                    match dirs.get(&signal.name.value).copied() {
                        Some(ast::PortDir::Input) | Some(ast::PortDir::Ref) => {
                            sig.add_input(llty);
                            inputs.push(port);
                        }
                        Some(ast::PortDir::Output) | Some(ast::PortDir::Inout) | None => {
                            sig.add_output(llty);
                            outputs.push(port);
                        }
                    }
                }
            } else {
                trace!("    Regular port");
                let llty = llhd::signal_ty(self.emit_type(ty)?);
                let name = port.name.to_string();
                let mp = ModulePort {
                    port,
                    ty,
                    name,
                    accnode: AccessedNode::Regular(port.id),
                    default: port.data.as_ref().and_then(|pd| pd.default),
                    kind: ModulePortKind::Port,
                };
                match port.dir {
                    ast::PortDir::Input | ast::PortDir::Ref => {
                        sig.add_input(llty);
                        inputs.push(mp);
                    }
                    ast::PortDir::Inout | ast::PortDir::Output => {
                        sig.add_output(llty);
                        outputs.push(mp);
                    }
                }
            }
        }

        debug!("  Signature: {}", sig);

        Ok(ModuleIntf {
            sig,
            inputs,
            outputs,
        })
    }

    /// Map an interface to a list of signals defined by that interface.
    fn determine_interface_signals(
        &mut self,
        intf: &'gcx ty::InterfaceType<'gcx>,
        dims: &'gcx [ty::UnpackedDim<'gcx>],
    ) -> Result<Vec<IntfSignal<'gcx>>> {
        let port_list = self.canonicalize_ports(intf.ast);
        let intf_hir = self.hir_of_interface(intf.ast)?;

        let signals = port_list
            .int
            .iter()
            .map(|p| Ok((p.id, p.name, p.data.as_ref().and_then(|d| d.default))))
            .chain(intf_hir.block.decls.iter().map(|&id| {
                Ok(match self.hir_of(id)? {
                    HirNode::VarDecl(x) => (id, x.name, x.init),
                    _ => unreachable!(),
                })
            }));

        let mut result = vec![];
        for x in signals {
            let (decl_id, name, default) = x?;
            let mut sig_ty = self.type_of(decl_id, intf.env)?.clone();
            sig_ty.dims.extend(dims);
            let sig_ty = sig_ty.intern(self.cx);
            result.push(IntfSignal {
                decl_id,
                ty: sig_ty,
                name,
                default,
            });
        }
        Ok(result)
    }

    /// Emit the code for a procedure.
    fn emit_procedure(
        &mut self,
        id: NodeId,
        env: ParamEnv,
        name_prefix: &str,
    ) -> Result<EmittedProcedure> {
        let hir = match self.hir_of(id)? {
            HirNode::Proc(x) => x,
            _ => unreachable!(),
        };

        // Find the accessed nodes.
        let acc = self.accessed_nodes(hir.stmt, env)?;
        trace!("Process accesses {:#?}", acc);
        let mut sig = llhd::ir::Signature::new();
        let mut inputs = vec![];
        let mut outputs = vec![];
        for &id in acc.read.iter().filter(|id| !acc.written.contains(id)) {
            sig.add_input(llhd::signal_ty(self.emit_type(match id {
                AccessedNode::Regular(id) => self.type_of(id, env)?,
                AccessedNode::Intf(intf, id) => {
                    let intf_ty = self.type_of(intf, env)?;
                    let intf_ty_inner = intf_ty.resolve_full().core.get_interface().unwrap();
                    let mut sig_ty = self.type_of(id, intf_ty_inner.env)?.clone();
                    sig_ty.dims.extend(&intf_ty.dims);
                    sig_ty.intern(self.cx)
                }
            })?));
            inputs.push(id);
        }
        for &id in acc.written.iter() {
            sig.add_output(llhd::signal_ty(self.emit_type(match id {
                AccessedNode::Regular(id) => self.type_of(id, env)?,
                AccessedNode::Intf(intf, id) => {
                    let intf_ty = self.type_of(intf, env)?;
                    let intf_ty_inner = intf_ty.resolve_full().core.get_interface().unwrap();
                    let mut sig_ty = self.type_of(id, intf_ty_inner.env)?.clone();
                    sig_ty.dims.extend(&intf_ty.dims);
                    sig_ty.intern(self.cx)
                }
            })?));
            outputs.push(id);
        }
        trace!("Process Inputs: {:?}", inputs);
        trace!("Process Outputs: {:?}", outputs);
        trace!("Process Signature: {}", sig);
        trace!("Process Env: {:?}", self.param_env_data(env));

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
        let mut prok = llhd::ir::UnitData::new(
            llhd::ir::UnitKind::Process,
            llhd::ir::UnitName::Local(proc_name),
            sig,
        );
        let mut builder = llhd::ir::UnitBuilder::new_anonymous(&mut prok);

        // Assign names to inputs and outputs.
        let guess_name = |id| {
            let (prefix, id) = match id {
                AccessedNode::Regular(id) => (None, id),
                AccessedNode::Intf(inst_id, id) => {
                    let inst_name = match self.hir_of(inst_id).ok()? {
                        HirNode::IntPort(x) => Some(x.name),
                        HirNode::Inst(x) => Some(x.name),
                        _ => None,
                    };
                    (inst_name, id)
                }
            };
            let name = match self.hir_of(id).ok()? {
                HirNode::VarDecl(x) => Some(x.name),
                HirNode::IntPort(x) => Some(x.name),
                _ => None,
            };
            match (prefix, name) {
                (Some(prefix), Some(name)) => Some(format!("{}.{}", prefix, name)),
                (None, Some(name)) => Some(format!("{}", name)),
                _ => None,
            }
        };
        for (i, &id) in inputs.iter().enumerate() {
            if let Some(name) = guess_name(id) {
                let value = builder.input_arg(i);
                builder.set_name(value, name);
            }
        }
        for (i, &id) in outputs.iter().enumerate() {
            if let Some(name) = guess_name(id) {
                let value = builder.output_arg(i);
                builder.set_name(value, name);
            }
        }

        // Create a mapping from read/written nodes to process parameters.
        let mut values = HashMap::new();
        for (&id, arg) in inputs
            .iter()
            .zip(builder.input_args())
            .chain(outputs.iter().zip(builder.output_args()))
        {
            values.insert(id.into(), arg);
        }
        let mut pg = UnitGenerator {
            gen: self,
            builder: &mut builder,
            values: &mut values,
            interned_consts: Default::default(),
            interned_lvalues: Default::default(),
            interned_rvalues: Default::default(),
            shadows: Default::default(),
        };
        let entry_blk = pg.add_nameless_block();
        pg.builder.append_to(entry_blk);

        // Determine which values are both read and written. These require
        // shadow variables to emulate the expected behaviour under blocking
        // assignments.
        let input_set: HashSet<_> = acc.read.iter().cloned().collect();
        let output_set: HashSet<_> = acc.written.iter().cloned().collect();
        for &id in input_set.intersection(&output_set) {
            let init = pg.builder.ins().prb(pg.values[&id.into()]);
            let shadow = pg.builder.ins().var(init);
            if let Some(name) = pg
                .builder
                .get_name(pg.values[&id.into()])
                .map(|name| format!("{}.shadow", name))
            {
                pg.builder.set_name(shadow, name);
            }
            pg.shadows.insert(id.into(), shadow);
        }

        // Emit prologue and determine which basic block to jump back to.
        let head_blk = match hir.kind {
            ast::ProcedureKind::AlwaysComb | ast::ProcedureKind::AlwaysLatch => {
                let body_blk = pg.add_named_block("body");
                let check_blk = pg.add_named_block("check");
                pg.builder.ins().br(body_blk);
                pg.builder.append_to(check_blk);
                let trigger_on = inputs
                    .iter()
                    .map(|id| pg.emitted_value(*id).clone())
                    .collect();
                pg.builder.ins().wait(body_blk, trigger_on);
                pg.builder.append_to(body_blk);
                pg.flush_mir(); // ensure we don't reuse earlier expr probe
                pg.emit_shadow_update();
                check_blk
            }
            ast::ProcedureKind::Final => {
                // TODO(fschuiki): Replace this with a cleverer way to implement a trigger-on-end.
                let body_blk = pg.add_named_block("body");
                let endtimes = pg.builder.ins().const_time(llhd::value::TimeValue::new(
                    "9001".parse().unwrap(),
                    0,
                    0,
                ));
                pg.builder.set_name(endtimes, "endtimes".to_string());
                pg.builder.ins().wait_time(body_blk, endtimes, vec![]);
                pg.builder.append_to(body_blk);
                pg.flush_mir(); // ensure we don't reuse earlier expr probe
                pg.emit_shadow_update();
                entry_blk // This block is ignored for final blocks
            }
            _ => entry_blk,
        };

        // Emit the main statement.
        pg.emit_stmt(hir.stmt, env)?;

        // Emit epilogue.
        match hir.kind {
            ast::ProcedureKind::Initial => {
                pg.builder.ins().halt();
            }
            ast::ProcedureKind::Always
            | ast::ProcedureKind::AlwaysComb
            | ast::ProcedureKind::AlwaysLatch
            | ast::ProcedureKind::AlwaysFf => {
                pg.builder.ins().br(head_blk);
            }
            ast::ProcedureKind::Final => {
                pg.builder.ins().halt();
            }
        }

        Ok(EmittedProcedure {
            unit: self.into.add_unit(prok),
            inputs,
            outputs,
        })
    }

    /// Map a type to an LLHD type (interned).
    fn emit_type(&mut self, ty: &'gcx UnpackedType<'gcx>) -> Result<llhd::Type> {
        if let Some(x) = self.tables.interned_types.get(&ty) {
            x.clone()
        } else {
            let x = self.emit_type_uninterned(ty);
            self.tables.interned_types.insert(ty, x.clone());
            x
        }
    }

    /// Map a type to an LLHD type.
    fn emit_type_uninterned(&mut self, ty: &'gcx UnpackedType<'gcx>) -> Result<llhd::Type> {
        if ty.is_error() {
            return Err(());
        }
        let ty = ty.resolve_full();

        // Handle things that coalesce easily to scalars.
        if ty.coalesces_to_llhd_scalar() {
            return Ok(llhd::int_ty(ty.get_bit_size().unwrap()));
        }

        // Handle arrays.
        if let Some(dim) = ty.outermost_dim() {
            let size = match dim.get_size() {
                Some(size) => size,
                None => panic!("cannot map unsized array `{}` to LLHD", ty),
            };
            let inner = ty.pop_dim(self.cx).unwrap();
            return Ok(llhd::array_ty(size, self.emit_type(inner)?));
        }

        // Handle structs.
        if let Some(strukt) = ty.get_struct() {
            let mut types = vec![];
            for member in &strukt.members {
                types.push(self.emit_type(member.ty)?);
            }
            return Ok(llhd::struct_ty(types));
        }

        // Handle packed types.
        if let Some(packed) = ty.get_packed() {
            let packed = packed.resolve_full();
            return match packed.core {
                ty::PackedCore::Error => Ok(llhd::void_ty()),
                ty::PackedCore::Void => Ok(llhd::void_ty()),
                ty::PackedCore::IntAtom(ty::IntAtomType::Time) => Ok(llhd::time_ty()),
                ty::PackedCore::Enum(ref enm) => self.emit_type(enm.base.to_unpacked(self.cx)),
                _ => unreachable!("emitting `{}` should have been handled above", packed),
            };
        }

        // Everything else we cannot do.
        error!("Cannot map type {:#?}", ty);
        panic!("cannot map `{}` to LLHD", ty);
    }

    /// Execute the initialization step of a generate loop.
    fn execute_genvar_init(&mut self, id: NodeId, env: ParamEnv) -> Result<ParamEnv> {
        let hir = self.hir_of(id)?;
        match hir {
            HirNode::GenvarDecl(_) => Ok(env),
            HirNode::Stmt(stmt) => match stmt.kind {
                hir::StmtKind::Assign {
                    lhs,
                    rhs,
                    kind: hir::AssignKind::Block(ast::AssignOp::Identity),
                } => {
                    let target_id = self.resolve_node(lhs, env)?;
                    let init_value = self.constant_value_of(rhs, env);
                    let mut env_data = self.param_env_data(env).clone();
                    env_data.set_value(target_id, init_value);
                    Ok(self.intern_param_env(env_data))
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    /// Execute the iteration step of a generate loop.
    fn execute_genvar_step(&mut self, id: NodeId, env: ParamEnv) -> Result<ParamEnv> {
        let hir = self.hir_of(id)?;
        let mut env_data = self.param_env_data(env).clone();
        let next = match hir {
            HirNode::Expr(expr) => match expr.kind {
                hir::ExprKind::Unary(op, target_id) => {
                    let target_id = self.resolve_node(target_id, env)?;
                    let current_value = self.constant_value_of(target_id, env);
                    let next_value = match current_value.kind {
                        ValueKind::Int(ref v, ..) => match op {
                            hir::UnaryOp::PostInc | hir::UnaryOp::PreInc => Some(v + 1),
                            hir::UnaryOp::PostDec | hir::UnaryOp::PreDec => Some(v - 1),
                            _ => None,
                        }
                        .map(|v| value::make_int(current_value.ty, v)),
                        _ => unreachable!(),
                    };
                    next_value.map(|v| (target_id, self.intern_value(v)))
                }
                hir::ExprKind::Assign { .. } => {
                    let mir = self.mir_rvalue(id, env);
                    match mir.kind {
                        mir::RvalueKind::Error => return Err(()),
                        mir::RvalueKind::Assignment { lvalue, rvalue, .. } => {
                            let target_id = match lvalue.kind {
                                mir::LvalueKind::Error => return Err(()),
                                mir::LvalueKind::Genvar(id) => id,
                                _ => unreachable!(),
                            };
                            let next_value = self.const_mir_rvalue(Ref(rvalue));
                            Some((target_id, next_value))
                        }
                        _ => unreachable!(),
                    }
                }
                _ => None,
            },
            _ => None,
        };
        match next {
            Some((target_id, next_value)) => {
                env_data.set_value(target_id, next_value);
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

/// A code generator for functions, processes, and entities.
struct UnitGenerator<'a, 'gcx, C> {
    /// The global code generator.
    gen: &'a mut CodeGenerator<'gcx, C>,
    /// The builder into which instructions are emitted.
    builder: &'a mut llhd::ir::UnitBuilder<'a>,
    /// The emitted LLHD values for various nodes.
    values: &'a mut HashMap<AccessedNode, llhd::ir::Value>,
    /// The constant values emitted into the unit.
    interned_consts: HashMap<Value<'gcx>, Result<llhd::ir::Value>>,
    /// The MIR lvalues emitted into the unit.
    interned_lvalues: HashMap<NodeId, Result<(llhd::ir::Value, Option<llhd::ir::Value>)>>,
    /// The MIR rvalues emitted into the unit.
    interned_rvalues: HashMap<(NodeId, Mode), Result<(llhd::ir::Value, Mode)>>,
    /// The shadow variables introduced to handle signals which are both read
    /// and written in a process.
    shadows: HashMap<AccessedNode, llhd::ir::Value>,
}

impl<'a, 'gcx, C> Deref for UnitGenerator<'a, 'gcx, C> {
    type Target = CodeGenerator<'gcx, C>;

    fn deref(&self) -> &CodeGenerator<'gcx, C> {
        &self.gen
    }
}

impl<'a, 'gcx, C> DerefMut for UnitGenerator<'a, 'gcx, C> {
    fn deref_mut(&mut self) -> &mut CodeGenerator<'gcx, C> {
        &mut self.gen
    }
}

impl<'a, 'b, 'gcx, C> UnitGenerator<'a, 'gcx, &'b C>
where
    C: Context<'gcx> + 'b,
{
    fn emitted_value(&self, src: impl Into<AccessedNode>) -> llhd::ir::Value {
        let src = src.into();
        match self.values.get(&src) {
            Some(&v) => v,
            None => bug_span!(
                self.span(match src {
                    AccessedNode::Regular(id) => id,
                    AccessedNode::Intf(_, id) => id,
                }),
                self.cx,
                "no value emitted for {:?}",
                src
            ),
        }
    }

    fn set_emitted_value(&mut self, src: impl Into<AccessedNode>, value: llhd::ir::Value) {
        let src = src.into();
        self.values.insert(src, value);
    }

    /// Clear the cached MIR lvalues and rvalues. This should be called before
    /// or after emitting an expression, and at least for every statement.
    /// Otherwise MIR codegen might reuse values that have become out-of-date
    /// due to time passing in between statements.
    fn flush_mir(&mut self) {
        self.interned_lvalues.clear();
        self.interned_rvalues.clear();
    }

    /// Emit the code for the contents of a module.
    fn emit_module_block(
        &mut self,
        id: NodeId,
        env: ParamEnv,
        hir: &hir::ModuleBlock,
        name_prefix: &str,
    ) -> Result<()> {
        // Emit declarations.
        for &decl_id in &hir.decls {
            let hir = match self.hir_of(decl_id)? {
                HirNode::VarDecl(x) => x,
                _ => unreachable!(),
            };
            let ty = self.type_of(decl_id, env)?;
            let value = self.emit_varnet_decl(decl_id, ty, env, hir.init)?;
            self.builder.set_name(value, hir.name.value.into());
            self.values.insert(decl_id.into(), value.into());
        }

        // Emit interface instances.
        for &inst_id in &hir.insts {
            // Resolve the instantiation details.
            let inst = match self.hir_of(inst_id)? {
                HirNode::Inst(x) => x,
                _ => unreachable!(),
            };
            let inst = self.inst_details(Ref(inst), env)?;

            // Compute the array dimensions for the signals.
            // let mut dims = vec![];
            let inst_ty = self.type_of_inst(Ref(inst.hir), env);
            let intf_ty = match inst_ty.resolve_full().core.get_interface() {
                Some(x) => x,
                None => continue,
            };
            trace!(
                "Interface instance is of type `{}` ({:?})",
                inst_ty,
                intf_ty
            );

            // Expand the interface declarations.
            let signals = self.determine_interface_signals(intf_ty, &inst_ty.dims)?;
            let mut signal_lookup = HashMap::new();
            for signal in signals {
                let value =
                    self.emit_varnet_decl(signal.decl_id, signal.ty, intf_ty.env, signal.default)?;
                self.builder
                    .set_name(value, format!("{}.{}", inst.hir.name, signal.name));
                let src = AccessedNode::Intf(inst_id, signal.decl_id);
                trace!(
                    "Emitted value for {:?} {}.{}",
                    src,
                    inst.hir.name,
                    signal.name
                );
                self.values.insert(src, value.into());
                signal_lookup.insert(signal.decl_id, value);
            }

            // Generate the code for the port assignments.
            let port_list = self.canonicalize_ports(intf_ty.ast);
            let ports = self.determine_module_ports(&port_list.int, intf_ty.env)?;
            let (inputs, outputs) = self.emit_port_connections(
                port_list,
                inst.as_ref(),
                &ports.inputs,
                &ports.outputs,
            )?;
            trace!("Attaching interface inputs {:?}", inputs);
            trace!("Attaching interface outputs {:?}", outputs);
            trace!("Signal lookup: {:?}", signal_lookup);

            // Actually wire up the ports.
            let inputs = inputs.into_iter().zip(ports.inputs.iter());
            let outputs = outputs.into_iter().zip(ports.outputs.iter());
            for (assigned, port) in inputs.chain(outputs) {
                trace!(
                    "Assign `{}` ({:?}) = {:?}",
                    port.name,
                    port.port.id,
                    assigned
                );
                self.builder
                    .ins()
                    .con(signal_lookup[&port.port.id], assigned);
            }
        }

        // Emit assignments.
        for &assign_id in &hir.assigns {
            let hir = match self.hir_of(assign_id)? {
                HirNode::Assign(x) => x,
                _ => unreachable!(),
            };
            let lhs = self.mir_lvalue(hir.lhs, env);
            let rhs = self.mir_rvalue(hir.rhs, env);
            if lhs.is_error() || rhs.is_error() {
                continue;
            }
            assert_type!(rhs.ty, lhs.ty, rhs.span, self.cx);
            let lhs = self.emit_mir_lvalue(lhs)?.0;
            let rhs = self.emit_mir_rvalue(rhs)?;
            let one_epsilon = llhd::value::TimeValue::new(num::zero(), 0, 1);
            let one_epsilon = self.builder.ins().const_time(one_epsilon);
            self.builder.ins().drv(lhs, rhs, one_epsilon);
        }

        // Emit module instantiations.
        for &inst_id in &hir.insts {
            // Resolve the instantiation details.
            let inst = match self.hir_of(inst_id)? {
                HirNode::Inst(x) => x,
                _ => unreachable!(),
            };
            let inst = self.inst_details(Ref(inst), env)?;
            let target_module = match inst.target.kind {
                InstTarget::Module(x) => self.hir_of_module(x)?,
                _ => continue,
            };

            // Emit the instantiated module.
            let target = self.emit_module_with_env(target_module.id, inst.inner_env)?;

            // Prepare the port assignments.
            let (inputs, outputs) = self.emit_port_connections(
                target_module.ports_new,
                inst.as_ref(),
                &target.ports.inputs,
                &target.ports.outputs,
            )?;

            // Instantiate the module.
            let ext_unit = self.builder.add_extern(
                self.into.unit(target.unit).name().clone(),
                self.into.unit(target.unit).sig().clone(),
            );
            if !inst.hir.ast.dims.is_empty() {
                bug_span!(
                    inst.hir.ast.span(),
                    self.cx,
                    "instance arrays of modules not supported"
                );
            }
            self.builder.ins().inst(ext_unit, inputs, outputs);
            // TODO: Annotate instance name once LLHD allows that.
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
                    let k = self.constant_value_of(cond, env);
                    if k.is_false() {
                        if let Some(else_body) = else_body {
                            self.emit_module_block(id, env, else_body, name_prefix)?;
                        }
                    } else {
                        self.emit_module_block(id, env, main_body, name_prefix)?;
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
                    while self.constant_value_of(cond, local_env).is_true() {
                        self.emit_module_block(id, local_env, body, name_prefix)?;
                        local_env = self.execute_genvar_step(step, local_env)?;
                    }
                }
                _ => return self.unimp_msg("code generation for", hir),
            }
        }

        // Emit and instantiate procedures.
        for &proc_id in &hir.procs {
            let prok = self.emit_procedure(proc_id, env, name_prefix)?;
            let lookup_value = |&id: &AccessedNode| match self.values.get(&id) {
                Some(v) => v.clone(),
                None => {
                    self.emit(
                        DiagBuilder2::bug(format!(
                            "{} used as input/output of {}, but no value has been emitted",
                            self.hir_of(id.id()).unwrap().desc_full(),
                            self.hir_of(proc_id).unwrap().desc_full(),
                        ))
                        .span(self.span(id.id())),
                    );
                    panic!("no value emitted for {:?}", id);
                }
            };
            let inputs = prok.inputs.iter().map(lookup_value).collect();
            let outputs = prok.outputs.iter().map(lookup_value).collect();
            let ext_unit = self.builder.add_extern(
                self.into.unit(prok.unit).name().clone(),
                self.into.unit(prok.unit).sig().clone(),
            );
            self.builder.ins().inst(ext_unit, inputs, outputs);
        }

        Ok(())
    }

    /// Emit code for the connections made in a port list.
    fn emit_port_connections(
        &mut self,
        port_list: &PortList<'gcx>,
        inst: &InstDetails<'gcx>,
        inputs: &[ModulePort<'gcx>],
        outputs: &[ModulePort<'gcx>],
    ) -> Result<(Vec<llhd::ir::Value>, Vec<llhd::ir::Value>)> {
        // Map the values associated with the external ports to internal
        // ports.
        let mut port_mapping_int: HashMap<NodeId, NodeEnvId> = HashMap::new();
        for port in &port_list.ext_pos {
            let mapping = match inst.ports.find(port.id) {
                Some(m) => m,
                None => continue,
            };
            if port.exprs.len() > 1 {
                self.emit(
                    DiagBuilder2::bug("port expressions with concatenations not supported")
                        .span(inst.hir.span())
                        .add_note("Port declared here:")
                        .span(port.span),
                );
                continue;
            }
            let expr = match port.exprs.iter().next() {
                Some(m) => m,
                None => continue,
            };
            if !expr.selects.is_empty() {
                self.emit(
                    DiagBuilder2::bug("port expressions with selections not supported")
                        .span(inst.hir.span())
                        .add_note("Port declared here:")
                        .span(port.span),
                );
                continue;
            }
            let int = &port_list.int[expr.port];
            if port_mapping_int.insert(int.id, mapping).is_some() {
                self.emit(
                    DiagBuilder2::error(format!("port `{}` connected multiple times", int.name))
                        .span(self.span(mapping.id())),
                );
            }
        }
        trace!("Internal Port Mapping: {:?}", port_mapping_int);

        // Connect to the actual internal ports emitted as the module's port
        // interface.
        let mut map_port = |port: &ModulePort<'gcx>, lvalue: bool| {
            trace!(
                "Mapping port `{}` of type `{}` as {}",
                port.name,
                port.ty,
                match lvalue {
                    true => "lvalue",
                    false => "rvalue",
                }
            );
            if let Some(&mapping) = port_mapping_int.get(&port.port.id) {
                // Emit the assigned node as rvalue or lvalue, depending on
                // the port direction.
                if lvalue {
                    let mir = self.mir_lvalue(mapping.id(), mapping.env());
                    if mir.is_error() {
                        return Err(());
                    }
                    let mir = match port.kind {
                        ModulePortKind::Port => mir,
                        ModulePortKind::IntfSignal { decl_id, env, .. } => {
                            self.arena().alloc_mir_lvalue(mir::Lvalue {
                                id: NodeId::alloc(),
                                origin: mir.origin,
                                env,
                                span: mir.span,
                                ty: port.ty,
                                kind: mir::LvalueKind::IntfSignal(mir, decl_id),
                            })
                        }
                    };
                    self.emit_mir_lvalue(mir).map(|(x, _)| x)
                } else {
                    let mir = self.mir_rvalue(mapping.id(), mapping.env());
                    if mir.is_error() {
                        return Err(());
                    }
                    let mir = match port.kind {
                        ModulePortKind::Port => mir,
                        ModulePortKind::IntfSignal { decl_id, env, .. } => {
                            self.arena().alloc_mir_rvalue(mir::Rvalue {
                                id: NodeId::alloc(),
                                origin: mir.origin,
                                env,
                                span: mir.span,
                                ty: port.ty,
                                kind: mir::RvalueKind::IntfSignal(mir, decl_id),
                                konst: false,
                            })
                        }
                    };
                    self.emit_mir_rvalue_mode(mir, Mode::Signal)
                }
            } else {
                // Emit an auxiliary signal with the default value for this
                // port or type.
                let ty = self.type_of_int_port(Ref(port.port), inst.inner_env);
                let value = match port.port.data.as_ref().and_then(|d| d.default) {
                    Some(default) => {
                        self.emit_rvalue_mode(default, inst.inner_env, Mode::Signal)?
                    }
                    None => {
                        let v = self.type_default_value(ty);
                        let v = self.emit_const(v, inst.inner_env, port.port.span)?;
                        self.builder.ins().sig(v)
                    }
                };
                self.builder
                    .set_name(value, format!("{}.{}.default", inst.hir.name, port.name));
                Ok(value)
            }
        };
        let inputs = inputs
            .iter()
            .map(|p| map_port(p, false))
            .collect::<Result<Vec<_>>>()?;
        let outputs = outputs
            .iter()
            .map(|p| map_port(p, true))
            .collect::<Result<Vec<_>>>()?;
        Ok((inputs, outputs))
    }

    /// Map a value to an LLHD constant (interned).
    fn emit_const(
        &mut self,
        value: Value<'gcx>,
        env: ParamEnv,
        span: Span,
    ) -> Result<llhd::ir::Value> {
        if let Some(x) = self.interned_consts.get(value) {
            x.clone()
        } else {
            let x = self.emit_const_uninterned(value, env, span);
            // self.interned_consts.insert(value, x.clone());
            x
        }
    }

    /// Map a value to an LLHD constant.
    fn emit_const_uninterned(
        &mut self,
        value: Value<'gcx>,
        env: ParamEnv,
        span: Span,
    ) -> Result<llhd::ir::Value> {
        if value.ty.is_error() {
            return Err(());
        }
        match value.kind {
            ValueKind::Int(ref k, ..) => {
                let size = value.ty.simple_bit_vector(self.cx, span).size;
                Ok(self.builder.ins().const_int((size, k.clone())))
            }
            ValueKind::Time(ref k) => Ok(self
                .builder
                .ins()
                .const_time(llhd::value::TimeValue::new(k.clone(), 0, 0))),
            ValueKind::StructOrArray(ref v) => {
                if let Some(_dim) = value.ty.outermost_dim() {
                    let fields: Result<Vec<_>> = v
                        .iter()
                        .map(|v| self.emit_const(v, env, span).map(Into::into))
                        .collect();
                    Ok(self.builder.ins().array(fields?))
                } else if let Some(_strukt) = value.ty.get_struct() {
                    let fields: Result<Vec<_>> = v
                        .iter()
                        .map(|v| self.emit_const(v, env, span).map(Into::into))
                        .collect();
                    Ok(self.builder.ins().strukt(fields?))
                } else {
                    panic!(
                        "invalid type `{}` for const struct/array value {:#?}",
                        value.ty, value
                    );
                }
            }
            ValueKind::Error => Err(()),
            _ => panic!(
                "invalid combination of type `{}` and value {:#?}",
                value.ty, value
            ),
        }
    }

    /// Emit the zero value for an LLHD type.
    ///
    /// This function is ultimately expected to be moved into LLHD.
    fn emit_zero_for_type(&mut self, ty: &llhd::Type) -> llhd::ir::Value {
        match **ty {
            llhd::TimeType => {
                self.builder
                    .ins()
                    .const_time(llhd::value::TimeValue::new(num::zero(), 0, 0))
            }
            llhd::IntType(w) => self.builder.ins().const_int((w, 0)),
            llhd::SignalType(ref ty) => {
                let inner = self.emit_zero_for_type(ty);
                self.builder.ins().sig(inner)
            }
            llhd::PointerType(ref ty) => {
                let inner = self.emit_zero_for_type(ty);
                self.builder.ins().var(inner)
            }
            llhd::ArrayType(l, ref ty) => {
                let inner = self.emit_zero_for_type(ty);
                self.builder.ins().array_uniform(l, inner)
            }
            llhd::StructType(ref tys) => {
                let inner = tys.iter().map(|ty| self.emit_zero_for_type(ty)).collect();
                self.builder.ins().strukt(inner)
            }
            _ => panic!("no zero-value for type {}", ty),
        }
    }

    /// Get the type of an LLHD value.
    fn llhd_type(&self, value: llhd::ir::Value) -> llhd::Type {
        self.builder.value_type(value)
    }

    /// Emit the code for an rvalue.
    fn emit_rvalue(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<llhd::ir::Value> {
        self.emit_rvalue_mode(expr_id, env, Mode::Value)
    }

    /// Emit the code for an rvalue.
    fn emit_rvalue_mode(
        &mut self,
        expr_id: NodeId,
        env: ParamEnv,
        mode: Mode,
    ) -> Result<llhd::ir::Value> {
        let mir = self.mir_rvalue(expr_id, env);
        self.emit_mir_rvalue_mode(mir, mode)
    }

    /// Emit the code for an MIR rvalue.
    fn emit_mir_rvalue(&mut self, mir: &'gcx mir::Rvalue<'gcx>) -> Result<llhd::ir::Value> {
        self.emit_mir_rvalue_mode(mir, Mode::Value)
    }

    /// Emit the code for an MIR rvalue.
    fn emit_mir_rvalue_mode(
        &mut self,
        mir: &'gcx mir::Rvalue<'gcx>,
        mode: Mode,
    ) -> Result<llhd::ir::Value> {
        let (value, actual_mode) = if let Some(x) = self.interned_rvalues.get(&(mir.id, mode)) {
            x.clone()?
        } else {
            let x = self.emit_mir_rvalue_uninterned(mir, mode);
            self.interned_rvalues.insert((mir.id, mode), x);
            x?
        };

        match (mode, actual_mode) {
            (Mode::Signal, Mode::Value) => {
                let ty = self.llhd_type(value);
                let init = self.emit_zero_for_type(&ty);
                let sig = self.builder.ins().sig(init);
                let delay = llhd::value::TimeValue::new(num::zero(), 1, 0);
                let delay_const = self.builder.ins().const_time(delay);
                self.builder.ins().drv(sig, value, delay_const);
                Ok(sig)
            }
            (Mode::Value, Mode::Signal) => unreachable!(),
            _ => Ok(value),
        }
    }

    /// Emit the code for an MIR rvalue.
    ///
    /// Wrapper around `emit_mir_rvalue_inner` that asserts the LLHD type of the
    /// result matches expectations.
    fn emit_mir_rvalue_uninterned(
        &mut self,
        mir: &'gcx mir::Rvalue<'gcx>,
        mode_hint: Mode,
    ) -> Result<(llhd::ir::Value, Mode)> {
        let result = self.emit_mir_rvalue_inner(mir, mode_hint);
        match result {
            Ok((result, actual_mode)) => {
                let llty_exp = self.emit_type(mir.ty)?;
                let llty_exp = match actual_mode {
                    Mode::Value => llty_exp,
                    Mode::Signal => llhd::signal_ty(llty_exp),
                };
                let llty_act = self.llhd_type(result);
                assert_span!(
                    llty_exp == llty_act,
                    mir.span,
                    self.cx,
                    "codegen for MIR rvalue `{}` should produce `{}`, but got `{}`; {:#?}",
                    mir.span.extract(),
                    llty_exp,
                    llty_act,
                    mir
                );
            }
            Err(()) => (),
        }
        result
    }

    /// Emit the code for an MIR rvalue.
    ///
    /// The `mode_hint` parameter provides a hint if the caller ultimately wants
    /// the result to be a signal or a value. For example, port connections to
    /// an instance would set the hint to `Mode::Signal`, while a binary expr
    /// would set it to `Mode::Value`. The function is free to ignore the hint,
    /// but will provide the actual mode it produced as part of the return
    /// value.
    fn emit_mir_rvalue_inner(
        &mut self,
        mir: &'gcx mir::Rvalue<'gcx>,
        mode_hint: Mode,
    ) -> Result<(llhd::ir::Value, Mode)> {
        // If the value is a constant, emit the fully folded constant value.
        if mir.is_const() {
            let value = self.const_mir_rvalue(mir.into());
            return self
                .emit_const(value, mir.env, mir.span)
                .map(|v| (v, Mode::Value));
        }

        let value = match mir.kind {
            mir::RvalueKind::Var(id) | mir::RvalueKind::Port(id) => {
                let sig = self
                    .shadows
                    .get(&id.into())
                    .cloned()
                    .unwrap_or_else(|| self.emitted_value(id));
                if mode_hint == Mode::Signal && self.llhd_type(sig).is_signal() {
                    return Ok((sig, Mode::Signal));
                } else {
                    Ok(self.emit_prb_or_var(sig))
                }
            }

            mir::RvalueKind::Intf(_) => {
                self.emit(
                    DiagBuilder2::error("interface cannot be used in an expression").span(mir.span),
                );
                Err(())
            }

            // Interface signals require special care, because they are emitted
            // in a transposed fashion.
            mir::RvalueKind::IntfSignal(value, signal) => {
                return self.emit_rvalue_interface(value, signal, mode_hint);
            }

            mir::RvalueKind::CastValueDomain { value, .. } => {
                // TODO(fschuiki): Turn this into an actual `iN` to `lN` cast.
                return self.emit_mir_rvalue_inner(value, mode_hint);
            }

            mir::RvalueKind::Transmute(value) => {
                // Transmute is a simple no-op.
                return self.emit_mir_rvalue_inner(value, mode_hint);
            }

            mir::RvalueKind::CastSign(_, value) => {
                // Sign conversions are no-ops in LLHD since they merely
                // influence the type system.
                return self.emit_mir_rvalue_inner(value, mode_hint);
            }

            mir::RvalueKind::CastToBool(value) => {
                let value = self.emit_mir_rvalue(value)?;
                let ty = self.llhd_type(value);
                let zero = self.emit_zero_for_type(&ty);
                Ok(self.builder.ins().neq(value, zero))
            }

            mir::RvalueKind::Truncate(target_width, value) => {
                let llvalue = self.emit_mir_rvalue(value)?;
                Ok(self.builder.ins().ext_slice(llvalue, 0, target_width))
            }

            mir::RvalueKind::ZeroExtend(_, value) => {
                let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                let llty = self.emit_type(mir.ty)?;
                let result = self.emit_zero_for_type(&llty);
                let value = self.emit_mir_rvalue(value)?;
                let result = self.builder.ins().ins_slice(result, value, 0, width);
                self.builder.set_name(result, "zext".to_string());
                Ok(result)
            }

            mir::RvalueKind::SignExtend(_, value) => {
                let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                let llty = self.emit_type(mir.ty)?;
                let value = self.emit_mir_rvalue(value)?;
                let sign = self.builder.ins().ext_slice(value, width - 1, 1);
                let zeros = self.emit_zero_for_type(&llty);
                let ones = self.builder.ins().not(zeros);
                let mux = self.builder.ins().array(vec![zeros, ones]);
                let mux = self.builder.ins().mux(mux, sign);
                let result = self.builder.ins().ins_slice(mux, value, 0, width);
                self.builder.set_name(result, "sext".to_string());
                Ok(result)
            }

            mir::RvalueKind::ConstructArray(ref indices) => {
                let llvalue = (0..indices.len())
                    .map(|i| self.emit_mir_rvalue(indices[&i]))
                    .collect::<Result<Vec<_>>>()?;
                Ok(self.builder.ins().array(llvalue))
            }

            mir::RvalueKind::ConstructStruct(ref members) => {
                let members = members
                    .iter()
                    .map(|&v| self.emit_mir_rvalue(v))
                    .collect::<Result<Vec<_>>>()?;
                Ok(self.builder.ins().strukt(members))
            }

            mir::RvalueKind::Const(k) => self.emit_const(k, mir.env, mir.span),

            mir::RvalueKind::Index {
                value,
                base,
                length,
            } => {
                let target = self.emit_mir_rvalue(value)?;
                self.emit_rvalue_index(value.ty, target, base, length)
            }

            mir::RvalueKind::Member { value, field } => {
                let target = self.emit_mir_rvalue(value)?;
                let value = self.builder.ins().ext_field(target, field);
                // let name = format!(
                //     "{}.{}",
                //     self.builder
                //
                //         .get_name(target)
                //         .map(String::from)
                //         .unwrap_or_else(|| "struct".into()),
                //     field
                // );
                // self.builder.set_name(value, name);
                Ok(value)
            }

            mir::RvalueKind::UnaryBitwise { op, arg } => {
                let arg = self.emit_mir_rvalue(arg)?;
                Ok(match op {
                    mir::UnaryBitwiseOp::Not => self.builder.ins().not(arg),
                })
            }

            mir::RvalueKind::BinaryBitwise { op, lhs, rhs } => {
                let lhs = self.emit_mir_rvalue(lhs)?;
                let rhs = self.emit_mir_rvalue(rhs)?;
                Ok(match op {
                    mir::BinaryBitwiseOp::And => self.builder.ins().and(lhs, rhs),
                    mir::BinaryBitwiseOp::Or => self.builder.ins().or(lhs, rhs),
                    mir::BinaryBitwiseOp::Xor => self.builder.ins().xor(lhs, rhs),
                })
            }

            mir::RvalueKind::IntComp {
                op, lhs, rhs, sign, ..
            } => {
                let lhs = self.emit_mir_rvalue(lhs)?;
                let rhs = self.emit_mir_rvalue(rhs)?;
                let signed = sign.is_signed();
                Ok(match op {
                    mir::IntCompOp::Eq => self.builder.ins().eq(lhs, rhs),
                    mir::IntCompOp::Neq => self.builder.ins().neq(lhs, rhs),
                    mir::IntCompOp::Lt if signed => self.builder.ins().slt(lhs, rhs),
                    mir::IntCompOp::Leq if signed => self.builder.ins().sle(lhs, rhs),
                    mir::IntCompOp::Gt if signed => self.builder.ins().sgt(lhs, rhs),
                    mir::IntCompOp::Geq if signed => self.builder.ins().sge(lhs, rhs),
                    mir::IntCompOp::Lt => self.builder.ins().ult(lhs, rhs),
                    mir::IntCompOp::Leq => self.builder.ins().ule(lhs, rhs),
                    mir::IntCompOp::Gt => self.builder.ins().ugt(lhs, rhs),
                    mir::IntCompOp::Geq => self.builder.ins().uge(lhs, rhs),
                })
            }

            mir::RvalueKind::IntUnaryArith { op, arg, .. } => {
                let arg = self.emit_mir_rvalue(arg)?;
                Ok(match op {
                    mir::IntUnaryArithOp::Neg => self.builder.ins().neg(arg),
                })
            }

            mir::RvalueKind::IntBinaryArith {
                op, lhs, rhs, sign, ..
            } => {
                let lhs_ll = self.emit_mir_rvalue(lhs)?;
                let rhs_ll = self.emit_mir_rvalue(rhs)?;
                let signed = sign.is_signed();
                Ok(match op {
                    mir::IntBinaryArithOp::Add => self.builder.ins().add(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Sub => self.builder.ins().sub(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mul if signed => self.builder.ins().smul(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Div if signed => self.builder.ins().sdiv(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mod if signed => self.builder.ins().smod(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mul => self.builder.ins().umul(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Div => self.builder.ins().udiv(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mod => self.builder.ins().umod(lhs_ll, rhs_ll),

                    // The `x**y` operator requires special love, because there
                    // is no direct equivalent for it in LLHD.
                    mir::IntBinaryArithOp::Pow => {
                        // If the exponent is a constant, we simply unroll.
                        if rhs.is_const() {
                            let count = self.const_mir_rvalue_int(Ref(rhs))?;
                            let mut value = lhs_ll;
                            for _ in 1..count.to_usize().unwrap() {
                                value = self.builder.ins().umul(value, lhs_ll);
                            }
                            return Ok((value, Mode::Value));
                        }

                        // If the base is a constant power of two, we translate
                        // `x**y` into `1 << (y * log2(x))`.
                        if lhs.is_const() {
                            let base = self.const_mir_rvalue_int(Ref(lhs))?.to_usize();
                            // `log2(base)`
                            let lg2 = base.and_then(|base| {
                                if base.is_power_of_two() {
                                    Some(base.trailing_zeros())
                                } else {
                                    None
                                }
                            });
                            // `y * log2(base)`
                            let rhs_ll = lg2.map(|lg2| {
                                let width = self.llhd_type(rhs_ll).len();
                                let lg2 = self.builder.ins().const_int((width, BigInt::from(lg2)));
                                self.builder.ins().umul(lg2, rhs_ll)
                            });
                            if let Some(rhs_ll) = rhs_ll {
                                // `1`
                                let width = self.llhd_type(lhs_ll).len();
                                let lhs_ll = self.builder.ins().const_int((width, BigInt::one()));
                                // `1 << (y * log2(base))`
                                let zeros = self.emit_zero_for_type(&self.llhd_type(lhs_ll));
                                return Ok((
                                    self.builder.ins().shl(lhs_ll, zeros, rhs_ll),
                                    Mode::Value,
                                ));
                            }
                        }

                        // Otherwise we just complain.
                        self.emit(
                            DiagBuilder2::error("`**` operator on non-constants not supported")
                                .span(mir.span),
                        );
                        return Err(());
                    }
                })
            }

            mir::RvalueKind::Concat(ref values) => {
                let mut offset = 0;
                let llty = self.emit_type(mir.ty)?;
                let mut result = self.emit_zero_for_type(&llty);
                trace!(
                    "Concatenating {} values into `{}` (as `{}`)",
                    values.len(),
                    mir.ty,
                    llty
                );
                for value in values.iter().rev() {
                    let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                    let llval = self.emit_mir_rvalue(value)?;
                    trace!(
                        " - Value has width {}, type `{}`, in LLHD `{}`",
                        width,
                        value.ty,
                        self.llhd_type(llval)
                    );
                    result = self.builder.ins().ins_slice(result, llval, offset, width);
                    offset += width;
                }
                self.builder.set_name(result, "concat".to_string());
                Ok(result)
            }

            mir::RvalueKind::Repeat(times, value) => {
                let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                let value = self.emit_mir_rvalue(value)?;
                let llty = self.emit_type(mir.ty)?;
                let mut result = self.emit_zero_for_type(&llty);
                for i in 0..times {
                    result = self
                        .builder
                        .ins()
                        .ins_slice(result, value, i * width, width);
                }
                self.builder.set_name(result, "repeat".to_string());
                Ok(result)
            }

            mir::RvalueKind::Shift {
                op,
                arith,
                value,
                amount,
            } => {
                let value = self.emit_mir_rvalue(value)?;
                let amount = self.emit_mir_rvalue(amount)?;
                let value_ty = self.builder.unit().value_type(value);
                let hidden = self.emit_zero_for_type(&value_ty);
                let hidden = if arith && op == mir::ShiftOp::Right {
                    let ones = self.builder.ins().not(hidden);
                    let sign = self
                        .builder
                        .ins()
                        .ext_slice(value, value_ty.unwrap_int() - 1, 1);
                    let mux = self.builder.ins().array(vec![hidden, ones]);
                    self.builder.ins().mux(mux, sign)
                } else {
                    hidden
                };
                Ok(match op {
                    mir::ShiftOp::Left => self.builder.ins().shl(value, hidden, amount),
                    mir::ShiftOp::Right => self.builder.ins().shr(value, hidden, amount),
                })
            }

            mir::RvalueKind::Ternary {
                cond,
                true_value,
                false_value,
            } => {
                let cond = self.emit_mir_rvalue(cond)?;
                let true_value = self.emit_mir_rvalue(true_value)?;
                let false_value = self.emit_mir_rvalue(false_value)?;
                let array = self.builder.ins().array(vec![false_value, true_value]);
                Ok(self.builder.ins().mux(array, cond))
            }

            mir::RvalueKind::Reduction { op, arg } => {
                let width = arg.ty.simple_bit_vector(self.cx, arg.span).size;
                let arg = self.emit_mir_rvalue(arg)?;
                let mut value = self.builder.ins().ext_slice(arg, 0, 1);
                for i in 1..width {
                    let bit = self.builder.ins().ext_slice(arg, i, 1);
                    value = match op {
                        mir::BinaryBitwiseOp::And => self.builder.ins().and(value, bit),
                        mir::BinaryBitwiseOp::Or => self.builder.ins().or(value, bit),
                        mir::BinaryBitwiseOp::Xor => self.builder.ins().xor(value, bit),
                    };
                }
                Ok(value)
            }

            mir::RvalueKind::Assignment {
                lvalue,
                rvalue,
                result,
            } => {
                self.emit_mir_blocking_assign(lvalue, rvalue)?;
                self.emit_mir_rvalue(result)
            }

            mir::RvalueKind::PackString(value) | mir::RvalueKind::UnpackString(value) => bug_span!(
                value.span,
                self.cx,
                "codegen for string packing/unpacking not implemented"
            ),

            mir::RvalueKind::StringComp { .. } => bug_span!(
                mir.span,
                self.cx,
                "runtime string comparisons not implemented"
            ),

            mir::RvalueKind::Error => Err(()),
        };

        value.map(|v| (v, Mode::Value))
    }

    fn emit_prb_or_var(&mut self, sig: llhd::ir::Value) -> llhd::ir::Value {
        match *self.llhd_type(sig) {
            llhd::SignalType(_) => {
                let value = self.builder.ins().prb(sig);
                if let Some(name) = self.builder.get_name(sig) {
                    self.builder.set_name(value, format!("{}.prb", name));
                }
                value
            }
            llhd::PointerType(_) => {
                let value = self.builder.ins().ld(sig);
                if let Some(name) = self.builder.get_name(sig) {
                    self.builder.set_name(value, format!("{}.ld", name));
                }
                value
            }
            _ => sig,
        }
    }

    /// Emit the code for an rvalue converted to a boolean..
    fn emit_rvalue_bool(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<llhd::ir::Value> {
        let mir = self.mir_rvalue(expr_id, env);
        assert_span!(
            mir.ty
                .get_simple_bit_vector()
                .map(|sbv| sbv.size == 1)
                .unwrap_or(false),
            mir.span,
            self,
            "value of type `{}` should be a bool",
            mir.ty
        );
        self.emit_mir_rvalue(mir)
    }

    /// Emit the code for an MIR rvalue interface.
    ///
    /// This is a bit tricky, since we transpose interface arrays to array
    /// signals, which means from an MIR perspective, an access `a[0][1].x`
    /// looks rather like `a.x[0][1]` during codegen.
    fn emit_rvalue_interface(
        &mut self,
        mir: &mir::Rvalue<'gcx>,
        signal: NodeId,
        mode_hint: Mode,
    ) -> Result<(llhd::ir::Value, Mode)> {
        match mir.kind {
            mir::RvalueKind::Intf(intf) => {
                let id = AccessedNode::Intf(intf, signal);
                let sig = self
                    .shadows
                    .get(&id)
                    .cloned()
                    .unwrap_or_else(|| self.emitted_value(id));
                debug!(
                    "{:?} emitted value is {:?} (type {})",
                    id,
                    sig,
                    self.llhd_type(sig)
                );
                if mode_hint == Mode::Signal && self.llhd_type(sig).is_signal() {
                    Ok((sig, Mode::Signal))
                } else {
                    Ok((self.emit_prb_or_var(sig), Mode::Value))
                }
            }

            mir::RvalueKind::Index {
                value,
                base,
                length,
            } => {
                let (inner, actual_mode) = self.emit_rvalue_interface(value, signal, mode_hint)?;
                self.emit_rvalue_index(value.ty, inner, base, length)
                    .map(|v| (v, actual_mode))
            }

            _ => bug_span!(
                mir.span,
                self.cx,
                "found MIR rvalue which cannot appear in a transposed interface signal access: \
                 {:#?}",
                mir
            ),
        }
    }

    /// Emit the code for an indexing operation on an already emitted rvalue.
    fn emit_rvalue_index(
        &mut self,
        ty: &'gcx UnpackedType<'gcx>,
        value: llhd::ir::Value,
        base: &'gcx mir::Rvalue<'gcx>,
        length: usize,
    ) -> Result<llhd::ir::Value> {
        let base = self.emit_mir_rvalue(base)?;
        let hidden = self.emit_zero_for_type(&self.llhd_type(value));
        // TODO(fschuiki): make the above a constant of all `x`.
        let shifted = self.builder.ins().shr(value, hidden, base);
        if ty.coalesces_to_llhd_scalar() {
            let length = std::cmp::max(1, length);
            Ok(self.builder.ins().ext_slice(shifted, 0, length))
        } else {
            if length == 0 {
                Ok(self.builder.ins().ext_field(shifted, 0))
            } else {
                Ok(self.builder.ins().ext_slice(shifted, 0, length))
            }
        }
    }

    /// Emit the code for an MIR lvalue.
    fn emit_mir_lvalue(
        &mut self,
        mir: &mir::Lvalue<'gcx>,
    ) -> Result<(llhd::ir::Value, Option<llhd::ir::Value>)> {
        if let Some(x) = self.interned_lvalues.get(&mir.id) {
            x.clone()
        } else {
            let x = self.emit_mir_lvalue_uninterned(mir);
            self.interned_lvalues.insert(mir.id, x);
            x
        }
    }

    /// Emit the code for an MIR lvalue.
    ///
    /// The first returned value is the actually targeted lvalue. The second is
    /// a potential shadow variable that must be kept up-to-date.
    fn emit_mir_lvalue_uninterned(
        &mut self,
        mir: &mir::Lvalue<'gcx>,
    ) -> Result<(llhd::ir::Value, Option<llhd::ir::Value>)> {
        let result = self.emit_mir_lvalue_inner(mir);
        match result {
            Ok((sig, var)) => {
                let llty_exp1 = llhd::signal_ty(self.emit_type(mir.ty)?);
                let llty_exp2 = llhd::pointer_ty(self.emit_type(mir.ty)?);
                let llty_act = self.llhd_type(sig);
                assert_span!(
                    llty_exp1 == llty_act || llty_exp2 == llty_act,
                    mir.span,
                    self.cx,
                    "codegen for MIR lvalue `{}` should produce `{}` or `{}`, but got `{}`",
                    mir.span.extract(),
                    llty_exp1,
                    llty_exp2,
                    llty_act
                );
                if let Some(var) = var {
                    let llty_exp = llhd::pointer_ty(self.emit_type(mir.ty)?);
                    let llty_act = self.llhd_type(var);
                    assert_span!(
                        llty_exp == llty_act,
                        mir.span,
                        self.cx,
                        "codegen for MIR lvalue `{}` should produce `{}`, but got `{}`",
                        mir.span.extract(),
                        llty_exp,
                        llty_act
                    );
                }
            }
            Err(()) => (),
        }
        result
    }

    /// Emit the code for an MIR lvalue.
    ///
    /// The first returned value is the actually targeted lvalue. The second is
    /// a potential shadow variable that must be kept up-to-date.
    fn emit_mir_lvalue_inner(
        &mut self,
        mir: &mir::Lvalue<'gcx>,
    ) -> Result<(llhd::ir::Value, Option<llhd::ir::Value>)> {
        match mir.kind {
            // Variables and ports trivially return their declaration value.
            // This is either the `var` or `sig` instruction which introduced
            // them.
            mir::LvalueKind::Var(id) | mir::LvalueKind::Port(id) => Ok((
                self.emitted_value(id).clone(),
                self.shadows.get(&id.into()).cloned(),
            )),

            // Interface signals require special care, because they are emitted
            // in a transposed fashion.
            mir::LvalueKind::IntfSignal(value, signal) => self.emit_lvalue_interface(value, signal),

            // Member accesses simply look up their inner lvalue and extract the
            // signal or pointer to the respective subfield.
            mir::LvalueKind::Member { value, field } => {
                let target = self.emit_mir_lvalue(value)?;
                let value_real = self.builder.ins().ext_field(target.0, field);
                let value_shadow = target
                    .1
                    .map(|target| self.builder.ins().ext_field(target, field));
                Ok((value_real, value_shadow))
            }

            // Index accesses shift and extract the accessed slice as a signal
            // or pointer.
            mir::LvalueKind::Index {
                value,
                base,
                length,
            } => {
                let inner = self.emit_mir_lvalue(value)?;
                self.emit_lvalue_index(value.ty, inner, base, length)
            }

            mir::LvalueKind::Repeat(..) | mir::LvalueKind::Concat(..) => {
                bug_span!(
                    mir.span,
                    self.cx,
                    "mir lvalue should have been simplified by its parent assignment; {:#?}",
                    mir
                );
            }

            // Errors from MIR lowering have already been reported. Just abort.
            mir::LvalueKind::Error => Err(()),

            _ => {
                bug_span!(mir.span, self.cx, "codegen for mir lvalue {:#?}", mir);
            }
        }
    }

    /// Emit the code for an MIR lvalue interface.
    ///
    /// This is a bit tricky, since we transpose interface arrays to array
    /// signals, which means from an MIR perspective, an access `a[0][1].x`
    /// looks rather like `a.x[0][1]` during codegen.
    fn emit_lvalue_interface(
        &mut self,
        mir: &mir::Lvalue<'gcx>,
        signal: NodeId,
    ) -> Result<(llhd::ir::Value, Option<llhd::ir::Value>)> {
        match mir.kind {
            mir::LvalueKind::Intf(intf) => {
                let id = AccessedNode::Intf(intf, signal);
                Ok((
                    self.emitted_value(id).clone(),
                    self.shadows.get(&id).cloned(),
                ))
            }

            mir::LvalueKind::Index {
                value,
                base,
                length,
            } => {
                let inner = self.emit_lvalue_interface(value, signal)?;
                self.emit_lvalue_index(value.ty, inner, base, length)
            }

            _ => bug_span!(
                mir.span,
                self.cx,
                "found MIR lvalue which cannot appear in a transposed interface signal access: \
                 {:#?}",
                mir
            ),
        }
    }

    /// Emit the code for an indexing operation on an already emitted lvalue.
    fn emit_lvalue_index(
        &mut self,
        ty: &'gcx UnpackedType<'gcx>,
        value: (llhd::ir::Value, Option<llhd::ir::Value>),
        base: &'gcx mir::Rvalue<'gcx>,
        length: usize,
    ) -> Result<(llhd::ir::Value, Option<llhd::ir::Value>)> {
        let (target_real, target_shadow) = value;
        let base = self.emit_mir_rvalue(base)?;
        let shifted_real = {
            let hidden = self.emit_zero_for_type(&self.llhd_type(target_real));
            self.builder.ins().shr(target_real, hidden, base)
        };
        let shifted_shadow = target_shadow.map(|target| {
            let hidden = self.emit_zero_for_type(&self.llhd_type(target));
            self.builder.ins().shr(target, hidden, base)
        });
        if ty.coalesces_to_llhd_scalar() {
            let length = std::cmp::max(1, length);
            Ok((
                self.builder.ins().ext_slice(shifted_real, 0, length),
                shifted_shadow.map(|s| self.builder.ins().ext_slice(s, 0, length)),
            ))
        } else {
            if length == 0 {
                Ok((
                    self.builder.ins().ext_field(shifted_real, 0),
                    shifted_shadow.map(|s| self.builder.ins().ext_field(s, 0)),
                ))
            } else {
                Ok((
                    self.builder.ins().ext_slice(shifted_real, 0, length),
                    shifted_shadow.map(|s| self.builder.ins().ext_slice(s, 0, length)),
                ))
            }
        }
    }

    /// Emit a binary shift operator.
    fn emit_shift_operator(
        &mut self,
        dir: ShiftDir,
        arith: bool,
        lhs: llhd::ir::Value,
        rhs: llhd::ir::Value,
    ) -> llhd::ir::Value {
        let ty = self.builder.value_type(lhs);
        let width = if ty.is_signal() {
            ty.unwrap_signal().unwrap_int()
        } else {
            ty.unwrap_int()
        };
        let zeros = self.builder.ins().const_int((width, 0));
        let hidden = if arith && dir == ShiftDir::Right {
            let ones = self.builder.ins().not(zeros);
            let sign = self.builder.ins().ext_slice(lhs, width - 1, 1);
            let array = self.builder.ins().array(vec![zeros, ones]);
            self.builder.ins().mux(array, sign)
        } else {
            zeros
        };
        match dir {
            ShiftDir::Left => self.builder.ins().shl(lhs, hidden, rhs),
            ShiftDir::Right => self.builder.ins().shr(lhs, hidden, rhs),
        }
    }

    /// Add a nameless block.
    fn add_nameless_block(&mut self) -> llhd::ir::Block {
        self.builder.block()
    }

    /// Add a named block.
    fn add_named_block(&mut self, name: impl Into<String>) -> llhd::ir::Block {
        let bb = self.builder.block();
        self.builder.set_block_name(bb, name.into());
        bb
    }

    /// Emit the code for a statement.
    fn emit_stmt(&mut self, stmt_id: NodeId, env: ParamEnv) -> Result<()> {
        self.flush_mir();
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
        debug!("Emit stmt `{}`", {
            let s = hir.span.extract();
            if s.len() > 40 {
                format!("{} [...]", &s[0..40])
            } else {
                s
            }
        });
        #[allow(unreachable_patterns)]
        match hir.kind {
            hir::StmtKind::Null => (),
            hir::StmtKind::Block(ref ids) => {
                for &id in ids {
                    self.emit_stmt(id, env)?;
                }
            }
            hir::StmtKind::Assign { lhs, rhs, kind } => {
                let lhs_mir = self.mir_lvalue(lhs, env);
                let rhs_mir = self.mir_rvalue(rhs, env);
                if lhs_mir.is_error() || rhs_mir.is_error() {
                    return Err(());
                }
                assert_type!(rhs_mir.ty, lhs_mir.ty, rhs_mir.span, self.cx);
                let lhs_lv = self.emit_mir_lvalue(lhs_mir)?;
                let rhs_rv = self.emit_mir_rvalue(rhs_mir)?;

                match kind {
                    hir::AssignKind::Block(ast::AssignOp::Identity) => {
                        self.emit_blocking_assign_llhd(lhs_lv, rhs_rv)?;
                    }
                    hir::AssignKind::Block(op) => {
                        let lhs_rv = self.emit_rvalue(lhs, env)?;
                        let value = match op {
                            ast::AssignOp::Identity => unreachable!(),
                            ast::AssignOp::Add => self.builder.ins().add(lhs_rv, rhs_rv),
                            ast::AssignOp::Sub => self.builder.ins().sub(lhs_rv, rhs_rv),
                            ast::AssignOp::Mul => self.builder.ins().umul(lhs_rv, rhs_rv),
                            ast::AssignOp::Div => self.builder.ins().udiv(lhs_rv, rhs_rv),
                            ast::AssignOp::Mod => self.builder.ins().umod(lhs_rv, rhs_rv),
                            ast::AssignOp::BitAnd => self.builder.ins().and(lhs_rv, rhs_rv),
                            ast::AssignOp::BitOr => self.builder.ins().or(lhs_rv, rhs_rv),
                            ast::AssignOp::BitXor => self.builder.ins().xor(lhs_rv, rhs_rv),
                            ast::AssignOp::LogicShL => {
                                self.emit_shift_operator(ShiftDir::Left, false, lhs_rv, rhs_rv)
                            }
                            ast::AssignOp::LogicShR => {
                                self.emit_shift_operator(ShiftDir::Right, false, lhs_rv, rhs_rv)
                            }
                            ast::AssignOp::ArithShL => {
                                self.emit_shift_operator(ShiftDir::Left, true, lhs_rv, rhs_rv)
                            }
                            ast::AssignOp::ArithShR => {
                                self.emit_shift_operator(ShiftDir::Right, true, lhs_rv, rhs_rv)
                            }
                        };
                        self.emit_blocking_assign_llhd(lhs_lv, value)?;
                    }
                    hir::AssignKind::Nonblock => {
                        let delay = llhd::value::TimeValue::new(num::zero(), 1, 0);
                        let delay_const = self.builder.ins().const_time(delay);
                        self.builder.ins().drv(lhs_lv.0, rhs_rv, delay_const);
                    }
                    hir::AssignKind::NonblockDelay(delay) => {
                        let delay = self.emit_rvalue(delay, env)?;
                        self.builder.ins().drv(lhs_lv.0, rhs_rv, delay);
                    }
                    _ => {
                        error!("{:#?}", hir);
                        return self.unimp_msg(
                            format!("code generation for assignment {:?} in", kind),
                            hir,
                        );
                    }
                }
            }
            hir::StmtKind::Timed {
                control: hir::TimingControl::Delay(expr_id),
                stmt,
            } => {
                let resume_blk = self.add_nameless_block();
                let duration = self.emit_rvalue(expr_id, env)?.into();
                self.builder.ins().wait_time(resume_blk, duration, vec![]);
                self.builder.append_to(resume_blk);
                self.flush_mir(); // ensure we don't reuse earlier expr probe
                self.emit_shadow_update();
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
                self.builder.ins().br(init_blk);
                self.builder.append_to(init_blk);
                let mut init_values = vec![];
                for event in &expr_hir.events {
                    init_values.push(self.emit_rvalue(event.expr, env)?);
                }

                // Wait for any of the inputs to those expressions to change.
                let check_blk = self.add_named_block("check");
                let mut trigger_on = vec![];
                for event in &expr_hir.events {
                    let acc = self.accessed_nodes(event.expr, env)?;
                    for &id in &acc.read {
                        trigger_on.push(self.emitted_value(id).clone());
                    }
                }
                self.builder.ins().wait(check_blk, trigger_on);
                self.builder.append_to(check_blk);
                self.flush_mir(); // ensure we don't reuse earlier expr probe
                self.emit_shadow_update();

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
                        let iff_value = self.emit_rvalue_bool(iff, env)?;
                        trigger = self.builder.ins().and(trigger, iff_value);
                        self.builder.set_name(trigger, "iff".to_string());
                    }
                    event_cond = Some(match event_cond {
                        Some(chain) => {
                            let value = self.builder.ins().or(chain, trigger);
                            self.builder.set_name(value, "event_or".to_string());
                            value
                        }
                        None => trigger,
                    });
                }

                // If the event happened, branch to a new block which will
                // contain the subsequent statements. Otherwise jump back up to
                // the initial block.
                if let Some(event_cond) = event_cond {
                    let event_blk = self.add_named_block("event");
                    self.builder.ins().br_cond(event_cond, init_blk, event_blk);
                    self.builder.append_to(event_blk);
                }

                // Emit the actual statement.
                self.emit_stmt(stmt, env)?;
            }
            hir::StmtKind::Timed {
                control: hir::TimingControl::ImplicitEvent,
                stmt,
            } => {
                // Wait for any of the inputs to the statement to change.
                let trigger_blk = self.add_named_block("trigger");
                let mut trigger_on = vec![];
                let acc = self.accessed_nodes(stmt, env)?;
                for &id in &acc.read {
                    trigger_on.push(self.emitted_value(id).clone());
                }
                self.builder.ins().wait(trigger_blk, trigger_on);
                self.builder.append_to(trigger_blk);
                self.flush_mir(); // ensure we don't reuse earlier expr probe
                self.emit_shadow_update();

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
                let cond = self.emit_rvalue_bool(cond, env)?;
                self.builder.ins().br_cond(cond, else_blk, main_blk);
                let final_blk = self.add_named_block("if_exit");
                self.builder.append_to(main_blk);
                self.emit_stmt(main_stmt, env)?;
                self.builder.ins().br(final_blk);
                self.builder.append_to(else_blk);
                if let Some(else_stmt) = else_stmt {
                    self.emit_stmt(else_stmt, env)?;
                };
                self.builder.ins().br(final_blk);
                self.builder.append_to(final_blk);
            }
            hir::StmtKind::Loop { kind, body } => {
                let body_blk = self.add_named_block("loop_body");
                let exit_blk = self.add_named_block("loop_exit");

                // Emit the loop initialization.
                let repeat_var = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(count) => {
                        let ty = self.type_of(count, env)?;
                        let count = self.emit_rvalue(count, env)?;
                        let var = self.builder.ins().var(count);
                        self.builder.set_name(var, "loop_count".to_string());
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
                self.builder.ins().br(body_blk);
                self.builder.append_to(body_blk);
                let enter_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let lty = self.emit_type(ty)?;
                        let value = self.builder.ins().ld(repeat_var);
                        let zero = self.emit_zero_for_type(&lty);
                        Some(self.builder.ins().neq(value, zero))
                    }
                    hir::LoopKind::While(cond) => Some(self.emit_rvalue_bool(cond, env)?),
                    hir::LoopKind::Do(_) => None,
                    hir::LoopKind::For(_, cond, _) => Some(self.emit_rvalue_bool(cond, env)?),
                };
                if let Some(enter_cond) = enter_cond {
                    let entry_blk = self.add_named_block("loop_continue");
                    self.builder.ins().br_cond(enter_cond, exit_blk, entry_blk);
                    self.builder.append_to(entry_blk);
                }

                // Emit the loop body.
                self.emit_stmt(body, env)?;

                // Emit the epilogue.
                let continue_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let value = self.builder.ins().ld(repeat_var);
                        let one = self
                            .builder
                            .ins()
                            .const_int((ty.get_bit_size().unwrap(), 0));
                        let value = self.builder.ins().sub(value, one);
                        self.builder.ins().st(repeat_var, value);
                        None
                    }
                    hir::LoopKind::While(_) => None,
                    hir::LoopKind::Do(cond) => Some(self.emit_rvalue_bool(cond, env)?),
                    hir::LoopKind::For(_, _, step) => {
                        self.emit_rvalue(step, env)?;
                        None
                    }
                };
                match continue_cond {
                    Some(cond) => self.builder.ins().br_cond(cond, exit_blk, body_blk),
                    None => self.builder.ins().br(body_blk),
                };
                self.builder.append_to(exit_blk);
            }
            hir::StmtKind::InlineGroup { ref stmts, .. } => {
                for &stmt in stmts {
                    self.emit_stmt(stmt, env)?;
                }
            }

            hir::StmtKind::Case {
                expr,
                ref ways,
                default,
                kind,
            } => {
                let expr = self.emit_rvalue(expr, env)?;
                let final_blk = self.add_named_block("case_exit");
                for &(ref way_exprs, stmt) in ways {
                    let mut last_check = self.builder.ins().const_int((1, 0));
                    for &way_expr in way_exprs {
                        // Determine the constant value of the label.
                        let way_const = self.constant_value_of(way_expr, env);
                        let (_, special_bits, x_bits) = match &way_const.kind {
                            ValueKind::Int(v, s, x) => (v, s, x),
                            _ => panic!("case constant evaluates to non-integer"),
                        };
                        let way_expr = self.emit_const(way_const, env, self.span(way_expr))?;
                        let way_width = self.llhd_type(way_expr).unwrap_int();

                        // Generate the comparison mask based on the case kind.
                        let mask = match kind {
                            ast::CaseKind::Normal => None,
                            ast::CaseKind::DontCareZ => {
                                let mut mask = special_bits.clone();
                                mask.difference(x_bits);
                                mask.negate();
                                Some(mask)
                            }
                            ast::CaseKind::DontCareXZ => {
                                let mut mask = special_bits.clone();
                                mask.negate();
                                Some(mask)
                            }
                        };
                        let mask = mask.map(|bits| {
                            let mut mask = BigInt::zero();
                            for b in &bits {
                                mask <<= 1;
                                if b {
                                    mask |= BigInt::one();
                                }
                            }
                            self.builder.ins().const_int((way_width, mask))
                        });

                        // Filter the comparison values through the mask.
                        let (lhs, rhs) = match mask {
                            Some(mask) => (
                                self.builder.ins().and(expr, mask),
                                self.builder.ins().and(way_expr, mask),
                            ),
                            None => (expr, way_expr),
                        };

                        // Perform the comparison and branch.
                        let check = self.builder.ins().eq(lhs, rhs);
                        last_check = self.builder.ins().or(last_check, check);
                    }
                    let taken_blk = self.add_named_block("case_body");
                    let untaken_blk = self.add_nameless_block();
                    self.builder
                        .ins()
                        .br_cond(last_check, untaken_blk, taken_blk);
                    self.builder.append_to(taken_blk);
                    self.emit_stmt(stmt, env)?;
                    self.builder.ins().br(final_blk);
                    self.builder.append_to(untaken_blk);
                }
                if let Some(default) = default {
                    self.emit_stmt(default, env)?;
                }
                self.builder.ins().br(final_blk);
                self.builder.append_to(final_blk);
            }

            _ => {
                error!("{:#?}", hir);
                return self.unimp_msg("code generation for", hir);
            }
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
        let ty = self.type_of_var_decl(
            Ref(self
                .ast_for_id(decl_id)
                .as_all()
                .get_var_decl_name()
                .unwrap()),
            env,
        );
        let ty = self.emit_type(ty)?;
        let init = match hir.init {
            Some(expr) => self.emit_rvalue(expr, env)?,
            None => self.emit_zero_for_type(&ty),
        };
        let value = self.builder.ins().var(init);
        self.builder.set_name(value, hir.name.value.to_string());
        self.set_emitted_value(decl_id, value);
        Ok(())
    }

    /// Emit the code to check if a certain edge occurred between two values.
    fn emit_event_trigger(
        &mut self,
        edge: ast::EdgeIdent,
        prev: llhd::ir::Value,
        now: llhd::ir::Value,
    ) -> Result<llhd::ir::Value> {
        let ty = self.llhd_type(now);

        // Check if a posedge happened.
        let posedge = match edge {
            ast::EdgeIdent::Posedge | ast::EdgeIdent::Edge => {
                let zero = self.emit_zero_for_type(&ty);
                let prev_eq_0 = self.builder.ins().eq(prev, zero);
                let now_neq_0 = self.builder.ins().neq(now, zero);
                let value = self.builder.ins().and(prev_eq_0, now_neq_0);
                self.builder.set_name(value, "posedge".to_string());
                Some(value)
            }
            _ => None,
        };

        // Check if a negedge happened.
        let negedge = match edge {
            ast::EdgeIdent::Negedge | ast::EdgeIdent::Edge => {
                let zero = self.emit_zero_for_type(&ty);
                let prev_neq_0 = self.builder.ins().neq(prev, zero);
                let now_eq_0 = self.builder.ins().eq(now, zero);
                let value = self.builder.ins().and(now_eq_0, prev_neq_0);
                self.builder.set_name(value, "negedge".to_string());
                Some(value)
            }
            _ => None,
        };

        // Combine the two edge triggers, or emit an implicit edge check if none
        // of the above edges was checked.
        Ok(match (posedge, negedge) {
            (Some(a), Some(b)) => {
                let value = self.builder.ins().or(a, b);
                self.builder.set_name(value, "edge".to_string());
                value
            }
            (Some(a), None) => a,
            (None, Some(b)) => b,
            (None, None) => {
                let value = self.builder.ins().neq(prev, now);
                self.builder.set_name(value, "impledge".to_string());
                value
            }
        })
    }

    /// Emit a blocking assignment on MIR nodes.
    fn emit_mir_blocking_assign(
        &mut self,
        lvalue: &'gcx mir::Lvalue<'gcx>,
        rvalue: &'gcx mir::Rvalue<'gcx>,
    ) -> Result<()> {
        let lv = self.emit_mir_lvalue(lvalue)?;
        let rv = self.emit_mir_rvalue(rvalue)?;
        self.emit_blocking_assign_llhd(lv, rv)
    }

    /// Emit a blocking assignment to a variable or signal.
    fn emit_blocking_assign_llhd(
        &mut self,
        lvalue: (llhd::ir::Value, Option<llhd::ir::Value>),
        rvalue: llhd::ir::Value,
    ) -> Result<()> {
        let mut assign = |lvalue| {
            let lty = self.llhd_type(lvalue);
            match *lty {
                llhd::SignalType(..) => {
                    let one_epsilon = llhd::value::TimeValue::new(num::zero(), 0, 1);
                    let one_epsilon = self.builder.ins().const_time(one_epsilon);
                    self.builder.ins().drv(lvalue, rvalue, one_epsilon);
                    // // Emit a wait statement to allow for the assignment to take
                    // // effect.
                    // let blk = self.add_nameless_block();
                    // self.builder.ins().wait_time(blk, one_epsilon, vec![]);
                    // self.builder.append_to(blk);
                }
                llhd::PointerType(..) => {
                    self.builder.ins().st(lvalue, rvalue);
                }
                ref t => panic!("value of type `{}` cannot be driven", t),
            }
        };
        assign(lvalue.0);
        if let Some(lv) = lvalue.1 {
            assign(lv);
        }
        Ok(())
    }

    /// Emit the code to update the shadow variables of signals.
    fn emit_shadow_update(&mut self) {
        for (&id, &shadow) in &self.shadows {
            let value = self.builder.ins().prb(self.values[&id.into()]);
            self.builder.ins().st(shadow, value);
        }
    }

    /// Emit the code for a variable or net declaration.
    fn emit_varnet_decl(
        &mut self,
        decl_id: NodeId,
        ty: &'gcx UnpackedType<'gcx>,
        env: ParamEnv,
        default: Option<NodeId>,
    ) -> Result<llhd::ir::Value> {
        // Check if this is a variable or a net declaration.
        let is_var = match self.hir_of(decl_id)? {
            HirNode::VarDecl(x) => x.kind.is_var(),
            HirNode::IntPort(x) => x.kind.is_var(),
            x => unreachable!("emit_varnet_decl on HIR {:?}", x),
        };

        // Differentiate between variable and net declarations, which have
        // slightly different semantics regarding their initial value.
        if is_var {
            // For variables we require that the initial value is a
            // constant.
            let init = self.emit_const(
                match default {
                    Some(expr) => self.constant_value_of(expr, env),
                    None => self.type_default_value(ty),
                },
                env,
                self.span(default.unwrap_or(decl_id)),
            )?;
            Ok(self.builder.ins().sig(init))
        } else {
            // For nets we simply emit the initial value as a signal, then
            // short-circuit it with the net declaration.
            let zero = self.emit_const(self.type_default_value(ty), env, self.span(decl_id))?;
            let net = self.builder.ins().sig(zero);
            if let Some(default) = default {
                let init = self.emit_rvalue_mode(default, env, Mode::Signal)?;
                self.builder.ins().con(net, init);
            }
            Ok(net)
        }
    }
}

/// An rvalue emission mode.
///
/// Upon code emission, rvalues may be emitted either as direct values,
/// pointers, or signals. This enum is used to communicate the intent to the
/// corresopnding functions.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Mode {
    Value,
    // Pointer,
    Signal,
}

// /// Different binary ops that may be emitted.
// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
// enum BinaryOp {
//     Add,
//     Sub,
//     And,
//     Or,
//     Xor,
// }

/// Directions of the shift operation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ShiftDir {
    Left,
    Right,
}

/// Emit a detailed description of a module's ports.
///
/// Called when the PORTS verbosity flag is set.
fn emit_port_details<'gcx>(cx: &impl Context<'gcx>, hir: &hir::Module<'gcx>, env: ParamEnv) {
    trace!("Port details of {:#?}", hir.ports_new);
    println!("Ports of `{}`:", hir.name);

    // Dump the internal ports.
    println!("  internal:");
    for (i, port) in hir.ports_new.int.iter().enumerate() {
        println!(
            "    {}: {} {} {} {}",
            i,
            port.dir,
            port.kind,
            cx.type_of_int_port(Ref(port), env),
            port.name
        );
    }

    // Dump the external ports.
    println!("  external:");
    for (i, port) in hir.ports_new.ext_pos.iter().enumerate() {
        print!("    {}: ", i);
        if let Some(name) = port.name {
            print!(".{}(", name);
        }
        if port.exprs.len() > 1 {
            print!("{{");
        }
        for (expr, sep) in port.exprs.iter().zip(once("").chain(repeat(", "))) {
            print!("{}{}", sep, hir.ports_new.int[expr.port].name);
            for select in &expr.selects {
                match select {
                    hir::ExtPortSelect::Error => (),
                    hir::ExtPortSelect::Index(_mode) => {
                        print!("[..]");
                    }
                }
            }
        }
        if port.exprs.len() > 1 {
            print!("}}");
        }
        if port.name.is_some() {
            print!(")");
        }
        // TODO: Dump the external port type.
        println!();
    }
}

/// Result of emitting a module.
pub struct EmittedModule<'a> {
    /// The emitted LLHD unit.
    unit: llhd::ir::UnitId,
    /// The module's ports.
    ports: ModuleIntf<'a>,
}

/// Result of emitting a procedure.
pub struct EmittedProcedure {
    /// The emitted LLHD unit.
    unit: llhd::ir::UnitId,
    /// The nodes used exclusively as rvalues.
    inputs: Vec<AccessedNode>,
    /// The nodes used as lvalues.
    outputs: Vec<AccessedNode>,
}

/// A module's port interface.
#[derive(Debug)]
pub struct ModuleIntf<'a> {
    /// The signature of the module.
    pub sig: llhd::ir::Signature,
    /// The inputs to the module.
    pub inputs: Vec<ModulePort<'a>>,
    /// The outputs of the module.
    pub outputs: Vec<ModulePort<'a>>,
}

/// A canonicalized port of a module.
#[derive(Debug)]
pub struct ModulePort<'a> {
    /// The original port that generated this port. One `IntPort`s may spawn
    /// multiple module ports, e.g. in an interface.
    pub port: &'a port_list::IntPort<'a>,
    /// The type of the port.
    pub ty: &'a UnpackedType<'a>,
    /// The preferred name in the LLHD IR.
    pub name: String,
    /// The corresponding `AccessedNode` specifier.
    pub accnode: AccessedNode,
    /// The default value assigned to this port.
    pub default: Option<NodeId>,
    /// The kind of port.
    pub kind: ModulePortKind<'a>,
}

/// The different kinds of module ports.
#[derive(Debug)]
pub enum ModulePortKind<'a> {
    /// A regular port.
    Port,
    /// An interface signal.
    IntfSignal {
        intf: &'a ast::Interface<'a>,
        env: ParamEnv,
        decl_id: NodeId,
    },
}

/// An signal within an interface.
#[derive(Debug)]
pub struct IntfSignal<'a> {
    /// The node that declared this signal. Usually a `VarDecl`, `NetDecl`, or
    /// `PortDecl`.
    pub decl_id: NodeId,
    /// The type of the signal.
    pub ty: &'a UnpackedType<'a>,
    /// The name of the signal.
    pub name: Spanned<Name>,
    /// The expression assigned as default to the signal.
    pub default: Option<NodeId>,
}

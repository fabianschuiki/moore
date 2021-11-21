// Copyright (c) 2016-2021 Fabian Schuiki

//! This module implements LLHD code generation.
#![allow(unreachable_code)]

use crate::{
    crate_prelude::*,
    hir::{AccessedNode, HirNode},
    port_list::PortList,
    resolver::InstTarget,
    ty::UnpackedType,
    value::{Value, ValueKind},
    ParamEnv,
};
use circt::comb::CmpPred;
use circt::mlir;
use circt::prelude::*;
use num::{BigInt, FromPrimitive, One, ToPrimitive, Zero};
use std::{
    collections::{HashMap, HashSet},
    iter::{once, repeat},
    ops::{Deref, DerefMut},
    rc::Rc,
};

pub type HybridValue = (llhd::ir::Value, mlir::Value);
pub type HybridType = (llhd::Type, mlir::Type);
pub type HybridBlock = (llhd::ir::Block, mlir::Block);

/// A code generator.
///
/// Use this struct to emit LLHD code for nodes in a [`Context`].
pub struct CodeGenerator<'gcx, C> {
    /// The compilation context.
    cx: C,
    /// The MLIR compilation context.
    mcx: mlir::Context,
    /// The LLHD module to be populated.
    into: llhd::ir::Module,
    /// THe MLIR module to be populated.
    into_mlir: circt::ModuleOp,
    /// Tables holding mappings and interned values.
    tables: Tables<'gcx>,
}

impl<'gcx, C> CodeGenerator<'gcx, C> {
    /// Create a new code generator.
    pub fn new(cx: C, into_mlir: circt::ModuleOp) -> Self {
        CodeGenerator {
            cx,
            mcx: into_mlir.context(),
            into: llhd::ir::Module::new(),
            into_mlir,
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
    interned_types: HashMap<&'gcx UnpackedType<'gcx>, Result<HybridType>>,
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

        // Create MLIR entity.
        let mlir_cx = self.into_mlir.context();
        let mut mlir_builder = mlir::Builder::new(mlir_cx);
        mlir_builder.set_loc(span_to_loc(mlir_cx, hir.span()));
        mlir_builder.set_insertion_point_to_end(self.into_mlir.block());
        let mut entity_op = circt::llhd::EntityLikeBuilder::new(&entity_name);
        for port in ports.inputs.iter() {
            entity_op.add_input(&port.name, port.mty);
        }
        for port in ports.outputs.iter() {
            entity_op.add_output(&port.name, port.mty);
        }
        let entity_op = entity_op.build_entity(&mut mlir_builder);
        mlir_builder.set_insertion_point_to_start(entity_op.block());

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
            mlir_builder: &mut mlir_builder,
            interned_consts: Default::default(),
            interned_lvalues: Default::default(),
            interned_rvalues: Default::default(),
            shadows: Default::default(),
        };

        // Assign proper port names and collect ports into a lookup table.
        for (index, port) in ports.inputs.iter().enumerate() {
            let arg = gen.builder.input_arg(index);
            gen.builder.set_name(arg, port.name.clone());
            gen.values
                .insert(port.accnode, (arg, entity_op.input(index)));
        }
        for (index, port) in ports.outputs.iter().enumerate() {
            let arg = gen.builder.output_arg(index);
            gen.builder.set_name(arg, port.name.clone());
            gen.values
                .insert(port.accnode, (arg, entity_op.output(index)));
        }

        debug!("  Ports:");
        for (node, value) in gen.values.iter() {
            debug!(
                "    {:?} = {:?} (type {})",
                node,
                value,
                gen.llhd_type(value.0),
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
                    llhd::ir::Opcode::Drv => gen.builder[inst].args()[0] == value.0,
                    llhd::ir::Opcode::Inst => gen.builder[inst].output_args().contains(&value.0),
                    _ => false,
                });
            if driven {
                continue;
            }
            let default_value = gen.emit_const_both(
                if let Some(default) = port.default {
                    gen.constant_value_of(default, env)
                } else {
                    gen.type_default_value(port.ty)
                },
                env,
                port.port.span(),
            )?;
            let zero_time = llhd::value::TimeValue::new(num::zero(), 0, 0);
            let zero_time = (
                gen.builder.ins().const_time(zero_time),
                circt::llhd::ConstantTimeOp::with_delta(gen.mlir_builder, 1).into(),
            );
            gen.mk_drv(value, default_value, zero_time);
        }

        let unit = self.into.add_unit(ent);
        let result = Ok(Rc::new(EmittedModule {
            unit,
            mlir_symbol: entity_name.clone(),
            ports,
        }));
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
                    let (llty, mty) = signal_ty(self.emit_type_both(signal.ty)?);
                    let name = format!("{}.{}", port.name, signal.name);
                    trace!(
                        "    Signal `{}` of type `{}` / `{}` / `{}`",
                        name,
                        signal.ty,
                        llty,
                        mty
                    );
                    let port = ModulePort {
                        port,
                        ty: signal.ty,
                        mty,
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
                let (llty, mty) = signal_ty(self.emit_type_both(ty)?);
                let name = port.name.to_string();
                let mp = ModulePort {
                    port,
                    ty,
                    mty,
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
        let mut mlir_inputs = vec![];
        let mut mlir_outputs = vec![];
        for &id in acc.read.iter().filter(|id| !acc.written.contains(id)) {
            let ty = self.emit_type_both(match id {
                AccessedNode::Regular(id) => self.type_of(id, env)?,
                AccessedNode::Intf(intf, id) => {
                    let intf_ty = self.type_of(intf, env)?;
                    let intf_ty_inner = intf_ty.resolve_full().core.get_interface().unwrap();
                    let mut sig_ty = self.type_of(id, intf_ty_inner.env)?.clone();
                    sig_ty.dims.extend(&intf_ty.dims);
                    sig_ty.intern(self.cx)
                }
            })?;
            sig.add_input(llhd::signal_ty(ty.0));
            mlir_inputs.push(ty.1);
            inputs.push(id);
        }
        for &id in acc.written.iter() {
            let ty = self.emit_type_both(match id {
                AccessedNode::Regular(id) => self.type_of(id, env)?,
                AccessedNode::Intf(intf, id) => {
                    let intf_ty = self.type_of(intf, env)?;
                    let intf_ty_inner = intf_ty.resolve_full().core.get_interface().unwrap();
                    let mut sig_ty = self.type_of(id, intf_ty_inner.env)?.clone();
                    sig_ty.dims.extend(&intf_ty.dims);
                    sig_ty.intern(self.cx)
                }
            })?;
            sig.add_output(llhd::signal_ty(ty.0));
            mlir_outputs.push(ty.1);
            outputs.push(id);
        }
        trace!("Process Inputs: {:?}", inputs);
        trace!("Process Outputs: {:?}", outputs);
        trace!("Process Signature: {}", sig);
        trace!("Process MLIR Inputs: {:?}", mlir_inputs);
        trace!("Process MLIR Outputs: {:?}", mlir_outputs);
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
            llhd::ir::UnitName::Local(proc_name.clone()),
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

        // Create MLIR process.
        let mut mlir_builder = mlir::Builder::new(self.mcx);
        mlir_builder.set_loc(span_to_loc(self.mcx, hir.span()));
        mlir_builder.set_insertion_point_to_end(self.into_mlir.block());

        let mut proc_op = circt::llhd::EntityLikeBuilder::new(&proc_name);
        for ty in mlir_inputs {
            proc_op.add_input("", circt::llhd::get_signal_type(ty));
        }
        for ty in mlir_outputs {
            proc_op.add_output("", circt::llhd::get_signal_type(ty));
        }
        let proc_op = proc_op.build_process(&mut mlir_builder);
        mlir_builder.set_insertion_point_to_start(proc_op.first_block());

        // Create a mapping from read/written nodes to process parameters.
        let mut values = HashMap::<_, HybridValue>::new();
        mlir_builder.set_loc(span_to_loc(self.mcx, hir.span()));
        for ((&id, arg), mlir_port) in inputs
            .iter()
            .zip(builder.input_args())
            .chain(outputs.iter().zip(builder.output_args()))
            .zip(proc_op.ports())
        {
            values.insert(id.into(), (arg, mlir_port));
        }
        let mut pg = UnitGenerator {
            gen: self,
            builder: &mut builder,
            values: &mut values,
            mlir_builder: &mut mlir_builder,
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
            let value = pg.values[&id.into()];
            let init = pg.mk_prb(value);
            let shadow = pg.mk_var(init);
            if let Some(name) = pg
                .builder
                .get_name(value.0)
                .map(|name| format!("{}.shadow", name))
            {
                pg.builder.set_name(shadow.0, name);
            }
            pg.shadows.insert(id.into(), shadow);
        }

        // Emit prologue and determine which basic block to jump back to.
        let head_blk = match hir.kind {
            ast::ProcedureKind::AlwaysComb | ast::ProcedureKind::AlwaysLatch => {
                let body_blk = (pg.add_named_block("body"), pg.mlir_builder.add_block());
                let check_blk = (pg.add_named_block("check"), pg.mlir_builder.add_block());
                pg.builder.ins().br(body_blk.0);
                pg.builder.append_to(check_blk.0);
                circt::std::BranchOp::new(pg.mlir_builder, body_blk.1);
                pg.mlir_builder.set_insertion_point_to_end(check_blk.1);
                let trigger_on = inputs
                    .iter()
                    .map(|id| pg.emitted_value_both(*id).0.clone())
                    .collect();
                pg.builder.ins().wait(body_blk.0, trigger_on);
                pg.builder.append_to(body_blk.0);
                circt::llhd::WaitOp::new(
                    pg.mlir_builder,
                    body_blk.1,
                    inputs
                        .iter()
                        .map(|id| pg.emitted_value_both(*id).1)
                        .collect::<Vec<_>>(),
                    None,
                );
                pg.mlir_builder.set_insertion_point_to_end(body_blk.1);
                pg.flush_mir(); // ensure we don't reuse earlier expr probe
                pg.emit_shadow_update();
                Some(check_blk)
            }
            ast::ProcedureKind::Final => {
                // TODO(fschuiki): Replace this with a cleverer way to implement a trigger-on-end.
                let body_blk = (pg.add_named_block("body"), pg.mlir_builder.add_block());
                let endtimes = pg.builder.ins().const_time(llhd::value::TimeValue::new(
                    "9001".parse().unwrap(),
                    0,
                    0,
                ));
                pg.builder.set_name(endtimes, "endtimes".to_string());
                pg.builder.ins().wait_time(body_blk.0, endtimes, vec![]);
                pg.builder.append_to(body_blk.0);
                let endtimes = circt::llhd::ConstantTimeOp::with_seconds(
                    pg.mlir_builder,
                    &BigInt::from_i64(std::i64::MAX / 1_000_000_000_000)
                        .unwrap()
                        .into(),
                )
                .into();
                circt::llhd::WaitOp::new(pg.mlir_builder, body_blk.1, None, Some(endtimes));
                pg.mlir_builder.set_insertion_point_to_start(body_blk.1);
                pg.flush_mir(); // ensure we don't reuse earlier expr probe
                pg.emit_shadow_update();
                None
            }
            ast::ProcedureKind::Initial => None,
            _ => {
                let mlir_entry_blk = pg.mlir_builder.add_block();
                circt::std::BranchOp::new(pg.mlir_builder, mlir_entry_blk);
                pg.mlir_builder.set_insertion_point_to_end(mlir_entry_blk);
                Some((entry_blk, mlir_entry_blk))
            }
        };

        // Emit the main statement.
        pg.emit_stmt(hir.stmt, env)?;

        // Emit epilogue.
        match hir.kind {
            ast::ProcedureKind::Initial | ast::ProcedureKind::Final => {
                pg.builder.ins().halt();
                circt::llhd::HaltOp::new(pg.mlir_builder);
            }
            ast::ProcedureKind::Always
            | ast::ProcedureKind::AlwaysComb
            | ast::ProcedureKind::AlwaysLatch
            | ast::ProcedureKind::AlwaysFf => {
                pg.builder.ins().br(head_blk.unwrap().0);
                circt::std::BranchOp::new(pg.mlir_builder, head_blk.unwrap().1);
            }
        }

        Ok(EmittedProcedure {
            unit: self.into.add_unit(prok),
            mlir_symbol: proc_name.clone(),
            inputs,
            outputs,
        })
    }

    /// Map a type to an LLHD type (interned).
    fn emit_type(&mut self, ty: &'gcx UnpackedType<'gcx>) -> Result<llhd::Type> {
        self.emit_type_both(ty).map(|x| x.0)
    }

    /// Map a type to an LLHD type (interned).
    fn emit_type_both(&mut self, ty: &'gcx UnpackedType<'gcx>) -> Result<HybridType> {
        if let Some(x) = self.tables.interned_types.get(&ty) {
            x.clone()
        } else {
            let x = self.emit_type_uninterned(ty);
            self.tables.interned_types.insert(ty, x.clone());
            x
        }
    }

    /// Map a type to an LLHD type.
    fn emit_type_uninterned(&mut self, ty: &'gcx UnpackedType<'gcx>) -> Result<HybridType> {
        if ty.is_error() {
            return Err(());
        }
        let ty = ty.resolve_full();

        // Handle things that coalesce easily to scalars.
        if ty.coalesces_to_llhd_scalar() {
            let bits = ty.get_bit_size().unwrap();
            return Ok((llhd::int_ty(bits), mlir::get_integer_type(self.mcx, bits)));
        }

        // Handle arrays.
        if let Some(dim) = ty.outermost_dim() {
            let size = match dim.get_size() {
                Some(size) => size,
                None => panic!("cannot map unsized array `{}` to LLHD", ty),
            };
            let inner = ty.pop_dim(self.cx).unwrap();
            let (llty, mty) = self.emit_type_both(inner)?;
            return Ok((
                llhd::array_ty(size, llty),
                circt::hw::get_array_type(mty, size),
            ));
        }

        // Handle structs.
        if let Some(strukt) = ty.get_struct() {
            let mut types = vec![];
            let mut mtypes: Vec<(crate::common::name::RcStr, mlir::Type)> = vec![];
            for member in &strukt.members {
                let (llty, mty) = self.emit_type_both(member.ty)?;
                types.push(llty);
                mtypes.push((member.name.value.as_str(), mty));
            }
            return Ok((
                llhd::struct_ty(types),
                circt::hw::get_struct_type(self.mcx, mtypes),
            ));
        }

        // Handle packed types.
        if let Some(packed) = ty.get_packed() {
            let packed = packed.resolve_full();
            return match packed.core {
                // CAVEAT: We just use an empty HW dialect struct type as a
                // stand-in for an error or void type.
                ty::PackedCore::Void | ty::PackedCore::Error => Ok((
                    llhd::void_ty(),
                    circt::hw::get_struct_type(self.mcx, Option::<(String, mlir::Type)>::None),
                )),
                ty::PackedCore::IntAtom(ty::IntAtomType::Time) => {
                    Ok((llhd::time_ty(), circt::llhd::get_time_type(self.mcx)))
                }
                ty::PackedCore::Enum(ref enm) => self.emit_type_both(enm.base.to_unpacked(self.cx)),
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
    values: &'a mut HashMap<AccessedNode, HybridValue>,
    /// The MLIR builder which is used to create new operations.
    mlir_builder: &'a mut mlir::Builder,
    /// The constant values emitted into the unit.
    interned_consts: HashMap<Value<'gcx>, Result<HybridValue>>,
    /// The MIR lvalues emitted into the unit.
    interned_lvalues: HashMap<NodeId, Result<(HybridValue, Option<HybridValue>)>>,
    /// The MIR rvalues emitted into the unit.
    interned_rvalues: HashMap<(NodeId, Mode), Result<(HybridValue, Mode)>>,
    /// The shadow variables introduced to handle signals which are both read
    /// and written in a process.
    shadows: HashMap<AccessedNode, HybridValue>,
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
        self.emitted_value_both(src).0
    }

    fn emitted_value_both(&self, src: impl Into<AccessedNode>) -> HybridValue {
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

    fn set_emitted_value(&mut self, src: impl Into<AccessedNode>, value: HybridValue) {
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
            self.builder.set_name(value.0, hir.name.value.into());
            self.values.insert(decl_id.into(), value);
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
                    .set_name(value.0, format!("{}.{}", inst.hir.name, signal.name));
                let src = AccessedNode::Intf(inst_id, signal.decl_id);
                trace!(
                    "Emitted value for {:?} {}.{}",
                    src,
                    inst.hir.name,
                    signal.name
                );
                self.values.insert(src, value);
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
                let sig = signal_lookup[&port.port.id];
                self.builder.ins().con(sig.0, assigned.0);
                circt::llhd::ConnectOp::new(self.mlir_builder, sig.1, assigned.1);
            }
        }

        // Emit assignments.
        for &assign_id in &hir.assigns {
            let hir = match self.hir_of(assign_id)? {
                HirNode::Assign(x) => x,
                _ => unreachable!(),
            };

            // Map the assignment to an MIR node.
            let assign_mir = self.mir_assignment_from_concurrent(Ref(hir), env);
            debug!("Concurrent assignment: {:#?}", assign_mir);

            // Simplify the assignment to eliminate concatenations on the
            // left-hand side.
            let simplified = self.mir_simplify_assignment(Ref(assign_mir));
            debug!("Simplified to: {:#?}", simplified);

            // Check for sanity.
            for &assign in &simplified {
                assert_type!(assign.rhs.ty, assign.lhs.ty, assign.rhs.span, self.cx);
                if assign.is_error() {
                    return Err(());
                }
            }

            // Emit the assignments.
            let delay = llhd::value::TimeValue::new(num::zero(), 0, 1);
            let delay = (
                self.builder.ins().const_time(delay),
                circt::llhd::ConstantTimeOp::with_epsilon(self.mlir_builder, 1).into(),
            );
            for &assign in &simplified {
                let lhs = self.emit_mir_lvalue_both(assign.lhs)?;
                let rhs = self.emit_mir_rvalue_both(assign.rhs)?;
                self.mk_drv(lhs.0, rhs, delay);
            }
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
            self.builder.ins().inst(
                ext_unit,
                inputs.iter().map(|x| x.0).collect(),
                outputs.iter().map(|x| x.0).collect(),
            );
            circt::llhd::InstanceOp::new(
                self.mlir_builder,
                &inst.hir.name.value.to_string(),
                &target.mlir_symbol,
                inputs.iter().map(|x| x.1),
                outputs.iter().map(|x| x.1),
            );
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
            let inputs: Vec<_> = prok.inputs.iter().map(lookup_value).collect();
            let outputs: Vec<_> = prok.outputs.iter().map(lookup_value).collect();
            let ext_unit = self.builder.add_extern(
                self.into.unit(prok.unit).name().clone(),
                self.into.unit(prok.unit).sig().clone(),
            );
            self.builder.ins().inst(
                ext_unit,
                inputs.iter().map(|x| x.0).collect(),
                outputs.iter().map(|x| x.0).collect(),
            );
            circt::llhd::InstanceOp::new(
                self.mlir_builder,
                "",
                &prok.mlir_symbol,
                inputs.iter().map(|x| x.1),
                outputs.iter().map(|x| x.1),
            );
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
    ) -> Result<(Vec<HybridValue>, Vec<HybridValue>)> {
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
                    self.emit_mir_lvalue_both(mir).map(|x| x.0)
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
                        let v = self.emit_const_both(v, inst.inner_env, port.port.span)?;
                        (
                            self.builder.ins().sig(v.0),
                            circt::llhd::SignalOp::new(self.mlir_builder, "", v.1).into(),
                        )
                    }
                };
                self.builder
                    .set_name(value.0, format!("{}.{}.default", inst.hir.name, port.name));
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
        self.emit_const_both(value, env, span).map(|x| x.0)
    }

    /// Map a value to an LLHD constant (interned).
    fn emit_const_both(
        &mut self,
        value: Value<'gcx>,
        env: ParamEnv,
        span: Span,
    ) -> Result<HybridValue> {
        if let Some(x) = self.interned_consts.get(value) {
            x.clone()
        } else {
            let x = self.emit_const_uninterned(value, env, span);
            debug!("Emitted constant {:?}", x);
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
    ) -> Result<HybridValue> {
        if value.ty.is_error() {
            return Err(());
        }
        match value.kind {
            ValueKind::Int(ref k, ..) => {
                let size = value.ty.simple_bit_vector(self.cx, span).size;
                Ok((
                    self.builder.ins().const_int((size, k.clone())),
                    circt::hw::ConstantOp::new(self.mlir_builder, size, k).into(),
                ))
            }
            ValueKind::Time(ref k) => Ok((
                self.builder
                    .ins()
                    .const_time(llhd::value::TimeValue::new(k.clone(), 0, 0)),
                circt::llhd::ConstantTimeOp::with_seconds(self.mlir_builder, k).into(),
            )),
            ValueKind::StructOrArray(ref v) => {
                let ty = self.emit_type_both(value.ty)?;
                let mut ll_fields = vec![];
                let mut mlir_fields = vec![];
                for field in v {
                    let field = self.emit_const_both(field, env, span)?;
                    ll_fields.push(field.0);
                    mlir_fields.push(field.1);
                }
                if let Some(_dim) = value.ty.outermost_dim() {
                    Ok((
                        self.builder.ins().array(ll_fields),
                        circt::hw::ArrayCreateOp::new(self.mlir_builder, ty.1, mlir_fields).into(),
                    ))
                } else if let Some(_strukt) = value.ty.get_struct() {
                    Ok((
                        self.builder.ins().strukt(ll_fields),
                        circt::hw::StructCreateOp::new(self.mlir_builder, ty.1, mlir_fields).into(),
                    ))
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

    /// Emit the zero value for an MLIR type.
    fn emit_zero_for_type_mlir(&mut self, ty: mlir::Type) -> mlir::Value {
        if circt::hw::is_array_type(ty) {
            let inner = self.emit_zero_for_type_mlir(circt::hw::array_type_element(ty));
            circt::hw::ArrayCreateOp::new(
                self.mlir_builder,
                ty,
                (0..circt::hw::array_type_size(ty)).map(|_| inner),
            )
            .into()
        } else if circt::hw::is_struct_type(ty) {
            let inner: Vec<_> = circt::hw::struct_type_fields(ty)
                .map(|(_, ty)| self.emit_zero_for_type_mlir(ty))
                .collect();
            circt::hw::StructCreateOp::new(self.mlir_builder, ty, inner).into()
        } else if circt::llhd::is_pointer_type(ty) {
            let inner = self.emit_zero_for_type_mlir(circt::llhd::pointer_type_element(ty));
            circt::llhd::VariableOp::new(self.mlir_builder, inner).into()
        } else if circt::llhd::is_signal_type(ty) {
            let inner = self.emit_zero_for_type_mlir(circt::llhd::signal_type_element(ty));
            circt::llhd::SignalOp::new(self.mlir_builder, "", inner).into()
        } else if circt::llhd::is_time_type(ty) {
            circt::llhd::ConstantTimeOp::with_delta(self.mlir_builder, 0).into()
        } else if mlir::is_integer_type(ty) {
            circt::hw::ConstantOp::new(
                self.mlir_builder,
                mlir::integer_type_width(ty),
                &BigInt::zero(),
            )
            .into()
        } else {
            panic!("no zero value for type {}", ty)
        }
    }

    /// Emit the zero value for a type.
    fn emit_zero_for_type_both(&mut self, ty: HybridType) -> HybridValue {
        (
            self.emit_zero_for_type(&ty.0),
            self.emit_zero_for_type_mlir(ty.1),
        )
    }

    /// Get the type of an LLHD value.
    fn llhd_type(&self, value: llhd::ir::Value) -> llhd::Type {
        self.builder.value_type(value)
    }

    /// Emit the code for an rvalue.
    fn emit_rvalue(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<llhd::ir::Value> {
        self.emit_rvalue_both(expr_id, env).map(|x| x.0)
    }

    /// Emit the code for an rvalue.
    fn emit_rvalue_both(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<HybridValue> {
        self.emit_rvalue_mode(expr_id, env, Mode::Value)
    }

    /// Emit the code for an rvalue.
    fn emit_rvalue_mode(
        &mut self,
        expr_id: NodeId,
        env: ParamEnv,
        mode: Mode,
    ) -> Result<HybridValue> {
        let mir = self.mir_rvalue(expr_id, env);
        self.emit_mir_rvalue_mode(mir, mode)
    }

    /// Emit the code for an MIR rvalue.
    fn emit_mir_rvalue(&mut self, mir: &'gcx mir::Rvalue<'gcx>) -> Result<llhd::ir::Value> {
        self.emit_mir_rvalue_both(mir).map(|x| x.0)
    }

    /// Emit the code for an MIR rvalue.
    fn emit_mir_rvalue_both(&mut self, mir: &'gcx mir::Rvalue<'gcx>) -> Result<HybridValue> {
        self.emit_mir_rvalue_mode(mir, Mode::Value)
    }

    /// Emit the code for an MIR rvalue.
    fn emit_mir_rvalue_mode(
        &mut self,
        mir: &'gcx mir::Rvalue<'gcx>,
        mode: Mode,
    ) -> Result<HybridValue> {
        let (value, actual_mode) = if let Some(x) = self.interned_rvalues.get(&(mir.id, mode)) {
            x.clone()?
        } else {
            let x = self.emit_mir_rvalue_uninterned(mir, mode);
            self.interned_rvalues.insert((mir.id, mode), x);
            x?
        };

        match (mode, actual_mode) {
            (Mode::Signal, Mode::Value) => {
                let ty = (self.llhd_type(value.0), value.1.ty());
                let init = self.emit_zero_for_type_both(ty);
                let sig = (
                    self.builder.ins().sig(init.0),
                    circt::llhd::SignalOp::new(self.mlir_builder, "", init.1).into(),
                );
                let delay = llhd::value::TimeValue::new(num::zero(), 1, 0);
                let delay_const = self.builder.ins().const_time(delay);
                self.builder.ins().drv(sig.0, value.0, delay_const);
                let delay_const =
                    circt::llhd::ConstantTimeOp::with_delta(self.mlir_builder, 1).into();
                circt::llhd::DriveOp::new(self.mlir_builder, sig.1, value.1, delay_const);
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
    ) -> Result<(HybridValue, Mode)> {
        let result = self.emit_mir_rvalue_inner(mir, mode_hint);
        match result {
            Ok((result, actual_mode)) => {
                let llty_exp = self.emit_type(mir.ty)?;
                let llty_exp = match actual_mode {
                    Mode::Value => llty_exp,
                    Mode::Signal => llhd::signal_ty(llty_exp),
                };
                let llty_act = self.llhd_type(result.0);
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
    ) -> Result<(HybridValue, Mode)> {
        // If the value is a constant, emit the fully folded constant value.
        if mir.is_const() {
            let value = self.const_mir_rvalue(mir.into());
            return self
                .emit_const_both(value, mir.env, mir.span)
                .map(|v| (v, Mode::Value));
        }

        let value: HybridValue = match mir.kind {
            mir::RvalueKind::Var(id) | mir::RvalueKind::Port(id) => {
                let sig = self
                    .shadows
                    .get(&id.into())
                    .cloned()
                    .unwrap_or_else(|| self.emitted_value_both(id));
                if mode_hint == Mode::Signal && self.llhd_type(sig.0).is_signal() {
                    return Ok((sig, Mode::Signal));
                } else {
                    self.emit_prb_or_var(sig)
                }
            }

            mir::RvalueKind::Intf(_) => {
                self.emit(
                    DiagBuilder2::error("interface cannot be used in an expression").span(mir.span),
                );
                return Err(());
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
                let value = self.emit_mir_rvalue_both(value)?;
                let ty = self.llhd_type(value.0);
                let zero = self.emit_zero_for_type_both((ty, value.1.ty()));
                self.mk_cmp(CmpPred::Neq, value, zero)
            }

            mir::RvalueKind::Truncate(target_width, value) => {
                let llvalue = self.emit_mir_rvalue_both(value)?;
                self.mk_ext_slice(llvalue, 0, target_width)
            }

            mir::RvalueKind::ZeroExtend(_, value) => {
                let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                let llty = self.emit_type_both(mir.ty)?;
                let result = self.emit_zero_for_type_both(llty);
                let value = self.emit_mir_rvalue_both(value)?;
                let result = self.mk_ins_slice(result, value, 0, width);
                self.builder.set_name(result.0, "zext".to_string());
                result
            }

            mir::RvalueKind::SignExtend(_, value) => {
                let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                let llty = self.emit_type_both(mir.ty)?;
                let value = self.emit_mir_rvalue_both(value)?;
                let sign = self.mk_ext_slice(value, width - 1, 1);
                let zeros = self.emit_zero_for_type_both(llty);
                let ones = self.mk_not(zeros);
                let mux = self.mk_mux(sign, ones, zeros);
                let result = self.mk_ins_slice(mux, value, 0, width);
                self.builder.set_name(result.0, "sext".to_string());
                result
            }

            mir::RvalueKind::ConstructArray(ref indices) => {
                let values = (0..indices.len())
                    .map(|i| self.emit_mir_rvalue_both(indices[&i]))
                    .collect::<Result<Vec<_>>>()?;
                let llty = self.emit_type_both(mir.ty)?;
                self.mk_array(llty, &values)
            }

            mir::RvalueKind::ConstructStruct(ref members) => {
                let members = members
                    .iter()
                    .map(|&v| self.emit_mir_rvalue_both(v))
                    .collect::<Result<Vec<_>>>()?;
                let llty = self.emit_type_both(mir.ty)?;
                self.mk_struct(llty, &members)
            }

            mir::RvalueKind::Const(k) => self.emit_const_both(k, mir.env, mir.span)?,

            mir::RvalueKind::Index {
                value,
                base,
                length,
            } => {
                let target = self.emit_mir_rvalue_both(value)?;
                self.emit_rvalue_index(value.ty, target, base, length)?
            }

            mir::RvalueKind::Member { value, field } => {
                let target = self.emit_mir_rvalue_both(value)?;
                let value = self.mk_ext_field(target, field);
                value
            }

            mir::RvalueKind::UnaryBitwise { op, arg } => {
                let arg = self.emit_mir_rvalue_both(arg)?;
                match op {
                    mir::UnaryBitwiseOp::Not => self.mk_not(arg),
                }
            }

            mir::RvalueKind::BinaryBitwise { op, lhs, rhs } => {
                let lhs = self.emit_mir_rvalue_both(lhs)?;
                let rhs = self.emit_mir_rvalue_both(rhs)?;
                match op {
                    mir::BinaryBitwiseOp::And => self.mk_and(lhs, rhs),
                    mir::BinaryBitwiseOp::Or => self.mk_or(lhs, rhs),
                    mir::BinaryBitwiseOp::Xor => self.mk_xor(lhs, rhs),
                }
            }

            mir::RvalueKind::IntComp {
                op, lhs, rhs, sign, ..
            } => {
                let lhs = self.emit_mir_rvalue_both(lhs)?;
                let rhs = self.emit_mir_rvalue_both(rhs)?;
                let signed = sign.is_signed();
                match op {
                    mir::IntCompOp::Eq => self.mk_cmp(CmpPred::Eq, lhs, rhs),
                    mir::IntCompOp::Neq => self.mk_cmp(CmpPred::Neq, lhs, rhs),
                    mir::IntCompOp::Lt if signed => self.mk_cmp(CmpPred::Slt, lhs, rhs),
                    mir::IntCompOp::Leq if signed => self.mk_cmp(CmpPred::Sle, lhs, rhs),
                    mir::IntCompOp::Gt if signed => self.mk_cmp(CmpPred::Sgt, lhs, rhs),
                    mir::IntCompOp::Geq if signed => self.mk_cmp(CmpPred::Sge, lhs, rhs),
                    mir::IntCompOp::Lt => self.mk_cmp(CmpPred::Ult, lhs, rhs),
                    mir::IntCompOp::Leq => self.mk_cmp(CmpPred::Ule, lhs, rhs),
                    mir::IntCompOp::Gt => self.mk_cmp(CmpPred::Ugt, lhs, rhs),
                    mir::IntCompOp::Geq => self.mk_cmp(CmpPred::Uge, lhs, rhs),
                }
            }

            mir::RvalueKind::IntUnaryArith { op, arg, .. } => {
                let arg = self.emit_mir_rvalue_both(arg)?;
                match op {
                    mir::IntUnaryArithOp::Neg => self.mk_neg(arg),
                }
            }

            mir::RvalueKind::IntBinaryArith {
                op, lhs, rhs, sign, ..
            } => {
                let lhs_ll = self.emit_mir_rvalue_both(lhs)?;
                let rhs_ll = self.emit_mir_rvalue_both(rhs)?;
                let signed = sign.is_signed();
                match op {
                    mir::IntBinaryArithOp::Add => self.mk_add(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Sub => self.mk_sub(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mul if signed => self.mk_smul(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Div if signed => self.mk_sdiv(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mod if signed => self.mk_smod(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mul => self.mk_umul(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Div => self.mk_udiv(lhs_ll, rhs_ll),
                    mir::IntBinaryArithOp::Mod => self.mk_umod(lhs_ll, rhs_ll),

                    // The `x**y` operator requires special love, because there
                    // is no direct equivalent for it in LLHD.
                    mir::IntBinaryArithOp::Pow => {
                        // If the exponent is a constant, we simply unroll.
                        if rhs.is_const() {
                            let count = self.const_mir_rvalue_int(Ref(rhs))?;
                            let mut value = lhs_ll;
                            for _ in 1..count.to_usize().unwrap() {
                                value = self.mk_umul(value, lhs_ll);
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
                                let width = self.llhd_type(rhs_ll.0).len();
                                let lg2 = self.mk_const_int(width, &BigInt::from(lg2));
                                self.mk_umul(lg2, rhs_ll)
                            });
                            if let Some(rhs_ll) = rhs_ll {
                                // `1`
                                let width = self.llhd_type(lhs_ll.0).len();
                                let lhs_ll = self.mk_const_int(width, &BigInt::one());
                                // `1 << (y * log2(base))`
                                let zeros = self.emit_zero_for_type_both((
                                    self.llhd_type(lhs_ll.0),
                                    lhs_ll.1.ty(),
                                ));
                                return Ok((self.mk_shl(lhs_ll, zeros, rhs_ll), Mode::Value));
                            }
                        }

                        // Otherwise we just complain.
                        self.emit(
                            DiagBuilder2::error("`**` operator on non-constants not supported")
                                .span(mir.span),
                        );
                        return Err(());
                    }
                }
            }

            mir::RvalueKind::Concat(ref values) => {
                let mut offset = 0;
                let llty = self.emit_type_both(mir.ty)?;
                trace!(
                    "Concatenating {} values into `{}` (as {:?})",
                    values.len(),
                    mir.ty,
                    llty
                );
                let mut result = self.emit_zero_for_type_both(llty);
                for value in values.iter().rev() {
                    let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                    let llval = self.emit_mir_rvalue_both(value)?;
                    trace!(
                        " - Value has width {}, type `{}`, in LLHD `{}`",
                        width,
                        value.ty,
                        self.llhd_type(llval.0)
                    );
                    result = self.mk_ins_slice(result, llval, offset, width);
                    offset += width;
                }
                self.builder.set_name(result.0, "concat".to_string());
                result
            }

            mir::RvalueKind::Repeat(times, value) => {
                let width = value.ty.simple_bit_vector(self.cx, value.span).size;
                let value = self.emit_mir_rvalue_both(value)?;
                let llty = self.emit_type_both(mir.ty)?;
                let mut result = self.emit_zero_for_type_both(llty);
                for i in 0..times {
                    result = self.mk_ins_slice(result, value, i * width, width);
                }
                self.builder.set_name(result.0, "repeat".to_string());
                result
            }

            mir::RvalueKind::Shift {
                op,
                arith,
                value,
                amount,
            } => {
                let value = self.emit_mir_rvalue_both(value)?;
                let amount = self.emit_mir_rvalue_both(amount)?;
                let value_ty = self.builder.unit().value_type(value.0);
                let hidden = self.emit_zero_for_type_both((value_ty.clone(), value.1.ty()));
                let hidden = if arith && op == mir::ShiftOp::Right {
                    let ones = self.mk_not(hidden);
                    let sign = self.mk_ext_slice(value, value_ty.unwrap_int() - 1, 1);
                    self.mk_mux(sign, ones, hidden)
                } else {
                    hidden
                };
                match op {
                    mir::ShiftOp::Left => self.mk_shl(value, hidden, amount),
                    mir::ShiftOp::Right => self.mk_shr(value, hidden, amount),
                }
            }

            mir::RvalueKind::Ternary {
                cond,
                true_value,
                false_value,
            } => {
                let cond = self.emit_mir_rvalue_both(cond)?;
                let true_value = self.emit_mir_rvalue_both(true_value)?;
                let false_value = self.emit_mir_rvalue_both(false_value)?;
                self.mk_mux(cond, true_value, false_value)
            }

            mir::RvalueKind::Reduction { op, arg } => {
                let width = arg.ty.simple_bit_vector(self.cx, arg.span).size;
                let arg = self.emit_mir_rvalue_both(arg)?;
                let mut value = self.mk_ext_slice(arg, 0, 1);
                for i in 1..width {
                    let bit = self.mk_ext_slice(arg, i, 1);
                    value = match op {
                        mir::BinaryBitwiseOp::And => self.mk_and(value, bit),
                        mir::BinaryBitwiseOp::Or => self.mk_or(value, bit),
                        mir::BinaryBitwiseOp::Xor => self.mk_xor(value, bit),
                    };
                }
                value
            }

            mir::RvalueKind::Assignment {
                lvalue,
                rvalue,
                result,
            } => {
                self.emit_mir_blocking_assign(lvalue, rvalue)?;
                self.emit_mir_rvalue_both(result)?
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

            mir::RvalueKind::Error => return Err(()),
        };

        Ok((value, Mode::Value))
    }

    fn emit_prb_or_var(&mut self, sig: HybridValue) -> HybridValue {
        match *self.llhd_type(sig.0) {
            llhd::SignalType(_) => {
                let value = self.mk_prb(sig);
                if let Some(name) = self.builder.get_name(sig.0) {
                    self.builder.set_name(value.0, format!("{}.prb", name));
                }
                value
            }
            llhd::PointerType(_) => {
                let value = self.mk_ld(sig);
                if let Some(name) = self.builder.get_name(sig.0) {
                    self.builder.set_name(value.0, format!("{}.ld", name));
                }
                value
            }
            _ => sig,
        }
    }

    /// Emit the code for an rvalue converted to a boolean..
    fn emit_rvalue_bool_both(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<HybridValue> {
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
        self.emit_mir_rvalue_both(mir)
    }

    fn emit_rvalue_bool(&mut self, expr_id: NodeId, env: ParamEnv) -> Result<llhd::ir::Value> {
        self.emit_rvalue_bool_both(expr_id, env).map(|x| x.0)
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
    ) -> Result<(HybridValue, Mode)> {
        match mir.kind {
            mir::RvalueKind::Intf(intf) => {
                let id = AccessedNode::Intf(intf, signal);
                let sig = self
                    .shadows
                    .get(&id)
                    .cloned()
                    .unwrap_or_else(|| self.emitted_value_both(id));
                debug!(
                    "{:?} emitted value is {:?} (type {})",
                    id,
                    sig,
                    self.llhd_type(sig.0)
                );
                if mode_hint == Mode::Signal && self.llhd_type(sig.0).is_signal() {
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
        value: HybridValue,
        base: &'gcx mir::Rvalue<'gcx>,
        length: usize,
    ) -> Result<HybridValue> {
        let base = self.emit_mir_rvalue_both(base)?;
        let hidden = self.emit_zero_for_type_both((self.llhd_type(value.0), base.1.ty()));
        // TODO(fschuiki): make the above a constant of all `x`.
        let shifted = self.mk_shr(value, hidden, base);
        if ty.coalesces_to_llhd_scalar() {
            let length = std::cmp::max(1, length);
            Ok(self.mk_ext_slice(shifted, 0, length))
        } else {
            if length == 0 {
                Ok(self.mk_ext_field(shifted, 0))
            } else {
                Ok(self.mk_ext_slice(shifted, 0, length))
            }
        }
    }

    /// Emit the code for an MIR lvalue.
    fn emit_mir_lvalue(
        &mut self,
        mir: &mir::Lvalue<'gcx>,
    ) -> Result<(llhd::ir::Value, Option<llhd::ir::Value>)> {
        self.emit_mir_lvalue_both(mir)
            .map(|(x, y)| (x.0, y.map(|y| y.0)))
    }

    /// Emit the code for an MIR lvalue.
    fn emit_mir_lvalue_both(
        &mut self,
        mir: &mir::Lvalue<'gcx>,
    ) -> Result<(HybridValue, Option<HybridValue>)> {
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
    ) -> Result<(HybridValue, Option<HybridValue>)> {
        let result = self.emit_mir_lvalue_inner(mir);
        match result {
            Ok((sig, var)) => {
                let llty_exp1 = llhd::signal_ty(self.emit_type(mir.ty)?);
                let llty_exp2 = llhd::pointer_ty(self.emit_type(mir.ty)?);
                let llty_act = self.llhd_type(sig.0);
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
                    let llty_act = self.llhd_type(var.0);
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
    ) -> Result<(HybridValue, Option<HybridValue>)> {
        match mir.kind {
            // Transmutes are no-ops in code generation.
            mir::LvalueKind::Transmute(value) => self.emit_mir_lvalue_both(value),

            // Variables and ports trivially return their declaration value.
            // This is either the `var` or `sig` instruction which introduced
            // them.
            mir::LvalueKind::Var(id) | mir::LvalueKind::Port(id) => Ok((
                self.emitted_value_both(id).clone(),
                self.shadows.get(&id.into()).cloned(),
            )),

            // Interface signals require special care, because they are emitted
            // in a transposed fashion.
            mir::LvalueKind::IntfSignal(value, signal) => self.emit_lvalue_interface(value, signal),

            // Member accesses simply look up their inner lvalue and extract the
            // signal or pointer to the respective subfield.
            mir::LvalueKind::Member { value, field } => {
                let target = self.emit_mir_lvalue_both(value)?;
                let value_real = self.mk_ext_field(target.0, field);
                let value_shadow = target.1.map(|target| self.mk_ext_field(target, field));
                Ok((value_real, value_shadow))
            }

            // Index accesses shift and extract the accessed slice as a signal
            // or pointer.
            mir::LvalueKind::Index {
                value,
                base,
                length,
            } => {
                let inner = self.emit_mir_lvalue_both(value)?;
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
                bug_span!(
                    mir.span,
                    self.cx,
                    "codegen not implemented for mir lvalue {:#?}",
                    mir
                );
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
    ) -> Result<(HybridValue, Option<HybridValue>)> {
        match mir.kind {
            mir::LvalueKind::Intf(intf) => {
                let id = AccessedNode::Intf(intf, signal);
                Ok((
                    self.emitted_value_both(id).clone(),
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
        value: (HybridValue, Option<HybridValue>),
        base: &'gcx mir::Rvalue<'gcx>,
        length: usize,
    ) -> Result<(HybridValue, Option<HybridValue>)> {
        let (target_real, target_shadow) = value;
        let base = self.emit_mir_rvalue_both(base)?;
        let shifted_real = {
            let hidden =
                self.emit_zero_for_type_both((self.llhd_type(target_real.0), target_real.1.ty()));
            self.mk_shr(target_real, hidden, base)
        };
        let shifted_shadow = target_shadow.map(|target| {
            let hidden = self.emit_zero_for_type_both((self.llhd_type(target.0), target.1.ty()));
            self.mk_shr(target, hidden, base)
        });
        if ty.coalesces_to_llhd_scalar() {
            let length = std::cmp::max(1, length);
            Ok((
                self.mk_ext_slice(shifted_real, 0, length),
                shifted_shadow.map(|s| self.mk_ext_slice(s, 0, length)),
            ))
        } else {
            if length == 0 {
                Ok((
                    self.mk_ext_field(shifted_real, 0),
                    shifted_shadow.map(|s| self.mk_ext_field(s, 0)),
                ))
            } else {
                Ok((
                    self.mk_ext_slice(shifted_real, 0, length),
                    shifted_shadow.map(|s| self.mk_ext_slice(s, 0, length)),
                ))
            }
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
    fn emit_stmt_regular(&mut self, stmt_id: NodeId, hir: &hir::Stmt, env: ParamEnv) -> Result<()> {
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
                // Map the assignment to an MIR node.
                let assign_mir =
                    self.mir_assignment_from_procedural(stmt_id, lhs, rhs, env, hir.span, kind);
                debug!("Procedural assignment: {:#?}", assign_mir);

                // Simplify the assignment to eliminate concatenations on the
                // left-hand side.
                let simplified = self.mir_simplify_assignment(Ref(assign_mir));
                debug!("Simplified to: {:#?}", simplified);

                // Check for sanity.
                for &assign in &simplified {
                    assert_type!(assign.rhs.ty, assign.lhs.ty, assign.rhs.span, self.cx);
                    if assign.is_error() {
                        return Err(());
                    }
                }

                // Emit the appropriate assignments based on the assignment
                // kind.
                match kind {
                    hir::AssignKind::Block(_) => {
                        for &assign in &simplified {
                            let lhs_lv = self.emit_mir_lvalue(assign.lhs)?;
                            let rhs_rv = self.emit_mir_rvalue(assign.rhs)?;
                            self.emit_blocking_assign_llhd(lhs_lv, rhs_rv)?;
                        }
                    }
                    hir::AssignKind::Nonblock => {
                        let delay = llhd::value::TimeValue::new(num::zero(), 1, 0);
                        let delay_const = self.builder.ins().const_time(delay);
                        for &assign in &simplified {
                            let lhs_lv = self.emit_mir_lvalue(assign.lhs)?;
                            let rhs_rv = self.emit_mir_rvalue(assign.rhs)?;
                            self.builder.ins().drv(lhs_lv.0, rhs_rv, delay_const);
                        }
                    }
                    hir::AssignKind::NonblockDelay(delay) => {
                        let delay = self.emit_rvalue(delay, env)?;
                        for &assign in &simplified {
                            let lhs_lv = self.emit_mir_lvalue(assign.lhs)?;
                            let rhs_rv = self.emit_mir_rvalue(assign.rhs)?;
                            self.builder.ins().drv(lhs_lv.0, rhs_rv, delay);
                        }
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
                self.emit_rvalue_both(expr_id, env)?;
            }
            hir::StmtKind::If {
                cond,
                main_stmt,
                else_stmt,
            } => {
                let main_blk = self.mk_block(Some("if_true"));
                let else_blk = self.mk_block(Some("if_false"));
                let cond = self.emit_rvalue_bool_both(cond, env)?;
                self.mk_cond_br(cond, main_blk, else_blk);
                let final_blk = self.mk_block(Some("if_exit"));
                self.append_to(main_blk);
                self.emit_stmt(main_stmt, env)?;
                self.mk_br(final_blk);
                self.append_to(else_blk);
                if let Some(else_stmt) = else_stmt {
                    self.emit_stmt(else_stmt, env)?;
                };
                self.mk_br(final_blk);
                self.append_to(final_blk);
            }
            hir::StmtKind::Loop { kind, body } => {
                let body_blk = self.mk_block(Some("loop_body"));
                let exit_blk = self.mk_block(Some("loop_exit"));

                // Emit the loop initialization.
                let repeat_var = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(count) => {
                        let ty = self.type_of(count, env)?;
                        let count = self.emit_rvalue_both(count, env)?;
                        let var = self.mk_var(count);
                        self.builder.set_name(var.0, "loop_count".to_string());
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
                self.mk_br(body_blk);
                self.append_to(body_blk);
                let enter_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let lty = self.emit_type_both(ty)?;
                        let value = self.mk_ld(repeat_var);
                        let zero = self.emit_zero_for_type_both(lty);
                        Some(self.mk_cmp(CmpPred::Neq, value, zero))
                    }
                    hir::LoopKind::While(cond) => Some(self.emit_rvalue_bool_both(cond, env)?),
                    hir::LoopKind::Do(_) => None,
                    hir::LoopKind::For(_, cond, _) => Some(self.emit_rvalue_bool_both(cond, env)?),
                };
                if let Some(enter_cond) = enter_cond {
                    let entry_blk = self.mk_block(Some("loop_continue"));
                    self.mk_cond_br(enter_cond, entry_blk, exit_blk);
                    self.append_to(entry_blk);
                }

                // Emit the loop body.
                self.emit_stmt(body, env)?;

                // Emit the epilogue.
                let continue_cond = match kind {
                    hir::LoopKind::Forever => None,
                    hir::LoopKind::Repeat(_) => {
                        let (repeat_var, ty) = repeat_var.clone().unwrap();
                        let value = self.mk_ld(repeat_var);
                        let one = self.mk_const_int(ty.get_bit_size().unwrap(), &BigInt::one());
                        let value = self.mk_sub(value, one);
                        self.mk_st(repeat_var, value);
                        None
                    }
                    hir::LoopKind::While(_) => None,
                    hir::LoopKind::Do(cond) => Some(self.emit_rvalue_bool_both(cond, env)?),
                    hir::LoopKind::For(_, _, step) => {
                        self.emit_rvalue_both(step, env)?;
                        None
                    }
                };
                match continue_cond {
                    Some(cond) => self.mk_cond_br(cond, body_blk, exit_blk),
                    None => self.mk_br(body_blk),
                };
                self.append_to(exit_blk);
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
        let ty = self.emit_type_both(ty)?;
        let init = match hir.init {
            Some(expr) => self.emit_rvalue_both(expr, env)?,
            None => self.emit_zero_for_type_both(ty),
        };
        let value = self.mk_var(init);
        self.builder.set_name(value.0, hir.name.value.to_string());
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
        for (id, shadow) in self.shadows.clone() {
            let value = self.values[&id.into()];
            let value = self.mk_prb(value);
            self.mk_st(shadow, value);
        }
    }

    /// Emit the code for a variable or net declaration.
    fn emit_varnet_decl(
        &mut self,
        decl_id: NodeId,
        ty: &'gcx UnpackedType<'gcx>,
        env: ParamEnv,
        default: Option<NodeId>,
    ) -> Result<HybridValue> {
        // Check if this is a variable or a net declaration.
        let (is_var, name) = match self.hir_of(decl_id)? {
            HirNode::VarDecl(x) => (x.kind.is_var(), x.name.value.as_str()),
            HirNode::IntPort(x) => (x.kind.is_var(), x.name.value.as_str()),
            x => unreachable!("emit_varnet_decl on HIR {:?}", x),
        };

        // Differentiate between variable and net declarations, which have
        // slightly different semantics regarding their initial value.
        if is_var {
            // For variables we require that the initial value is a
            // constant.
            let init = self.emit_const_both(
                match default {
                    Some(expr) => self.constant_value_of(expr, env),
                    None => self.type_default_value(ty),
                },
                env,
                self.span(default.unwrap_or(decl_id)),
            )?;
            Ok((
                self.builder.ins().sig(init.0),
                circt::llhd::SignalOp::new(self.mlir_builder, &name, init.1).into(),
            ))
        } else {
            // For nets we simply emit the initial value as a signal, then
            // short-circuit it with the net declaration.
            let zero =
                self.emit_const_both(self.type_default_value(ty), env, self.span(decl_id))?;
            let net = (
                self.builder.ins().sig(zero.0),
                circt::llhd::SignalOp::new(self.mlir_builder, &name, zero.1).into(),
            );
            if let Some(default) = default {
                let init = self.emit_rvalue_mode(default, env, Mode::Signal)?;
                self.builder.ins().con(net.0, init.0);
                circt::llhd::ConnectOp::new(self.mlir_builder, net.1, init.1);
            }
            Ok(net)
        }
    }

    fn mk_block(&mut self, name: Option<&str>) -> HybridBlock {
        let bb = self.builder.block();
        if let Some(name) = name {
            self.builder.set_block_name(bb, name.into());
        }
        (bb, self.mlir_builder.add_block())
    }

    fn mk_br(&mut self, target: HybridBlock) {
        self.builder.ins().br(target.0);
        circt::std::BranchOp::new(self.mlir_builder, target.1);
    }

    fn mk_cond_br(&mut self, cond: HybridValue, true_block: HybridBlock, false_block: HybridBlock) {
        self.builder
            .ins()
            .br_cond(cond.0, false_block.0, true_block.0);
        circt::std::CondBranchOp::new(self.mlir_builder, cond.1, true_block.1, false_block.1);
    }

    fn append_to(&mut self, block: HybridBlock) {
        self.builder.append_to(block.0);
        self.mlir_builder.set_insertion_point_to_end(block.1);
    }

    fn mk_ext_slice(&mut self, arg: HybridValue, offset: usize, length: usize) -> HybridValue {
        (
            self.builder.ins().ext_slice(arg.0, offset, length),
            if mlir::is_integer_type(arg.1.ty()) {
                circt::comb::ExtractOp::with_sizes(self.mlir_builder, arg.1, offset, length).into()
            } else {
                if let Some(ty) = circt::llhd::get_signal_type_element(arg.1.ty()) {
                    if mlir::is_integer_type(ty) {
                        circt::llhd::SigExtractOp::with_const_offset(
                            self.mlir_builder,
                            arg.1,
                            offset,
                            length,
                        )
                        .into()
                    } else {
                        circt::llhd::SigArraySliceOp::with_const_offset(
                            self.mlir_builder,
                            arg.1,
                            offset,
                            length,
                        )
                        .into()
                    }
                } else if let Some(ty) = circt::llhd::get_pointer_type_element(arg.1.ty()) {
                    if mlir::is_integer_type(ty) {
                        circt::llhd::PtrExtractOp::with_const_offset(
                            self.mlir_builder,
                            arg.1,
                            offset,
                            length,
                        )
                        .into()
                    } else {
                        circt::llhd::PtrArraySliceOp::with_const_offset(
                            self.mlir_builder,
                            arg.1,
                            offset,
                            length,
                        )
                        .into()
                    }
                } else {
                    circt::hw::ArraySliceOp::with_const_offset(
                        self.mlir_builder,
                        arg.1,
                        offset,
                        length,
                    )
                    .into()
                }
            },
        )
    }

    fn mk_ins_slice_mlir(
        &mut self,
        into: mlir::Value,
        value: mlir::Value,
        offset: usize,
        length: usize,
    ) -> mlir::Value {
        let is_int = mlir::is_integer_type(into.ty());
        let len = match is_int {
            true => mlir::integer_type_width(into.ty()),
            false => circt::hw::array_type_size(into.ty()),
        };
        let mut concats = vec![];
        if offset > 0 {
            let ext = match is_int {
                true => {
                    circt::comb::ExtractOp::with_sizes(self.mlir_builder, into, 0, offset).into()
                }
                false => {
                    circt::hw::ArraySliceOp::with_const_offset(self.mlir_builder, into, 0, offset)
                        .into()
                }
            };
            concats.push(ext);
        }
        concats.push(value);
        if offset + length < len {
            let rest = len - offset - length;
            let ext = match is_int {
                true => circt::comb::ExtractOp::with_sizes(
                    self.mlir_builder,
                    into,
                    offset + length,
                    rest,
                )
                .into(),
                false => circt::hw::ArraySliceOp::with_const_offset(
                    self.mlir_builder,
                    into,
                    offset + length,
                    rest,
                )
                .into(),
            };
            concats.push(ext);
        }
        match is_int {
            true => circt::comb::ConcatOp::new(self.mlir_builder, concats).into(),
            false => circt::hw::ArrayConcatOp::new(self.mlir_builder, concats).into(),
        }
    }

    fn mk_ins_slice(
        &mut self,
        into: HybridValue,
        value: HybridValue,
        offset: usize,
        length: usize,
    ) -> HybridValue {
        (
            self.builder
                .ins()
                .ins_slice(into.0, value.0, offset, length),
            self.mk_ins_slice_mlir(into.1, value.1, offset, length),
        )
    }

    fn mk_ext_field(&mut self, arg: HybridValue, offset: usize) -> HybridValue {
        let mlir = if circt::hw::is_array_type(arg.1.ty()) {
            circt::hw::ArrayGetOp::with_const_offset(self.mlir_builder, arg.1, offset).into()
        } else if circt::hw::is_struct_type(arg.1.ty()) {
            circt::hw::StructExtractOp::new(self.mlir_builder, arg.1, offset).into()
        } else if let Some(ty) = circt::llhd::get_signal_type_element(arg.1.ty()) {
            if circt::hw::is_array_type(ty) {
                circt::llhd::SigArrayGetOp::with_const_offset(self.mlir_builder, arg.1, offset)
                    .into()
            } else if circt::hw::is_struct_type(ty) {
                circt::llhd::SigStructExtractOp::new(self.mlir_builder, arg.1, offset).into()
            } else {
                panic!("unsupported type {}", ty);
            }
        } else if let Some(ty) = circt::llhd::get_pointer_type_element(arg.1.ty()) {
            if circt::hw::is_array_type(ty) {
                circt::llhd::PtrArrayGetOp::with_const_offset(self.mlir_builder, arg.1, offset)
                    .into()
            } else if circt::hw::is_struct_type(ty) {
                circt::llhd::PtrStructExtractOp::new(self.mlir_builder, arg.1, offset).into()
            } else {
                panic!("unsupported type {}", ty);
            }
        } else {
            panic!("unsupported type {}", arg.1.ty());
        };
        (self.builder.ins().ext_field(arg.0, offset), mlir)
    }

    #[allow(dead_code)]
    fn mk_ins_field(
        &mut self,
        into: HybridValue,
        value: HybridValue,
        offset: usize,
    ) -> HybridValue {
        let mlir = if circt::hw::is_struct_type(into.1.ty()) {
            circt::hw::StructInjectOp::new(self.mlir_builder, into.1, value.1, offset).into()
        } else {
            let value = circt::hw::ArrayCreateOp::new(
                self.mlir_builder,
                circt::hw::get_array_type(value.1.ty(), 1),
                vec![value.1],
            )
            .into();
            self.mk_ins_slice_mlir(into.1, value, offset, 1)
        };
        (self.builder.ins().ins_field(into.0, value.0, offset), mlir)
    }

    fn mk_not(&mut self, arg: HybridValue) -> HybridValue {
        (self.builder.ins().not(arg.0), {
            let ones = circt::hw::ConstantOp::new(
                self.mlir_builder,
                mlir::integer_type_width(arg.1.ty()),
                &(-1).into(),
            )
            .into();
            circt::comb::XorOp::new(self.mlir_builder, ones, arg.1).into()
        })
    }

    fn mk_neg(&mut self, arg: HybridValue) -> HybridValue {
        (self.builder.ins().neg(arg.0), {
            let zero = self.emit_zero_for_type_mlir(arg.1.ty());
            circt::comb::SubOp::new(self.mlir_builder, zero, arg.1).into()
        })
    }

    fn mk_and(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().and(lhs.0, rhs.0),
            circt::comb::AndOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_or(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().or(lhs.0, rhs.0),
            circt::comb::OrOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_xor(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().xor(lhs.0, rhs.0),
            circt::comb::XorOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_mux(
        &mut self,
        cond: HybridValue,
        true_value: HybridValue,
        false_value: HybridValue,
    ) -> HybridValue {
        let array = self.builder.ins().array(vec![false_value.0, true_value.0]);
        (
            self.builder.ins().mux(array, cond.0),
            circt::comb::MuxOp::new(self.mlir_builder, cond.1, true_value.1, false_value.1).into(),
        )
    }

    fn mk_shl(
        &mut self,
        value: HybridValue,
        hidden: HybridValue,
        amount: HybridValue,
    ) -> HybridValue {
        (
            self.builder.ins().shl(value.0, hidden.0, amount.0),
            circt::llhd::ShlOp::new(self.mlir_builder, value.1, hidden.1, amount.1).into(),
        )
    }

    fn mk_shr(
        &mut self,
        value: HybridValue,
        hidden: HybridValue,
        amount: HybridValue,
    ) -> HybridValue {
        (
            self.builder.ins().shr(value.0, hidden.0, amount.0),
            circt::llhd::ShrOp::new(self.mlir_builder, value.1, hidden.1, amount.1).into(),
        )
    }

    fn mk_add(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().add(lhs.0, rhs.0),
            circt::comb::AddOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_sub(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().sub(lhs.0, rhs.0),
            circt::comb::SubOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_smul(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().smul(lhs.0, rhs.0),
            circt::comb::MulOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_umul(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().umul(lhs.0, rhs.0),
            circt::comb::MulOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_sdiv(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().sdiv(lhs.0, rhs.0),
            circt::comb::DivSOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_udiv(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().udiv(lhs.0, rhs.0),
            circt::comb::DivUOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_smod(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().smod(lhs.0, rhs.0),
            circt::comb::ModSOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_umod(&mut self, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        (
            self.builder.ins().umod(lhs.0, rhs.0),
            circt::comb::ModUOp::new(self.mlir_builder, lhs.1, rhs.1).into(),
        )
    }

    fn mk_const_int(&mut self, width: usize, value: &BigInt) -> HybridValue {
        (
            self.builder.ins().const_int((width, value.clone())),
            circt::hw::ConstantOp::new(self.mlir_builder, width, value).into(),
        )
    }

    fn mk_cmp(&mut self, pred: CmpPred, lhs: HybridValue, rhs: HybridValue) -> HybridValue {
        let mut ins = self.builder.ins();
        let old = match pred {
            CmpPred::Eq => ins.eq(lhs.0, rhs.0),
            CmpPred::Neq => ins.neq(lhs.0, rhs.0),
            CmpPred::Slt => ins.slt(lhs.0, rhs.0),
            CmpPred::Sle => ins.sle(lhs.0, rhs.0),
            CmpPred::Sgt => ins.sgt(lhs.0, rhs.0),
            CmpPred::Sge => ins.sge(lhs.0, rhs.0),
            CmpPred::Ult => ins.ult(lhs.0, rhs.0),
            CmpPred::Ule => ins.ule(lhs.0, rhs.0),
            CmpPred::Ugt => ins.ugt(lhs.0, rhs.0),
            CmpPred::Uge => ins.uge(lhs.0, rhs.0),
        };
        (
            old,
            circt::comb::ICmpOp::new(self.mlir_builder, pred, lhs.1, rhs.1).into(),
        )
    }

    fn mk_array(&mut self, ty: HybridType, elements: &[HybridValue]) -> HybridValue {
        (
            self.builder
                .ins()
                .array(elements.iter().map(|v| v.0.clone()).collect()),
            circt::hw::ArrayCreateOp::new(self.mlir_builder, ty.1, elements.iter().map(|v| v.1))
                .into(),
        )
    }

    fn mk_struct(&mut self, ty: HybridType, elements: &[HybridValue]) -> HybridValue {
        (
            self.builder
                .ins()
                .strukt(elements.iter().map(|v| v.0.clone()).collect()),
            circt::hw::StructCreateOp::new(self.mlir_builder, ty.1, elements.iter().map(|v| v.1))
                .into(),
        )
    }

    fn mk_prb(&mut self, value: HybridValue) -> HybridValue {
        (
            self.builder.ins().prb(value.0),
            circt::llhd::ProbeOp::new(self.mlir_builder, value.1).into(),
        )
    }

    fn mk_drv(&mut self, lhs: HybridValue, rhs: HybridValue, delay: HybridValue) {
        (
            self.builder.ins().drv(lhs.0, rhs.0, delay.0),
            circt::llhd::DriveOp::new(self.mlir_builder, lhs.1, rhs.1, delay.1),
        );
    }

    fn mk_var(&mut self, init: HybridValue) -> HybridValue {
        (
            self.builder.ins().var(init.0),
            circt::llhd::VariableOp::new(self.mlir_builder, init.1).into(),
        )
    }

    fn mk_ld(&mut self, var: HybridValue) -> HybridValue {
        (
            self.builder.ins().ld(var.0),
            circt::llhd::LoadOp::new(self.mlir_builder, var.1).into(),
        )
    }

    fn mk_st(&mut self, var: HybridValue, value: HybridValue) {
        (
            self.builder.ins().st(var.0, value.0),
            circt::llhd::StoreOp::new(self.mlir_builder, var.1, value.1),
        );
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
    /// The emitted MLIR symbol name.
    mlir_symbol: String,
    /// The module's ports.
    ports: ModuleIntf<'a>,
}

/// Result of emitting a procedure.
pub struct EmittedProcedure {
    /// The emitted LLHD unit.
    unit: llhd::ir::UnitId,
    /// The emitted MLIR symbol name.
    mlir_symbol: String,
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
    /// The lowered MLIR type.
    pub mty: mlir::Type,
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

/// Convert a `Span` to a corresponding MLIR location.
fn span_to_loc(cx: mlir::Context, span: Span) -> mlir::Location {
    let l = span.begin();
    mlir::Location::file_line_col(cx, &l.source.get_path(), l.human_line(), l.human_column())
}

/// Make a type a signal type.
///
/// This is a convenience function that process old LLHD types and the newer
/// MLIR types in parallel.
fn signal_ty(ty: HybridType) -> HybridType {
    (llhd::signal_ty(ty.0), circt::llhd::get_signal_type(ty.1))
}

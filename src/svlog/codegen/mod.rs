// Copyright (c) 2016-2019 Fabian Schuiki

//! This module implements LLHD code generation.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{Type, TypeKind},
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
    module_defs: HashMap<NodeId, Result<llhd::value::EntityRef>>,
    module_types: HashMap<NodeId, llhd::Type>,
    interned_types: HashMap<Type<'gcx>, Result<llhd::Type>>,
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
        if let Some(x) = self.tables.module_defs.get(&id) {
            return x.clone();
        }
        let hir = match self.hir_of(id)? {
            HirNode::Module(m) => m,
            _ => panic!("expected {:?} to be a module", id),
        };

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
            let ty = self.type_of(port_id)?;
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

        // Create entity.
        let mut ent = llhd::Entity::new(
            hir.name.value.into(),
            llhd::entity_ty(input_tys, output_tys),
        );

        // Assign proper port names and collect ports into a lookup table.
        let mut port_map = HashMap::new();
        for (index, port_id) in inputs.into_iter().enumerate() {
            ent.inputs_mut()[index].set_name(port_id_to_name[&port_id].value);
            port_map.insert(port_id, ent.input(index));
        }
        for (index, port_id) in outputs.into_iter().enumerate() {
            ent.outputs_mut()[index].set_name(port_id_to_name[&port_id].value);
            port_map.insert(port_id, ent.output(index));
        }

        let result = Ok(self.into.add_entity(ent));
        self.tables.module_defs.insert(id, result.clone());
        result
    }

    /// Map a type to an LLHD type.
    fn emit_type(&mut self, ty: Type<'gcx>) -> Result<llhd::Type> {
        if let Some(x) = self.tables.interned_types.get(ty) {
            x.clone()
        } else {
            let x = self.emit_type_uninterned(ty);
            self.tables.interned_types.insert(ty, x.clone());
            x
        }
    }

    fn emit_type_uninterned(&self, ty: Type<'gcx>) -> Result<llhd::Type> {
        Ok(match *ty {
            TypeKind::Void => llhd::void_ty(),
            TypeKind::Bit => llhd::int_ty(1),
            _ => unimplemented!(),
        })
    }
}

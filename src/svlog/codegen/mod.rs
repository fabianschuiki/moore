// Copyright (c) 2016-2019 Fabian Schuiki

//! This module implements LLHD code generation.

use crate::crate_prelude::*;
use crate::hir::HirNode;
use crate::ty::TypeKind;
use std::collections::HashMap;

pub(crate) fn generate_code<'gcx>(cx: Context<'gcx>, node_id: NodeId) -> Result<llhd::Module> {
    debug!("generate_code({})", node_id);

    let hir = cx.hir_of(node_id)?;

    let mut module = llhd::Module::new();
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Module(m) => {
            codegen_module(cx, m, &mut module)?;
        }
        _ => {
            cx.emit(
                DiagBuilder2::bug(format!(
                    "code generation for {} not implemented",
                    hir.desc_full()
                ))
                .span(hir.human_span()),
            );
            return Err(());
        }
    }
    Ok(module)
}

fn codegen_module<'gcx>(
    cx: Context<'gcx>,
    hir: &hir::Module,
    into: &mut llhd::Module,
) -> Result<llhd::ValueRef> {
    // Determine entity type and port names.
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    let mut input_tys = Vec::new();
    let mut output_tys = Vec::new();
    let mut port_id_to_name = HashMap::new();
    for &port_id in hir.ports {
        let port = match cx.hir_of(port_id)? {
            HirNode::Port(p) => p,
            _ => unreachable!(),
        };
        let ty = cx.type_of(port_id)?;
        debug!(
            "port {}.{} has type {:?}",
            hir.name.value, port.name.value, ty
        );
        let ty = codegen_type(cx, ty)?; // TODO: pick actual type
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

    Ok(into.add_entity(ent).into())
}

fn codegen_type<'gcx>(cx: Context<'gcx>, ty: Type<'gcx>) -> Result<llhd::Type> {
    Ok(match *ty {
        TypeKind::Void => llhd::void_ty(),
        TypeKind::Bit => llhd::int_ty(1),
        _ => unimplemented!(),
    })
}

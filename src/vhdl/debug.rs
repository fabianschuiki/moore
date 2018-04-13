// Copyright (c) 2018 Fabian Schuiki

#![allow(unused_variables)]

use common::errors::DiagBuilder2;

use syntax::ast;
use hir;
use hir::{FromAst, Node};

pub fn emit_pkgs(nodes: Vec<&ast::DesignUnit>) {
    // Filter out all the package declarations.
    let pkgs = nodes.into_iter().filter_map(|node| match node.data {
        ast::DesignUnitData::PkgDecl(ref d) => {
            debugln!("found VHDL package `{}`", d.name.value);
            Some(d)
        }
        _ => None,
    });

    // Allocate slots for each package.
    let arenas = hir::Arenas2::new();
    let ctx = hir::Context::new(&arenas);
    let scope = &hir::DummyScope;
    let slots: Vec<_> = pkgs.map(|pkg| hir::Package2::alloc_slot(scope, pkg, ctx).unwrap())
        .collect();
    debugln!("slots created");
    for s in &slots {
        eprintln!("{}", DiagBuilder2::note("package available").span(s.span()));
        let pkg = s.poll().unwrap();
        for d in pkg.decls() {
            eprintln!("{}", DiagBuilder2::note("declaration available").span(d.span()));
        }
    }
}

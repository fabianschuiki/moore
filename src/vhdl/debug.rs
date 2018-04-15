// Copyright (c) 2018 Fabian Schuiki

#![allow(unused_imports)]
#![allow(unused_variables)]

use common::Session;
use common::errors::DiagBuilder2;
use common::source::Spanned;
use common::name::Name;

use syntax::ast;
use hir::{self, Decl2, FromAst, Node};
use hir::visit::Visitor;
use scope2::ScopeData;
use arenas::Alloc;

pub fn emit_pkgs(sess: &Session, nodes: Vec<&ast::DesignUnit>) {
    // Filter out all the package declarations.
    let pkgs = nodes.into_iter().filter_map(|node| match node.data {
        ast::DesignUnitData::PkgDecl(ref d) => Some(d),
        _ => None,
    });

    // Allocate slots for each package.
    let arenas = hir::Arenas2::new();
    let scope = arenas.alloc(ScopeData::root());
    let ctx = hir::Context {
        sess: sess,
        arenas: &arenas,
        scope: scope,
    };
    let slots: Vec<_> = pkgs.map(|pkg| hir::Package2::alloc_slot(pkg, ctx).unwrap())
        .collect();
    // for s in &slots {
    //     let pkg = s.poll().unwrap();
    //     // eprintln!("{}", DiagBuilder2::note(format!("package {} available", pkg.name().value)).span(pkg.span()));
    //     for d in pkg.decls() {
    //         let decl = d.poll().unwrap();
    //         // eprintln!(
    //         //     "{}",
    //         //     DiagBuilder2::note(format!("declaration {} available", decl.name().value)).span(decl.span())
    //         // );
    //     }
    // }

    // Force name resolution and HIR creation.
    debugln!("forcing HIR creation");
    let mut v = IdentityVisitor;
    for s in &slots {
        s.poll().unwrap().accept(&mut v);
    }

    // Visit the packages.
    debugln!("names:");
    let mut v = NameVisitor;
    for s in &slots {
        s.poll().unwrap().accept(&mut v);
    }

    // Resolve a name in the scope.
}

struct IdentityVisitor;

impl<'t> Visitor<'t> for IdentityVisitor {
    fn as_visitor(&mut self) -> &mut Visitor<'t> {
        self
    }
}

struct NameVisitor;

impl<'t> Visitor<'t> for NameVisitor {
    fn visit_name(&mut self, name: Spanned<Name>) {
        debugln!("- {}", name.value);
    }

    fn as_visitor(&mut self) -> &mut Visitor<'t> {
        self as _
    }
}

// Copyright (c) 2018 Fabian Schuiki

#![allow(unused_imports)]
#![allow(unused_variables)]

use common::Session;
use common::errors::DiagBuilder2;
use common::source::Spanned;
use common::name::{get_name_table, Name};

use syntax::ast;
use hir::{self, Decl2, FromAst, LatentNode, Library, Node};
use hir::visit::Visitor;
use scope2::ScopeData;
use arenas::Alloc;

pub fn emit_pkgs(sess: &Session, nodes: Vec<&ast::DesignUnit>) {
    let arenas = hir::Arenas2::new();
    let scope = arenas.alloc(ScopeData::root());
    let ctx = hir::AllocContext {
        sess: sess,
        arenas: &arenas,
        scope: scope,
    };

    // Allocate the library.
    let name = get_name_table().intern("magic", true);
    let lib = Library::new(name, &nodes, ctx).unwrap();
    if sess.failed() {
        return;
    }

    // Filter out all the package declarations.
    // let pkgs = nodes.into_iter().filter_map(|node| match node.data {
    //     ast::DesignUnitData::PkgDecl(ref d) => Some(d),
    //     _ => None,
    // });

    // Allocate slots for each package.
    // let slots: Vec<_> = pkgs.map(|pkg| {
    //     hir::Package2::alloc_slot(pkg, ctx).unwrap() as &LatentNode<Node>
    // }).collect();
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
    lib.accept(&mut v);
    // for s in &slots {
    //     s.accept(&mut v);
    // }

    // Visit the names.
    debugln!("names:");
    let mut v = NameVisitor;
    lib.accept(&mut v);
    // for s in &slots {
    //     s.accept(&mut v);
    // }

    // Collect references to all packages.
    let mut v = PackageGatherer(Vec::new());
    lib.accept(&mut v);
    // for s in &slots {
    //     s.accept(&mut v);
    // }
    debugln!("gathered packages:");
    for pkg in v.0 {
        debugln!("- {}", pkg.name().value);
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
    fn as_visitor(&mut self) -> &mut Visitor<'t> {
        self
    }

    fn visit_name(&mut self, name: Spanned<Name>) {
        debugln!("- {}", name.value);
    }
}

struct PackageGatherer<'t>(Vec<&'t hir::Package2<'t>>);

impl<'t> Visitor<'t> for PackageGatherer<'t> {
    fn as_visitor(&mut self) -> &mut Visitor<'t> {
        self
    }

    fn visit_pkg(&mut self, pkg: &'t hir::Package2<'t>) {
        self.0.push(pkg);
        pkg.walk(self);
    }
}

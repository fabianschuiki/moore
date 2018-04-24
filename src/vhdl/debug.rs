// Copyright (c) 2018 Fabian Schuiki

#![allow(unused_imports)]
#![allow(unused_variables)]

use common::{Session, SessionContext, Verbosity};
use common::errors::DiagBuilder2;
use common::source::Spanned;
use common::errors::*;
use common::name::{get_name_table, Name};

use syntax::ast;
use hir::{self, Decl2, FromAst, LatentNode, Library, Node};
use hir::visit::Visitor;
use scope2::ScopeData;
use arenas::{Alloc, AllocOwned};
use ty2;
use konst2::{self, Const2, OwnedConst};

pub fn emit_pkgs(sess: &Session, nodes: Vec<&ast::DesignUnit>) {
    let (arenas, type_arena, const_arena) = (
        hir::Arenas2::new(),
        ty2::TypeArena::new(),
        konst2::ConstArena::new(),
    );
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

    // Force name resolution and HIR creation.
    debugln!("forcing HIR creation");
    lib.accept(&mut IdentityVisitor);

    // Visit the type declarations.
    debugln!("listing type declarations");
    let mut v = TypeVisitor {
        sess: sess,
        type_arena: &type_arena,
        const_arena: &const_arena,
    };
    lib.accept(&mut v);

    // // Visit the names.
    // debugln!("names:");
    // let mut v = NameVisitor;
    // lib.accept(&mut v);

    // // Collect references to all packages.
    // let mut v = PackageGatherer(Vec::new());
    // lib.accept(&mut v);
    // debugln!("gathered packages:");
    // for pkg in v.0 {
    //     debugln!("- {}", pkg.name().value);
    // }
}

struct IdentityVisitor;

impl<'t> Visitor<'t> for IdentityVisitor {
    fn as_visitor(&mut self) -> &mut Visitor<'t> {
        self
    }
}

// struct NameVisitor;

// impl<'t> Visitor<'t> for NameVisitor {
//     fn as_visitor(&mut self) -> &mut Visitor<'t> {
//         self
//     }

//     fn visit_name(&mut self, name: Spanned<Name>) {
//         debugln!("- {}", name.value);
//     }
// }

// struct PackageGatherer<'t>(Vec<&'t hir::Package2<'t>>);

// impl<'t> Visitor<'t> for PackageGatherer<'t> {
//     fn as_visitor(&mut self) -> &mut Visitor<'t> {
//         self
//     }

//     fn visit_pkg(&mut self, pkg: &'t hir::Package2<'t>) {
//         self.0.push(pkg);
//         pkg.walk(self);
//     }
// }

#[derive(Copy, Clone)]
struct TypeVisitor<'t> {
    sess: &'t Session,
    type_arena: &'t ty2::TypeArena<'t>,
    const_arena: &'t konst2::ConstArena<'t>,
}

impl<'a, 't: 'a> SessionContext for &'a TypeVisitor<'t> {
    fn has_verbosity(&self, verb: Verbosity) -> bool {
        self.sess.has_verbosity(verb)
    }
}

impl<'a, 't: 'a> DiagEmitter for &'a TypeVisitor<'t> {
    fn emit(&self, diag: DiagBuilder2) {
        self.sess.emit(diag);
    }
}

impl<'b, 'a, 't: 'a, T: 't> Alloc<'b, 't, T> for &'a TypeVisitor<'t>
where
    ty2::TypeArena<'t>: Alloc<'t, 't, T>,
{
    fn alloc(&'b self, value: T) -> &'t mut T {
        self.type_arena.alloc(value)
    }
}

impl<'b, 'a, 't: 'a> Alloc<'b, 't, konst2::IntegerConst<'t>> for &'a TypeVisitor<'t> {
    fn alloc(&'b self, value: konst2::IntegerConst<'t>) -> &'t mut konst2::IntegerConst<'t> {
        self.const_arena.alloc(value)
    }
}

impl<'a, 'b, 't: 'a> AllocOwned<'b, 't, konst2::Const2<'t>> for &'a TypeVisitor<'t> {
    fn alloc_owned(&'b self, value: OwnedConst<'t>) -> &'t mut Const2<'t> {
        self.const_arena.alloc_owned(value)
    }
}

impl<'t> Visitor<'t> for TypeVisitor<'t> {
    fn as_visitor(&mut self) -> &mut Visitor<'t> {
        self
    }

    fn visit_type_decl(&mut self, decl: &'t hir::TypeDecl2<'t>) {
        if let Ok(t) = decl.declared_type(self as &_) {
            debugln!("type {} = {}", decl.name(), t);
        }
        decl.walk(self);
    }
}

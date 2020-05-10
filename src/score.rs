// Copyright (c) 2016-2020 Fabian Schuiki
#![allow(dead_code)]

//! This module implements the scoreboard. The scoreboard is where the compiler
//! keeps track of intermediate results and processed artifacts, and where
//! additional compilation steps are initiated. This enables on-demand
//! compilation.

use crate::common::errors::*;
use crate::common::name::Name;
use crate::common::score::{GenericContext, NodeMaker, NodeRef, Result};
use crate::common::source::Spanned;
use crate::common::NodeId;
use crate::common::Session;
use crate::svlog::{self, ast as svlog_ast, BaseContext};
use crate::vhdl;
use crate::vhdl::syntax::ast as vhdl_ast;
use std;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use typed_arena::Arena;

/// The global context which holds information about the used scoreboards. All
/// useful operations are defined on this context rather than on the scoreboard
/// directly, to decouple processing and ownership.
pub struct ScoreContext<'lazy, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb> {
    /// The compiler session which carries the options and is used to emit
    /// diagnostics.
    pub sess: &'lazy Session,
    /// The global scoreboard.
    pub sb: &'sb ScoreBoard<'ast, 'ctx>,
    /// The VHDL scoreboard.
    pub vhdl: &'sb vhdl::score::ScoreBoard<'ast, 'ctx>,
    /// The VHDL lazy phase table.
    pub vhdl_phases: &'lazy vhdl::lazy::LazyPhaseTable<'sb, 'ast, 'ctx>,
    /// The SystemVerilog scoreboard.
    pub svlog: &'sb svlog::GlobalContext<'ast>,
}

/// The global scoreboard that drives the compilation of pretty much everything.
pub struct ScoreBoard<'ast, 'ctx> {
    /// The arenas within which the various nodes will be allocated.
    arenas: &'ctx Arenas,
    /// The root node ID, where the libraries live.
    pub root: RootRef,
    /// A table of library nodes. This is the only node that is actively
    /// maintained by the global scoreboard.
    libs: RefCell<HashMap<LibRef, (Name, &'ast [Ast<'ast>])>>,
    /// A table of definitions in each scope.
    defs: RefCell<HashMap<ScopeRef, &'ctx Defs>>,
}

impl<'lazy, 'sb, 'ast, 'ctx> GenericContext for ScoreContext<'lazy, 'sb, 'ast, 'ctx> {}

impl<'ast, 'ctx> ScoreBoard<'ast, 'ctx> {
    /// Create a new empty scoreboard.
    pub fn new(arenas: &'ctx Arenas) -> ScoreBoard<'ast, 'ctx> {
        ScoreBoard {
            arenas: arenas,
            root: RootRef::new(NodeId::alloc()),
            libs: RefCell::new(HashMap::new()),
            defs: RefCell::new(HashMap::new()),
        }
    }
}

impl<'ast, 'ctx> std::fmt::Debug for ScoreBoard<'ast, 'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Libraries:")?;
        for (k, v) in self.libs.borrow().iter() {
            write!(f, "\n - {:?}: contains {} root nodes", k, v.1.len())?;
        }
        write!(f, "\nDefs:")?;
        for (k, &v) in self.defs.borrow().iter() {
            write!(f, "\n - scope {:?}: contains {} defs nodes", k, v.len())?;
            for (n, d) in v {
                write!(f, "\n   - `{:?}` -> {:?}", n, d)?;
            }
        }
        Ok(())
    }
}

impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
    /// Obtain a reference to the VHDL context.
    pub fn vhdl(&'lazy self) -> vhdl::score::ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
        vhdl::score::ScoreContext {
            sess: self.sess,
            global: self,
            sb: self.vhdl,
            lazy: self.vhdl_phases,
        }
    }

    /// Add a library to the scoreboard.
    pub fn add_library(&self, name: Name, asts: &'ast [Ast<'ast>]) -> LibRef {
        let id = LibRef::new(NodeId::alloc());
        self.sb.libs.borrow_mut().insert(id, (name, asts));

        // Pass on the VHDL nodes to the VHDL scoreboard.
        let vhdl_ast = asts
            .iter()
            .flat_map(|v| match *v {
                Ast::Vhdl(ref a) => a.iter(),
                _ => [].iter(),
            })
            .collect();
        self.vhdl()
            .add_library(name, vhdl::score::LibRef::new(id.into()), vhdl_ast);

        // Pass on the SystemVerilog nodes to the VHDL scoreboard.
        let svlog_ast = asts.iter().filter_map(|v| match *v {
            Ast::Svlog(ref a) => Some(a),
            _ => None,
        });
        self.svlog.add_root_nodes(svlog_ast);

        id
    }

    /// Obtain the definitions in a scope. Calculate them if needed.
    pub fn defs(&self, id: ScopeRef) -> Result<&'ctx Defs> {
        if let Some(&node) = self.sb.defs.borrow().get(&id) {
            return Ok(node);
        }
        if self.sess.opts.trace_scoreboard {
            println!("[SB] make defs for {:?}", id);
        }
        let node = self.make(id)?;
        if self.sess.opts.trace_scoreboard {
            println!("[SB] defs for {:?} is {:?}", id, node);
        }
        if self.sb.defs.borrow_mut().insert(id, node).is_some() {
            panic!("node should not exist");
        }
        Ok(node)
    }
}

impl<'lazy, 'sb, 'ast, 'ctx> NodeMaker<ScopeRef, &'ctx Defs>
    for ScoreContext<'lazy, 'sb, 'ast, 'ctx>
{
    fn make(&self, id: ScopeRef) -> Result<&'ctx Defs> {
        match id {
            ScopeRef::Root(_) => {
                // Gather the names of all libraries and create a root scope out
                // of them.
                let mut defs = HashMap::new();
                for (&id, &(name, _)) in self.sb.libs.borrow().iter() {
                    if defs.insert(name, Def::Lib(id)).is_some() {
                        self.sess.emit(DiagBuilder2::fatal(format!(
                            "Library `{}` defined multiple times",
                            name
                        )));
                        return Err(());
                    }
                }
                Ok(self.sb.arenas.defs.alloc(defs))
            }

            ScopeRef::Lib(id) => {
                let lib = self.sb.libs.borrow()[&id];
                // Approach:
                // 1) ask vhdl scoreboard for the defs
                // 2) ask svlog scoreboard for the defs
                // 3) create new def that is the union of the two and return

                // Ask the VHDL scoreboard for the definitions in this library.
                let vhdl =
                    self.vhdl()
                        .defs(vhdl::score::ScopeRef::Lib(vhdl::score::LibRef::new(
                            id.into(),
                        )))?;
                if self.sess.opts.trace_scoreboard {
                    println!("[SB] vhdl_sb returned {:?}", vhdl);
                }

                // Build a union of the names defined by the above scoreboards.
                // Then determine the actual definition for each name, and throw
                // an error if multiple definitions are encountered.
                let names: HashSet<Name> = vhdl
                    .iter()
                    .filter_map(|(&k, _)| match k {
                        vhdl::score::ResolvableName::Ident(n) => Some(n),
                        _ => None,
                    })
                    .chain(self.svlog.modules().map(|(k, _)| k))
                    .collect();
                debug!("names defined in library: {:?}", names);

                let mut defs = HashMap::new();
                let mut had_dups = false;
                for name in names {
                    let vhdl_defs = match vhdl.get(&name.into()) {
                        Some(v) => v.iter(),
                        None => [].iter(),
                    };
                    let svlog_defs = self.svlog.find_module(name.into());
                    let both_defs: Vec<Spanned<Def>> = vhdl_defs
                        .map(|d| Spanned::new(Def::Vhdl(d.value), d.span))
                        .chain(
                            svlog_defs.map(|id| Spanned::new(Def::Svlog(id), self.svlog.span(id))),
                        )
                        .collect();

                    if both_defs.len() > 1 {
                        let mut diag =
                            DiagBuilder2::error(format!("`{}` declared multiple times", name));
                        for def in both_defs {
                            diag = diag.span(def.span);
                        }
                        self.sess.emit(diag);
                        had_dups = true;
                        continue;
                    }

                    defs.insert(name, both_defs[0].value);
                }
                if had_dups {
                    return Err(());
                }

                // Return the defs of definitions.
                Ok(self.sb.arenas.defs.alloc(defs))
            }
        }
    }
}

/// A collection of arenas that the scoreboard uses to allocate nodes in. This
/// also contains the sub-arenas for the VHDL- and SystemVerilog-specific
/// scoreboards.
pub struct Arenas {
    pub vhdl: vhdl::score::Arenas,
    defs: Arena<Defs>,
}

impl Arenas {
    /// Create a new collection of arenas for the scoreboard to use.
    pub fn new() -> Arenas {
        Arenas {
            vhdl: vhdl::score::Arenas::new(),
            defs: Arena::new(),
        }
    }
}

/// Roots for every AST that we support. During parsing, a list of these entries
/// is generated that is then passed to the `ScoreBoard` as a reference.
#[derive(Debug)]
pub enum Ast<'a> {
    Vhdl(Vec<vhdl_ast::DesignUnit>),
    Svlog(svlog_ast::Root<'a>),
}

/// The definitions in a scope.
pub type Defs = HashMap<Name, Def>;

// Declare some node references.
node_ref!(RootRef);
node_ref!(LibRef);

// Declare some node reference groups.
node_ref_group!(
    Def: Lib(LibRef),
    Vhdl(vhdl::score::Def),
    Svlog(NodeId), // TODO: handle this case
);
node_ref_group!(ScopeRef: Root(RootRef), Lib(LibRef),);

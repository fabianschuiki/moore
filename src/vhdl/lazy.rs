// Copyright (c) 2018 Fabian Schuiki

//! An implementation of lazy compiler passes.

// #![deny(missing_docs)]

use std;
use std::fmt;
use std::cell::RefCell;

use moore_common::score::Result;
use score::{ScoreBoard, ScoreContext};
// use std::collections::HashMap;
// use futures::Future;
use hir;
use score::WaitStmtRef;

/// A lazily evaluated node.
pub enum LazyNode<F: ?Sized> {
	/// Evaluation is currently running.
	Running,
	/// The callback which will provide the desired output.
	Pending(Box<F>),
}

impl<F> fmt::Debug for LazyNode<F> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			LazyNode::Running => write!(f, "running"),
			LazyNode::Pending(_) => write!(f, "pending"),
		}
	}
}

/// A table of lazy compiler phases.
pub struct LazyPhaseTable<'sb, 'ast: 'sb, 'ctx: 'sb> {
	/// The score board.
	pub sb: &'sb ScoreBoard<'ast, 'ctx>,
	/// The lazy HIR table.
	pub hir: RefCell<LazyHirTable<'sb>>,
}

impl <'sb, 'ast, 'ctx> LazyPhaseTable<'sb, 'ast, 'ctx> {
    /// Create a new phase table.
    pub fn new(sb: &'sb ScoreBoard<'ast, 'ctx>) -> LazyPhaseTable<'sb, 'ast, 'ctx> {
        LazyPhaseTable {
            sb: sb,
            hir: RefCell::new(LazyHirTable::new()),
        }
    }
}

node_storage!(LazyHirTable<'sb>:
	wait_stmts: WaitStmtRef => LazyNode<Fn(&ScoreContext) -> Result<hir::Stmt<hir::WaitStmt>> + 'sb>,
);

// /// A lazy table generator.
// #[macro_export]
// macro_rules! lazy_table {
// 	($name:ident<$lt:tt>: $($node_name:ident : $node_ref:ty => $node:ty,)+) => {
// 		pub struct $name<$lt> {
// 			$($node_name: std::collections::HashMap<$node_ref, Box<Future<Item=$node, Error=()> + $lt>>,)*
// 		}

// 		impl<$lt> $name<$lt> {
// 			/// Create a new empty table.
// 			pub fn new() -> $name<$lt> {
// 				$name {
// 					$($node_name: std::collections::HashMap::new(),)*
// 				}
// 			}
// 		}

// 		$(
// 		impl<$lt> $crate::lazy::LazyTable<$lt, $node_ref> for $name<$lt> {
// 			type Item = $node;

// 			fn get(&self, id: &$node_ref) -> &Future<Item=$node, Error=()> {
// 				self.$node_name.get(id).unwrap()
// 			}

// 			fn set(&mut self, id: $node_ref, node: Box<Future<Item=$node, Error=()> + $lt>) {
// 				self.$node_name.insert(id, node);
// 			}
// 		}
// 		)*
// 	}
// }

// /// A lazy table.
// ///
// /// Entries are described as callbacks which upon first query are used to
// /// determine the actual value of the entry. Further queries will return the
// /// value directly.
// pub trait LazyTable<'a, I> {
// 	type Item;
// 	fn get(&self, id: &I) -> &Future<Item=Self::Item, Error=()>;
// 	fn set(&mut self, id: I, node: Box<Future<Item=Self::Item, Error=()> + 'a>);
// }

// /// A lazy HIR table.
// pub struct LazyHirTable<'sb, 'ctx> {
// 	wait_stmt: HashMap<WaitStmtRef, Box<Future<Item=&'ctx hir::Stmt<hir::WaitStmt>, Error=()> + 'sb>>,
// }

// impl<'sb, 'ctx> LazyHirTable<'sb, 'ctx> {
// 	/// Create a new lazy HIR table.
// 	pub fn new() -> LazyHirTable<'sb, 'ctx> {
// 		LazyHirTable {
// 			wait_stmt: HashMap::new(),
// 		}
// 	}
// }

// impl<'sb, 'ctx> LazyTable<'sb, WaitStmtRef> for LazyHirTable<'sb, 'ctx> {
// 	type Item = &'ctx hir::Stmt<hir::WaitStmt>;

// 	fn get(&self, id: &WaitStmtRef) -> &Future<Item=Self::Item, Error=()> {
// 		self.wait_stmt.get(id).unwrap().as_ref()
// 	}

// 	fn set(&mut self, id: WaitStmtRef, node: Box<Future<Item=Self::Item, Error=()> + 'sb>) {
// 		self.wait_stmt.insert(id, node);
// 	}
// }

// lazy_table!(LazyHirTable<'ctx>:
// 	wait_stmts: WaitStmtRef => &'ctx hir::Stmt<hir::WaitStmt>,
// );

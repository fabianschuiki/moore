// Copyright (c) 2017 Fabian Schuiki

//! This module implements the scoreboard building blocks. Scoreboards are the
//! driving mechanism behind moore. They keep track of the results of each
//! compilation step for every node in the graph. Each node can be accessed in a
//! type safe manner by its ID.

use std;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;
use std::hash::Hash;

use crate::id::NodeId;

/// A context which provides a language-agnostic scoreboard. This is used by
/// the language-specific scoreboards to communicate with the global scoreboard.
pub trait GenericContext {}

/// The `NodeStorage` trait allows for references to nodes to be stored and
/// retrieved via a unique node ID.
///
/// Once a node is created for example in an arena, a reference to it can be
/// stored in a `NodeStorage` to associate it with an ID. If that ID is
/// presented to the `NodeStorage` again, that same reference will be produced.
/// Implementors of this trait are expected to implement it multiple times, once
/// for each different ID/node type pair that they support. This then allows for
/// nodes to be looked up in a type safe manner based on their ID.
///
/// The `NodeStorage` does not assume ownership over the nodes added to it.
/// Therefore all nodes are references of at least the lifetime `'tn`.
///
/// # Example
///
/// ```
/// use moore_common::score::NodeStorage;
/// use std::collections::HashMap;
///
/// #[derive(PartialEq, Eq, Debug)]
/// struct Foo;
/// #[derive(PartialEq, Eq, Debug)]
/// struct Bar;
///
/// #[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
/// struct FooId(usize);
/// #[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
/// struct BarId(usize);
///
/// struct Table<'tn> {
///     foos: HashMap<FooId, &'tn Foo>,
///     bars: HashMap<BarId, &'tn Bar>,
/// }
///
/// impl<'tn> NodeStorage<FooId> for Table<'tn> {
///     type Node = &'tn Foo;
///     fn get(&self, id: &FooId) -> Option<&&'tn Foo> { self.foos.get(id) }
///     fn set(&mut self, id: FooId, node: &'tn Foo) -> Option<&'tn Foo> { self.foos.insert(id, node) }
/// }
///
/// impl<'tn> NodeStorage<BarId> for Table<'tn> {
///     type Node = &'tn Bar;
///     fn get(&self, id: &BarId) -> Option<&&'tn Bar> { self.bars.get(id) }
///     fn set(&mut self, id: BarId, node: &'tn Bar) -> Option<&'tn Bar> { self.bars.insert(id, node) }
/// }
///
/// // Store node refs in table:
/// let foo = Foo;
/// let bar = Bar;
/// let mut tbl = Table{ foos: HashMap::new(), bars: HashMap::new() };
/// tbl.set(FooId(1), &foo);
/// tbl.set(BarId(2), &bar);
///
/// // Retrieve node refs again:
/// assert_eq!(tbl.get(&FooId(1)), Some(&&foo));
/// assert_eq!(tbl.get(&BarId(2)), Some(&&bar));
/// assert_eq!(tbl.get(&BarId(1)), None);
/// assert_eq!(tbl.get(&FooId(2)), None);
///
/// // The following would produce a compiler error due to type mismatch:
/// // let _: &Foo = *tbl.get(&BarId(1)).unwrap();
/// // let _: &Bar = *tbl.get(&FooId(2)).unwrap();
/// ```
pub trait NodeStorage<I> {
    /// The type of the node that is returned when presented with an ID of type
    /// `I`.
    type Node;

    /// Obtains a reference to the node with the given ID.
    ///
    /// Returns `None` when no node with the given ID exists.
    fn get(&self, id: &I) -> Option<&Self::Node>;

    /// Store a reference to a node under the given ID.
    ///
    /// Later that reference can be retrieved again by presenting the same ID to
    /// the `get` function. Returns the previously stored entry, if any.
    fn set(&mut self, id: I, node: Self::Node) -> Option<Self::Node>;
}

// Implement the NodeStorage trait for HashMaps.
impl<K, V> NodeStorage<K> for HashMap<K, V>
where
    K: Hash + Eq,
{
    type Node = V;

    fn get(&self, id: &K) -> Option<&V> {
        HashMap::get(self, id)
    }

    fn set(&mut self, id: K, node: V) -> Option<V> {
        HashMap::insert(self, id, node)
    }
}

// Implement the NodeStorage trait for BTreeMaps.
impl<K, V> NodeStorage<K> for BTreeMap<K, V>
where
    K: Ord,
{
    type Node = V;

    fn get(&self, id: &K) -> Option<&V> {
        BTreeMap::get(self, id)
    }

    fn set(&mut self, id: K, node: V) -> Option<V> {
        BTreeMap::insert(self, id, node)
    }
}

/// The `NodeMaker` trait allows for nodes to be generated from an ID.
///
/// This is useful in conjunction with the `NodeStorage` and `Scoreboard`
/// traits. If a value is requested that the scoreboard cannot find, this trait
/// allows for the node to be generated. For example, if the AST for a node is
/// requested but does not exist, this trait can be implemented in such a way
/// that said AST is loaded. This allows for complex on-demand loading and
/// compilation to be implemented.
///
/// The nodes are expected to be owned either by the caller or some arena.
/// Therefore only a reference to the created node is returned.
///
/// # Example
///
/// ```
/// use moore_common::score::{self, NodeMaker};
///
/// #[derive(PartialEq, Eq, Debug)]
/// struct Foo;
/// #[derive(PartialEq, Eq, Debug)]
/// struct Bar;
///
/// struct FooId(usize);
/// struct BarId(usize);
///
/// struct Table;
///
/// impl<'tn> NodeMaker<FooId, &'tn Foo> for Table {
///     fn make(&self, id: FooId) -> score::Result<&'tn Foo> {
///         Ok(unsafe { &*(1 as *const Foo) }) // usually you would allocate this in an arena
///     }
/// }
///
/// impl<'tn> NodeMaker<BarId, &'tn Bar> for Table {
///     fn make(&self, id: BarId) -> score::Result<&'tn Bar> {
///         Ok(unsafe { &*(1 as *const Bar) }) // usually you would allocate this in an arena
///     }
/// }
///
/// let tbl = Table;
/// let foo = tbl.make(FooId(1)).unwrap();
/// let bar = tbl.make(BarId(2)).unwrap();
/// assert_eq!(foo, &Foo);
/// assert_eq!(bar, &Bar);
///
/// // The following would produce a compiler error due to type mismatch:
/// // assert_eq!(foo, &Bar);
/// // assert_eq!(bar, &Foo);
/// ```
pub trait NodeMaker<I, N> {
    /// Creates the node with the given ID.
    ///
    /// Returns `Err(())` upon failure. Note that the generated node has
    /// lifetime `'tn` that outlives the `NodeMaker`. This is required to allow
    /// for the `NodeMaker` to generate multiple nodes at the same time. The
    /// generated nodes should be owned by an arena or the owner of the
    /// `NodeMaker` itself.
    fn make(&self, id: I) -> Result<N>;
}

/// The result of making a node. Errors that occur while making a node should be
/// reported via a separate channel, e.g. diagnostics, which provide more
/// information to the user.
pub type Result<T> = std::result::Result<T, ()>;

/// A reference to a node.
///
/// Newtypes around `NodeId` should implement this trait to offer functionality
/// common to all node references.
pub trait NodeRef: Copy + Eq + Ord + Hash + Debug + Into<NodeId> {
    /// Allocate a new reference.
    ///
    /// Creates a new unique reference. Calls `NodeId::alloc()` under the hood.
    fn alloc() -> Self {
        Self::new(NodeId::alloc())
    }

    /// Create a new reference from an existing node ID.
    fn new(id: NodeId) -> Self;
}

/// Create a new node reference.
///
/// This is merely a wrapper around `NodeId` to provide a type safe
/// representation of a node.
///
/// # Example
///
/// ```
/// #[macro_use]
/// extern crate moore_common;
/// # extern crate rustc_serialize;
///
/// # fn main() {
/// node_ref!(FooRef);
/// node_ref!(BarRef);
/// # }
/// ```
///
/// This creates two structs `FooRef` and `BarRef` that both wrap around a
/// `NodeId`.
#[macro_export]
macro_rules! node_ref {
    ($name:ident) => {
        #[derive(
            Copy, Clone, PartialEq, Eq, PartialOrd, Ord, RustcEncodable, RustcDecodable, Hash,
        )]
        pub struct $name($crate::NodeId);

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}({:?})", stringify!($name), self.0)
            }
        }

        impl Into<$crate::NodeId> for $name {
            fn into(self) -> $crate::NodeId {
                self.0
            }
        }

        impl $crate::score::NodeRef for $name {
            fn new(id: $crate::NodeId) -> $name {
                $name(id)
            }
        }
    };
}

/// Create a new group of node references.
///
/// This is a simple enum that contains variants for each of the references.
/// Implements `From` for the various references, and `Into<NodeId>`.
#[macro_export]
macro_rules! node_ref_group {
	($name:ident: $($var:ident($ty:ty),)+) => {
		#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, RustcEncodable, RustcDecodable, Hash)]
		pub enum $name {
			$($var($ty),)*
		}

		impl std::fmt::Debug for $name {
			fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
				node_ref_group!(MATCHES *self, $($name::$var(id) => write!(f, "{}({:?})", stringify!($var), id)),*)
			}
		}

		impl Into<$crate::NodeId> for $name {
			fn into(self) -> $crate::NodeId {
				node_ref_group!(MATCHES self, $($name::$var(id) => id.into()),*)
			}
		}

		$(
		impl From<$ty> for $name {
			fn from(id: $ty) -> $name {
				$name::$var(id)
			}
		}
		)*
	};

	(MATCHES $value:expr, $($lhs:pat => $rhs:expr),+) => {
		match $value {
			$($lhs => $rhs),+
		}
	};
}

/// Create a new table that implements the `NodeStorage` trait.
///
/// The resulting table can then be used to store nodes in a type safe manner.
///
/// # Example
///
/// ```
/// #[macro_use]
/// extern crate moore_common;
/// use moore_common::score::NodeStorage;
/// # extern crate rustc_serialize;
/// # use std::collections::HashMap;
///
/// #[derive(PartialEq, Eq, Hash, Debug)]
/// struct FooRef(usize);
/// #[derive(PartialEq, Eq, Hash, Debug)]
/// struct BarRef(usize);
///
/// #[derive(PartialEq, Eq, Debug)]
/// struct Foo;
/// #[derive(PartialEq, Eq, Debug)]
/// struct Bar;
///
/// node_storage!(NodeTable<'tn>:
///     foos: FooRef => &'tn Foo,
///     bars: BarRef => &'tn Bar,
/// );
///
/// # fn main() {
/// let foo = &Foo;
/// let bar = &Bar;
///
/// let mut tbl = NodeTable::new();
/// tbl.set(FooRef(0), foo);
/// tbl.set(BarRef(1), bar);
///
/// assert_eq!(tbl.get(&FooRef(0)), Some(&foo));
/// assert_eq!(tbl.get(&BarRef(1)), Some(&bar));
///
/// // The following would produce a compiler error due to the type mismatch:
/// // assert_eq!(tbl.get(&BarRef(0)), Some(&foo));
/// // assert_eq!(tbl.get(&FooRef(1)), Some(&bar));
/// # }
/// ```
#[macro_export]
macro_rules! node_storage {
	($name:ident<$($lt:tt),+>: $($node_name:ident : $node_ref:ty => $node:ty,)+) => {
		pub struct $name<$($lt),*> {
			$($node_name: std::collections::HashMap<$node_ref, $node>,)*
		}

		node_storage!(STRUCT_IMPL $name; $($lt),*; $($node_name, $node_ref, $node;)*);
	};

	($name:ident<$($lt:tt),+> where ($($wh:tt)+): $($node_name:ident : $node_ref:ty => $node:ty,)+) => {
		pub struct $name<$($lt),*> where $($wh)* {
			$($node_name: std::collections::HashMap<$node_ref, $node>,)*
		}

		node_storage!(STRUCT_IMPL $name; $($lt),*; $($node_name, $node_ref, $node;)*);
	};

	(STRUCT_IMPL $name:ident; $($lt:tt),+; $($node_name:ident, $node_ref:ty, $node:ty;)*) => {
		impl<$($lt),*> $name<$($lt),*> {
			/// Create a new empty table.
			pub fn new() -> $name<$($lt),*> {
				$name {
					$($node_name: std::collections::HashMap::new(),)*
				}
			}
		}

		node_storage!(TRAIT_IMPL $name; $($lt),*; $($node_name, $node_ref, $node;)*);
	};

	(TRAIT_IMPL $name:ident; $($lt:tt),+; $node_name:ident, $node_ref:ty, $node:ty; $($tail_name:ident, $tail_ref:ty, $tail:ty;)*) => {
		impl<$($lt),*> $crate::score::NodeStorage<$node_ref> for $name<$($lt),*> {
			type Node = $node;

			fn get(&self, id: &$node_ref) -> Option<&$node> {
				self.$node_name.get(id)
			}

			fn set(&mut self, id: $node_ref, node: $node) -> Option<$node> {
				self.$node_name.insert(id, node)
			}
		}

		node_storage!(TRAIT_IMPL $name; $($lt),*; $($tail_name, $tail_ref, $tail;)*);
	};

	(TRAIT_IMPL $name:ident; $($lt:tt),*;) => {}
}

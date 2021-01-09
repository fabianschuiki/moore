// Copyright (c) 2016-2021 Fabian Schuiki

//! Procedural macros for the moore compiler.

extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;

mod accept_visitor;
mod all_node;
mod arena;
mod node;
mod node_data;
mod query;
mod visitor;
mod walk_visitor;

/// Pick the first lifetime from a `syn::Generics`, or create one.
///
/// This either returns the first lifetime in the generics, or adds a new
/// lifetime.
fn first_lifetime(gen: &mut syn::Generics) -> syn::Lifetime {
    // Check if there already is a lifetime that we can use.
    if let Some(ltdef) = gen.lifetimes().next() {
        return ltdef.lifetime.clone();
    }

    // Otherwise generate one.
    let ltdef: syn::LifetimeDef = syn::parse_str("'a").unwrap();
    let lt = ltdef.lifetime.clone();
    gen.params.insert(0, syn::GenericParam::Lifetime(ltdef));
    lt
}

/// Generate an `AcceptVisitor` implementation.
#[proc_macro_derive(AcceptVisitor, attributes(dont_visit))]
pub fn accept_visitor(input: TokenStream) -> TokenStream {
    accept_visitor::accept_visitor(input, false)
}

/// Generate an `AcceptVisitor`, `ForEachNode`, and `ForEachChild` implementation.
#[proc_macro_derive(AcceptVisitorAndForeach, attributes(dont_visit))]
pub fn accept_visitor_and_foreach(input: TokenStream) -> TokenStream {
    accept_visitor::accept_visitor(input, true)
}

/// Wrap a struct or enum in a `Node`.
#[proc_macro_attribute]
pub fn node(args: TokenStream, input: TokenStream) -> TokenStream {
    node::node(args, input)
}

/// Generate an `AnyNodeData` implementation.
#[proc_macro_derive(AnyNodeData, attributes(name, forward, indefinite, definite))]
pub fn node_data(input: TokenStream) -> TokenStream {
    node_data::node_data(input)
}

/// Generate corresponding `*_visit_*` functions in a visitor.
#[proc_macro_attribute]
pub fn walk_visitor(args: TokenStream, input: TokenStream) -> TokenStream {
    walk_visitor::walk_visitor(args, input)
}

/// Convenience macro to derive `AcceptVisitorAndForeach` and `walk_visitor`.
#[proc_macro_attribute]
pub fn visit(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    TokenStream::from(quote! {
        #[moore_derive::walk_visitor]
        #[derive(moore_derive::AcceptVisitorAndForeach)]
        #input
    })
}

/// Convenience macro to derive `AcceptVisitor` and `walk_visitor`.
#[proc_macro_attribute]
pub fn visit_without_foreach(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    TokenStream::from(quote! {
        #[moore_derive::walk_visitor]
        #[derive(moore_derive::AcceptVisitor)]
        #input
    })
}

/// Generate a `AllNode` enum.
#[proc_macro]
pub fn derive_all_node(input: TokenStream) -> TokenStream {
    all_node::all_node(input)
}

/// Mark a node to be included in the `AllNode` enum.
#[proc_macro_attribute]
pub fn all_node(args: TokenStream, input: TokenStream) -> TokenStream {
    all_node::mark_all_node(args, input)
}

/// Generate a `Visitor` trait.
#[proc_macro]
pub fn derive_visitor(input: TokenStream) -> TokenStream {
    visitor::visitor(input)
}

/// Mark a function as a compiler query.
#[proc_macro_attribute]
pub fn query(args: TokenStream, input: TokenStream) -> TokenStream {
    query::mark_query(args, input)
}

/// Generate a compiler query database.
#[proc_macro]
pub fn derive_query_db(input: TokenStream) -> TokenStream {
    query::derive_query_db(input)
}

/// Generate an arena struct.
#[proc_macro]
pub fn derive_arena(input: TokenStream) -> TokenStream {
    arena::derive_arena(input)
}

/// Mark an item to be allocatable in an arena.
#[proc_macro_attribute]
pub fn arena(args: TokenStream, input: TokenStream) -> TokenStream {
    arena::mark_arena(args, input)
}

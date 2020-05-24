// Copyright (c) 2016-2020 Fabian Schuiki

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{
    parse::{Parse, ParseStream},
    DeriveInput,
};

pub(crate) fn node(args: TokenStream, input: TokenStream) -> TokenStream {
    // Parse the input.
    let _args = syn::parse_macro_input!(args as NodeConfig);
    let mut input = syn::parse_macro_input!(input as DeriveInput);

    // Extract the name of the node.
    let vis = input.vis.clone();
    let generics = input.generics.clone();
    let node_name = input.ident.clone();

    // Rename the node.
    let data_name = format_ident!("{}{}", node_name, "Data");
    input.ident = data_name.clone();

    // Generate the wrapper node.
    let mut output = proc_macro2::TokenStream::new();
    output.extend(quote! {
        #[moore_derive::walk_visitor]
        #vis type #node_name #generics = Node<'a, #data_name #generics>;
    });

    // Emit the modified data.
    output.extend(quote! {
        #[derive(moore_derive::AcceptVisitor)]
        #input
    });

    // Schedule the node for inclusion in `AllNode`.
    crate::all_node::add_node(&node_name, &generics);

    // Implement the `AnyNode` trait for this node.
    output.extend(quote! {
        impl<'a> AnyNode<'a> for #node_name #generics {
            fn as_all(&'a self) -> AllNode<'a> {
                AllNode::from(self)
            }

            fn as_any(&'a self) -> &'a AnyNode<'a> {
                self
            }
        }
    });

    // match &input.data {
    //     syn::Data::Struct(input) => println!("found struct {:?}", input),
    //     syn::Data::Enum(input) => println!("found enum {:?}", input),
    //     _ => panic!("unsupported item"),
    // }

    output.into()
}

struct NodeConfig {}

impl Parse for NodeConfig {
    fn parse(_input: ParseStream) -> syn::Result<Self> {
        Ok(NodeConfig {})
    }
}

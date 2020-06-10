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
    let node_name_str = node_name.to_string();

    // Rename the node.
    let data_name = format_ident!("{}{}", node_name, "Data");
    input.ident = data_name.clone();

    // Ensure the new type alias has at least one lifetime.
    let mut impl_generics = generics.clone();
    let lt = crate::first_lifetime(&mut impl_generics);

    // Generate the wrapper node.
    let mut output = proc_macro2::TokenStream::new();
    output.extend(quote! {
        #[moore_derive::arena]
        #[moore_derive::walk_visitor(node)]
        #vis type #node_name #impl_generics = Node<#lt, #data_name #generics>;
    });

    // Emit the modified data.
    output.extend(quote! {
        #[derive(
            moore_derive::AcceptVisitorAndForeach,
            moore_derive::AnyNodeData
        )]
        #input
    });

    // Schedule the node for inclusion in `AllNode`.
    crate::all_node::add_node(&node_name, &impl_generics);

    // Implement the `BasicNode` trait for this node.
    output.extend(quote! {
        impl #impl_generics BasicNode<#lt> for #node_name #impl_generics {
            fn type_name(&self) -> &'static str {
                #node_name_str
            }

            fn as_all(&#lt self) -> AllNode<#lt> {
                AllNode::from(self)
            }

            fn as_any(&#lt self) -> &#lt AnyNode<#lt> {
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

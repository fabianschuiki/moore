// Copyright (c) 2016-2020 Fabian Schuiki

use heck::SnakeCase;
use proc_macro::TokenStream;
use proc_macro2::Ident;
use quote::{format_ident, quote, ToTokens};
use std::cell::RefCell;
use syn::{Generics, Item};

// CAUTION: This is all wildly unstable and relies on the compiler maintaining
// a certain order between proc macro expansions. So this could break any
// minute. Better have a robust CI.
thread_local! {
    static NODES: RefCell<Vec<Node>> = Default::default();
}

struct Node {
    name: String,
    generics: String,
}

pub(crate) fn add_node(name: &Ident, generics: &Generics) {
    // Map everything to a string here. Compiler panics horribly if we hand out
    // the actual idents and generics.
    let node = Node {
        name: name.to_string(),
        generics: generics.to_token_stream().to_string(),
    };
    NODES.with(|c| c.borrow_mut().push(node));
}

pub(crate) fn all_node(_input: TokenStream) -> TokenStream {
    // Flush the accumulated nodes.
    let nodes = NODES.with(|c| std::mem::replace(&mut *c.borrow_mut(), Default::default()));

    // Catch the trivial case of an empty node list.
    if nodes.is_empty() {
        panic!("no nodes marked for AllNode generation");
    }

    // Determine a lifetime for the enum.
    let lt: syn::Lifetime = syn::parse_str("'a").unwrap();

    // Generate the enum variants.
    let mut variants = vec![];
    let mut from_impls = vec![];
    let mut get_funcs = vec![];
    let mut is_funcs = vec![];
    let mut unwrap_funcs = vec![];
    let mut variant_names = vec![];
    for node in nodes {
        // Convert the name back to identifiers and re-parse the generics.
        let name = format_ident!("{}", node.name);
        let generics: syn::Generics = syn::parse_str(&node.generics).unwrap();

        let mut impl_generics = generics.clone();
        let var_lt = crate::first_lifetime(&mut impl_generics);

        // Render the corresponding variant.
        variants.push(quote! {
            #name(&#lt #name #generics),
        });
        variant_names.push(name.clone());

        // Render the corresponding `From` implementation.
        from_impls.push(quote! {
            impl #impl_generics From<&#var_lt #name #generics> for AllNode<#var_lt> {
                fn from(node: &#var_lt #name #generics) -> Self {
                    Self::#name(node)
                }
            }
        });

        // Render the corresponding `get_*` function.
        let get_fn = format_ident!("get_{}", node.name.to_snake_case());
        let get_doc = format!(
            r#"Get the underlying `{0}`, or `None` if the node is not a `{0}`.
            "#,
            name
        );
        get_funcs.push(quote! {
            #[doc = #get_doc]
            pub fn #get_fn(self) -> Option<&#lt #name #generics> {
                match self {
                    Self::#name(node) => Some(node),
                    _ => None,
                }
            }
        });

        // Render the corresponding `is_*` function.
        let is_fn = format_ident!("is_{}", node.name.to_snake_case());
        let is_doc = format!(
            r#"Check whether this is a `{}` node.
            "#,
            name
        );
        is_funcs.push(quote! {
            #[doc = #is_doc]
            pub fn #is_fn(self) -> bool {
                match self {
                    Self::#name(..) => true,
                    _ => false,
                }
            }
        });

        // Render the corresponding `unwrap_*` function.
        let unwrap_fn = format_ident!("unwrap_{}", node.name.to_snake_case());
        let unwrap_doc = format!(
            r#"Get the underlying `{0}`, or panic if the node is not a `{0}`.
            "#,
            name
        );
        unwrap_funcs.push(quote! {
            #[doc = #unwrap_doc]
            pub fn #unwrap_fn(self) -> &#lt #name #generics {
                match self.#get_fn() {
                    Some(node) => node,
                    None => panic!("node is not a {}", stringify!(#name)),
                }
            }
        });
    }

    let output = quote! {
        /// An exhaustive list of all nodes.
        #[derive(Copy, Clone, Debug)]
        pub enum AllNode<#lt> {
            #(#variants)*
        }

        impl<#lt> AllNode<#lt> {
            #(#get_funcs)*
            #(#is_funcs)*
            #(#unwrap_funcs)*

            /// Convert to an `AnyNode` trait object.
            pub fn as_any(self) -> &'a dyn AnyNode<'a> {
                match self {
                    #(Self::#variant_names(node) => node,)*
                }
            }
        }

        #(#from_impls)*
    };
    output.into()
}

pub(crate) fn mark_all_node(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as Item);
    let (name, generics) = match &input {
        Item::Enum(item) => (&item.ident, &item.generics),
        Item::Struct(item) => (&item.ident, &item.generics),
        Item::Type(item) => (&item.ident, &item.generics),
        _ => panic!("unsupported item to add to AllNode"),
    };
    add_node(&name, &generics);
    let output = quote! {
        #input
    };
    output.into()
}

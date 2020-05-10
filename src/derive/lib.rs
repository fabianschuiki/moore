// Copyright (c) 2016-2020 Fabian Schuiki

//! Procedural macros for the moore compiler.

extern crate proc_macro;
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, DeriveInput};

fn is_child_field(field: &syn::Field) -> bool {
    let tystr = field.ty.to_token_stream().to_string();
    if tystr.chars().nth(0).unwrap().is_lowercase() {
        return false;
    }
    if tystr == "Span" || tystr == "Spanned" {
        return false;
    }
    if field
        .attrs
        .iter()
        .any(|attr| attr.path.to_token_stream().to_string() == "ignore_child")
    {
        return false;
    }
    true
}

#[proc_macro_derive(CommonNode, attributes(ignore_child))]
pub fn derive_common_node(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    // println!("derive(CommonNode) on `{}`", input.ident);

    // Assemble the body of the `children()` method.
    let mut child_fields = vec![];
    match &input.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => {
                for field in &fields.named {
                    if is_child_field(field) {
                        let n = field.ident.as_ref().unwrap();
                        child_fields.push(quote! { #n });
                    }
                }
            }
            syn::Fields::Unnamed(fields) => {
                for (i, field) in fields.unnamed.iter().enumerate() {
                    if is_child_field(field) {
                        let i = syn::Index::from(i);
                        child_fields.push(quote! { #i });
                    }
                }
            }
            syn::Fields::Unit => (),
        },
        syn::Data::Enum(_data) => (),
        syn::Data::Union(_) => (),
    }

    // Emit the trait implementation.
    let name = &input.ident;
    let generics = &input.generics;
    let output = quote! {
        impl #generics CommonNode for #name #generics {
            fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode)) {
                #( f(&self.#child_fields); )*
            }
        }
    };
    output.into()
}

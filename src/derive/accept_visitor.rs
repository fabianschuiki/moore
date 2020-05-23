// Copyright (c) 2016-2020 Fabian Schuiki

use heck::SnakeCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::DeriveInput;

pub(crate) fn accept_visitor(input: TokenStream) -> TokenStream {
    // Parse the input.
    let input = syn::parse_macro_input!(input as DeriveInput);
    let mut output = proc_macro2::TokenStream::new();

    let name = &input.ident;
    let generics = &input.generics;

    // Generate the match that visits the relevant fields of the input.
    let mut visits = vec![];
    match &input.data {
        syn::Data::Struct(input) => {
            let visit = visit_fields(&input.fields);
            visits.push(quote! {
                #name #visit
            });
        }
        syn::Data::Enum(input) => {
            for variant in &input.variants {
                let variant_name = &variant.ident;
                let visit = visit_fields(&variant.fields);
                visits.push(quote! {
                    #name::#variant_name #visit
                });
            }
        }
        _ => panic!("unsupported item for AcceptVisitor"),
    };

    // Determine the name of the `visit_*` function corresponding to us.
    let visit_call = format_ident!(
        "visit_{}",
        name.to_string().to_snake_case(),
        span = name.span()
    );

    // Generate the implementation of the `AcceptVisitor` trait.
    output.extend(quote! {
        impl #generics AcceptVisitor for #name #generics {
            fn accept<V: Visitor + ?Sized>(&self, visitor: &mut V) {
                match self {
                    #(#visits,)*
                }
            }

            fn visit<V: Visitor + ?Sized>(&self, visitor: &mut V) {
                visitor.#visit_call(self);
            }
        }
    });

    output.into()
}

/// Generate the code to visit fields in a struct-like item.
fn visit_fields(fields: &syn::Fields) -> proc_macro2::TokenStream {
    // Generate a destructuring pattern that assigns predictable names to all
    // fields.
    let mut names = vec![];
    let pat = match fields {
        syn::Fields::Named(ref fields) => {
            let mut mapping = vec![];
            for (i, field) in fields.named.iter().enumerate() {
                let field_name = &field.ident;
                let name = format_ident!("arg{}", i);
                names.push(name.clone());
                mapping.push(quote! {
                    #field_name: #name
                });
            }
            quote! { {#(#mapping),*} }
        }
        syn::Fields::Unnamed(ref fields) => {
            let mut mapping = vec![];
            for (i, _) in fields.unnamed.iter().enumerate() {
                let name = format_ident!("arg{}", i);
                names.push(name.clone());
                mapping.push(name);
            }
            quote! { (#(#mapping),*) }
        }
        syn::Fields::Unit => {
            quote! {}
        }
    };

    // Generate the visit calls for the names that we do not skip or ignore.
    quote! {
        #pat => {
            #(#names.visit(visitor);)*
        }
    }
}

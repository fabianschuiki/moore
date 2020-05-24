// Copyright (c) 2016-2020 Fabian Schuiki

use proc_macro::TokenStream;
use quote::{format_ident, quote, ToTokens};
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

    // Determine the impl generics, which may add another lifetime.
    let mut impl_generics = generics.clone();
    let lt = crate::determine_lifetime(&mut impl_generics);

    // Generate the implementation of the `AcceptVisitor` trait.
    output.extend(quote! {
        impl #impl_generics AcceptVisitor<#lt> for #name #generics {
            fn accept<V: Visitor<#lt> + ?Sized>(&#lt self, visitor: &mut V) {
                match self {
                    #(#visits,)*
                }
            }
        }
    });

    output.into()
}

/// Check if a field has the `#[dont_visit]` attribute.
fn has_dont_visit(attrs: &[syn::Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| attr.to_token_stream().to_string() == "# [dont_visit]")
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
                if !has_dont_visit(&field.attrs) {
                    names.push(name.clone());
                }
                mapping.push(quote! {
                    #field_name: #name
                });
            }
            quote! { {#(#mapping),*} }
        }
        syn::Fields::Unnamed(ref fields) => {
            let mut mapping = vec![];
            for (i, field) in fields.unnamed.iter().enumerate() {
                let name = format_ident!("arg{}", i);
                if !has_dont_visit(&field.attrs) {
                    names.push(name.clone());
                }
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
            #(#names.walk(visitor);)*
        }
    }
}

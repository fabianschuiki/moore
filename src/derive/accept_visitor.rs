// Copyright (c) 2016-2020 Fabian Schuiki

use proc_macro::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::DeriveInput;

pub(crate) fn accept_visitor(input: TokenStream, with_foreach: bool) -> TokenStream {
    // Parse the input.
    let input = syn::parse_macro_input!(input as DeriveInput);
    let mut output = proc_macro2::TokenStream::new();

    let name = &input.ident;
    let generics = &input.generics;

    // Generate the match that visits the relevant fields of the input.
    let mut visits = vec![];
    let mut eachs = vec![];
    let dont_visit = has_dont_visit(&input.attrs);
    match &input.data {
        syn::Data::Struct(input) => {
            let (visit, each) = visit_fields(&input.fields, dont_visit);
            visits.push(quote! {
                #name #visit
            });
            eachs.push(quote! {
                #name #each
            });
        }
        syn::Data::Enum(input) => {
            for variant in &input.variants {
                let dont_visit = dont_visit || has_dont_visit(&variant.attrs);
                let variant_name = &variant.ident;
                let (visit, each) = visit_fields(&variant.fields, dont_visit);
                visits.push(quote! {
                    #name::#variant_name #visit
                });
                eachs.push(quote! {
                    #name::#variant_name #each
                });
            }
        }
        _ => panic!("unsupported item for AcceptVisitor"),
    };

    // Determine the impl generics, which may add another lifetime.
    let mut impl_generics = generics.clone();
    let lt = crate::first_lifetime(&mut impl_generics);

    // Generate the implementation of the `AcceptVisitor` trait.
    output.extend(quote! {
        impl #impl_generics AcceptVisitor<#lt> for #name #generics {
            fn accept(&#lt self, visitor: &mut dyn Visitor<#lt>) {
                match self {
                    #(#visits,)*
                }
            }
        }
    });
    if with_foreach {
        output.extend(quote! {
            impl #impl_generics ForEachChild<#lt> for #name #generics {
                fn for_each_child(&#lt self, each: &mut dyn FnMut(&#lt dyn AnyNode<#lt>)) {
                    match self {
                        #(#eachs,)*
                    }
                }
            }

            impl #impl_generics ForEachNode<#lt> for #name #generics {
                fn for_each_node(&#lt self, each: &mut dyn FnMut(&#lt dyn AnyNode<#lt>)) {
                    self.for_each_child(each);
                }
            }
        });
    }

    output.into()
}

/// Check if a field has the `#[dont_visit]` attribute.
fn has_dont_visit(attrs: &[syn::Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| attr.to_token_stream().to_string() == "# [dont_visit]")
}

/// Generate the code to visit fields in a struct-like item.
fn visit_fields(
    fields: &syn::Fields,
    dont_visit: bool,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    // Generate a destructuring pattern that assigns predictable names to all
    // fields.
    let mut names = vec![];
    let pat = match fields {
        syn::Fields::Named(ref fields) => {
            let mut mapping = vec![];
            for (i, field) in fields.named.iter().enumerate() {
                let field_name = &field.ident;
                let name = format_ident!("arg{}", i);
                if !dont_visit && !has_dont_visit(&field.attrs) {
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
                if !dont_visit && !has_dont_visit(&field.attrs) {
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
    (
        quote! {
            #pat => {
                #(#names.walk(visitor);)*
            }
        },
        quote! {
            #pat => {
                #(#names.for_each_node(each);)*
            }
        },
    )
}

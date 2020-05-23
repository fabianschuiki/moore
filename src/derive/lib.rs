// Copyright (c) 2016-2020 Fabian Schuiki

//! Procedural macros for the moore compiler.

extern crate proc_macro;
use heck::SnakeCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::{parse_macro_input, spanned::Spanned, DeriveInput};

mod accept_visitor;
mod call_visitor;
mod node;

fn is_child_field(field: &syn::Field) -> bool {
    let tystr = field.ty.to_token_stream().to_string();
    if tystr.chars().nth(0).unwrap().is_lowercase() {
        return false;
    }
    if tystr == "Span"
        || tystr.starts_with("Spanned")
        // || tystr.starts_with("Vec")
        || tystr.starts_with("Option")
    {
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

    // Gather all fields in the structure.
    let mut all_fields = vec![];
    match &input.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => {
                for field in &fields.named {
                    let n = field.ident.as_ref().unwrap();
                    all_fields.push((quote! { #n }, field));
                }
            }
            syn::Fields::Unnamed(fields) => {
                for (i, field) in fields.unnamed.iter().enumerate() {
                    let i = syn::Index::from(i);
                    all_fields.push((quote! { #i }, field));
                }
            }
            syn::Fields::Unit => (),
        },
        syn::Data::Enum(_data) => (),
        syn::Data::Union(_) => (),
    }

    // Assemble the body of the `for_each_child` method.
    let child_fields = all_fields.iter().flat_map(|(name, field)| {
        if is_child_field(field) {
            Some(name)
        } else {
            None
        }
    });

    // Assemble the body of the `AcceptVisitor` trait.
    let visit_fields = all_fields.iter().flat_map(|(name, field)| {
        if !is_child_field(field) {
            return None;
        }
        match &field.ty {
            syn::Type::Path(path) => {
                let ident = &path.path.segments.last().unwrap().ident.to_string();
                if ident == "Vec" || ident == "Option" {
                    Some(quote! { self.#name.accept(visitor); })
                } else {
                    let method_name =
                        format_ident!("visit_{}", ident.to_snake_case(), span = field.ty.span());
                    Some(quote! { visitor.#method_name(&self.#name); })
                }
            }
            _ => None,
        }
    });

    // Emit the trait implementation.
    let name = &input.ident;
    let generics = &input.generics;
    let visit_call = format_ident!(
        "visit_{}",
        name.to_string().to_snake_case(),
        span = name.span()
    );
    let output = quote! {
        impl #generics CommonNode for #name #generics {
            fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode)) {
                #( f(&self.#child_fields); )*
            }
        }

        impl #generics AcceptVisitor for #name #generics {
            fn accept<V: Visitor + ?Sized>(&self, visitor: &mut V) {
                #(#visit_fields)*
            }
        }

        impl #generics CallVisitor for #name #generics {
            fn visit<V: Visitor + ?Sized>(&self, visitor: &mut V) {
                visitor.#visit_call(self);
            }
        }
    };
    output.into()
}

#[proc_macro_derive(AcceptVisitor, attributes(dont_visit))]
pub fn derive_accept_visitor(input: TokenStream) -> TokenStream {
    accept_visitor::accept_visitor(input)
}

#[proc_macro_attribute]
pub fn call_visitor(args: TokenStream, input: TokenStream) -> TokenStream {
    call_visitor::call_visitor(args, input)
}

#[proc_macro_attribute]
pub fn node(args: TokenStream, input: TokenStream) -> TokenStream {
    node::node(args, input)
}

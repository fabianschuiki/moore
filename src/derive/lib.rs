// Copyright (c) 2016-2020 Fabian Schuiki

//! Procedural macros for the moore compiler.

extern crate proc_macro;
use heck::SnakeCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::{parse_macro_input, DeriveInput};

mod accept_visitor;
mod node;
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
        Some(quote! { self.#name.walk(visitor); })
    });

    // Emit the trait implementation.
    let name = &input.ident;
    let generics = &input.generics;
    let mut impl_generics = generics.clone();
    let lt = first_lifetime(&mut impl_generics);
    let pre_visit_fn = format_ident!(
        "pre_visit_{}",
        name.to_string().to_snake_case(),
        span = name.span()
    );
    let post_visit_fn = format_ident!(
        "post_visit_{}",
        name.to_string().to_snake_case(),
        span = name.span()
    );
    crate::visitor::add_call(&name, &generics);
    let output = quote! {
        impl #generics CommonNode for #name #generics {
            fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode)) {
                #( f(&self.#child_fields); )*
            }
        }

        impl #impl_generics AcceptVisitor<#lt> for #name #generics {
            fn accept<V: Visitor<#lt> + ?Sized>(&#lt self, visitor: &mut V) {
                #(#visit_fields)*
            }
        }

        impl #impl_generics WalkVisitor<#lt> for #name #generics {
            fn walk<V: Visitor<#lt> + ?Sized>(&#lt self, visitor: &mut V) {
                if visitor.#pre_visit_fn(self) {
                    self.accept(visitor);
                }
                visitor.#post_visit_fn(self);
            }
        }
    };
    output.into()
}

/// Generate an `AcceptVisitor` implementation.
#[proc_macro_derive(AcceptVisitor, attributes(dont_visit))]
pub fn accept_visitor(input: TokenStream) -> TokenStream {
    accept_visitor::accept_visitor(input)
}

#[proc_macro_attribute]
pub fn node(args: TokenStream, input: TokenStream) -> TokenStream {
    node::node(args, input)
}

#[proc_macro]
pub fn visitor(input: TokenStream) -> TokenStream {
    visitor::visitor(input)
}

/// Generate corresponding `*_visit_*` functions in a visitor.
#[proc_macro_attribute]
pub fn walk_visitor(args: TokenStream, input: TokenStream) -> TokenStream {
    walk_visitor::walk_visitor(args, input)
}

/// Convenience macro to derive `AcceptVisitor` and `walk_visitor`.
#[proc_macro_attribute]
pub fn visit(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    TokenStream::from(quote! {
        #[moore_derive::walk_visitor]
        #[derive(AcceptVisitor)]
        #input
    })
}

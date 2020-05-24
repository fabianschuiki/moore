// Copyright (c) 2016-2020 Fabian Schuiki

use heck::SnakeCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::Item;

pub(crate) fn call_visitor(_args: TokenStream, raw_input: TokenStream) -> TokenStream {
    // Parse the input.
    let input = syn::parse_macro_input!(raw_input as Item);
    let (name, generics) = match &input {
        Item::Enum(item) => (&item.ident, &item.generics),
        Item::Struct(item) => (&item.ident, &item.generics),
        Item::Type(item) => (&item.ident, &item.generics),
        _ => panic!("unsupported item to derive CallVisitor for"),
    };

    // Determine the name of the visit functions corresponding to us.
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

    // Determine the impl generics, which may add another lifetime.
    let mut impl_generics = generics.clone();
    let lt = crate::determine_lifetime(&mut impl_generics);

    // Generate the implementation of the `CallVisitor` trait.
    let output = quote! {
        #input

        impl #impl_generics CallVisitor<#lt> for #name #generics {
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

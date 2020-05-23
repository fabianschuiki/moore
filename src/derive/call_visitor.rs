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

    // Determine the name of the `visit_*` function corresponding to us.
    let visit_call = format_ident!(
        "visit_{}",
        name.to_string().to_snake_case(),
        span = name.span()
    );

    // Generate the implementation of the `CallVisitor` trait.
    let output = quote! {
        #input

        impl #generics CallVisitor for #name #generics {
            fn visit<V: Visitor + ?Sized>(&self, visitor: &mut V) {
                visitor.#visit_call(self);
            }
        }
    };
    output.into()
}

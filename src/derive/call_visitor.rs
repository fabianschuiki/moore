// Copyright (c) 2016-2020 Fabian Schuiki

use proc_macro::TokenStream;
use quote::quote;
use syn::Item;

pub(crate) fn call_visitor(_args: TokenStream, input: TokenStream) -> TokenStream {
    // Parse the input.
    let input = syn::parse_macro_input!(input as Item);
    let (name, generics) = match &input {
        Item::Enum(item) => (&item.ident, &item.generics),
        Item::Struct(item) => (&item.ident, &item.generics),
        Item::Type(item) => (&item.ident, &item.generics),
        _ => panic!("unsupported item to derive CallVisitor for"),
    };

    // Ensure that the visitor will contain visit calls for this type.
    crate::visitor::add_call(&name, &generics);

    // Return the input.
    let output = quote! { #input };
    output.into()
}

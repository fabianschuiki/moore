// Copyright (c) 2016-2020 Fabian Schuiki

use heck::SnakeCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::Item;

pub(crate) fn walk_visitor(args: TokenStream, raw_input: TokenStream) -> TokenStream {
    // Parse the input.
    let input = syn::parse_macro_input!(raw_input as Item);
    let (name, generics) = match &input {
        Item::Enum(item) => (&item.ident, &item.generics),
        Item::Struct(item) => (&item.ident, &item.generics),
        Item::Type(item) => (&item.ident, &item.generics),
        _ => panic!("unsupported item to derive WalkVisitor for"),
    };

    // Parse the additional funnel function name.
    let funnel_name = syn::parse_macro_input!(args as Option<syn::Ident>);

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
    let lt = crate::first_lifetime(&mut impl_generics);
    // let lt: syn::Lifetime = syn::parse_str("'a").unwrap();

    // Generate some documentation.
    let doc = format!(
        r#"
        Walk a visitor over `self`.

        Calling this function is equivalent to calling:
        - `visitor.{}(self)`
        - `self.accept(visitor)`
        - `visitor.{}(self);`
        "#,
        pre_visit_fn, post_visit_fn,
    );

    // Assemble the sequence of pre- and post-visit functions.
    let mut pre_visit_calls = vec![];
    let mut post_visit_calls = vec![];
    pre_visit_calls.push(quote! {
        let mut visit = visitor.#pre_visit_fn(self);
    });
    post_visit_calls.push(quote! {
        visitor.#post_visit_fn(self);
    });

    if let Some(funnel_name) = funnel_name {
        let pre_funnel_fn = format_ident!("pre_visit_{}", funnel_name);
        let post_funnel_fn = format_ident!("post_visit_{}", funnel_name);
        pre_visit_calls.push(quote! {
            if visit { visit = visitor.#pre_funnel_fn(self); }
        });
        post_visit_calls.push(quote! {
            visitor.#post_funnel_fn(self);
        });
    }

    post_visit_calls.reverse();

    // Generate the implementation of the `WalkVisitor` trait.
    let output = quote! {
        #input

        impl #impl_generics WalkVisitor<#lt> for #name #generics {
            #[doc = #doc]
            fn walk(&#lt self, visitor: &mut dyn Visitor<#lt>) {
                #(#pre_visit_calls)*
                if visit {
                    self.accept(visitor);
                }
                #(#post_visit_calls)*
            }
        }
    };
    output.into()
}

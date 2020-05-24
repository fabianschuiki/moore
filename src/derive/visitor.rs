// Copyright (c) 2016-2020 Fabian Schuiki

use heck::SnakeCase;
use proc_macro::TokenStream;
use proc_macro2::Ident;
use quote::{format_ident, quote, ToTokens};
use std::{cell::RefCell, collections::HashSet};
use syn::Generics;

// CAUTION: This is all wildly unstable and relies on the compiler maintaining
// a certain order between proc macro expansions. So this could break any
// minute. Better have a robust CI.
thread_local! {
    static CALLS: RefCell<Vec<Call>> = Default::default();
}

struct Call {
    name: String,
    generics: String,
}

pub(crate) fn add_call(name: &Ident, generics: &Generics) {
    // Map everything to a string here. Compiler panics horribly if we hand out
    // the actual idents and generics.
    let call = Call {
        name: name.to_string(),
        generics: generics.to_token_stream().to_string(),
    };
    CALLS.with(|c| c.borrow_mut().push(call));
}

pub(crate) fn visitor(_input: TokenStream) -> TokenStream {
    // Flush the accumulated calls.
    let calls = CALLS.with(|c| std::mem::replace(&mut *c.borrow_mut(), Default::default()));

    // Determine a lifetime for the visitor.
    let lt: syn::Lifetime = syn::parse_str("'a").unwrap();

    // Generate some documentation.
    let mut doc = format!(
        "A visitor.\n\n\
        Use the `accept()` function to start visiting nodes. For example:\n\n\
        ```ignore\n\
        struct MagicVisitor;\n\n\
        impl Visitor for MagicVisitor {{\n\
        }}\n\n\
        node.accept(&mut MagicVisitor);\n\
        ```\n\n\
        "
    );
    doc.push_str("Implements the visitor pattern over the following nodes:\n\n");
    for call in &calls {
        doc.push_str(&format!("- `{}`\n", call.name));
    }

    // Generate the `visit_*` calls.
    let mut emitted = HashSet::new();
    let mut pre_calls = vec![];
    let mut post_calls = vec![];
    for call in calls {
        // Avoid duplicates.
        if !emitted.insert(call.name.clone()) {
            continue;
        }

        // Convert the names back to identifiers.
        let pre_visit_fn = format_ident!("pre_visit_{}", call.name.to_snake_case());
        let post_visit_fn = format_ident!("post_visit_{}", call.name.to_snake_case());
        let name = format_ident!("{}", call.name);

        // Parse the generics again and add appropriate lifetime bounds.
        let generics: syn::Generics = syn::parse_str(&call.generics).unwrap();
        let mut impl_generics = generics.clone();
        for ltdef in impl_generics.lifetimes_mut() {
            ltdef.bounds.push(lt.clone());
        }

        // Generate some documentation.
        let pre_doc = format!(
            "Called for every `{}` node before visiting its children.\n\n\
            Return `false` from this function to not visit the node's children.",
            name
        );
        let post_doc = format!(
            "Called for every `{}` node after visiting its children.",
            name
        );

        // Render the corresponding call.
        pre_calls.push(quote! {
            #[doc = #pre_doc]
            fn #pre_visit_fn (&mut self, node: &#lt #name #generics) -> bool {
                true
            }
        });
        post_calls.push(quote! {
            #[doc = #post_doc]
            fn #post_visit_fn (&mut self, node: &#lt #name #generics) {
            }
        });
    }

    let output = quote! {
        #[doc = #doc]
        pub trait Visitor<#lt> {
            #(#pre_calls)*
            #(#post_calls)*
        }
    };
    output.into()
}

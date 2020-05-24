// Copyright (c) 2016-2020 Fabian Schuiki

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
    ty: String,
    generics: String,
}

pub(crate) fn add_call(name: &Ident, ty: &Ident, generics: &Generics) {
    // Map everything to a string here. Compiler panics horribly if we hand out
    // the actual idents and generics.
    let call = Call {
        name: name.to_string(),
        ty: ty.to_string(),
        generics: generics.to_token_stream().to_string(),
    };
    CALLS.with(|c| c.borrow_mut().push(call));
}

pub(crate) fn visitor(_input: TokenStream) -> TokenStream {
    // Flush the accumulated calls.
    let calls = CALLS.with(|c| std::mem::take(&mut *c.borrow_mut()));

    // Determine a lifetime for the visitor which does not collide.
    let mut existing = HashSet::new();
    for call in &calls {
        let generics: syn::Generics = syn::parse_str(&call.generics).unwrap();
        existing.extend(generics.lifetimes().map(|l| l.lifetime.to_string()));
    }
    let lt = crate::pick_lifetime(&existing);
    let lt: syn::Lifetime = syn::parse_str(&lt).unwrap();

    // Generate the `visit_*` calls.
    let calls = calls.into_iter().map(|call| {
        let Call { name, ty, generics } = call;

        // Convert the names back to identifiers.
        let name = format_ident!("{}", name);
        let ty = format_ident!("{}", ty);

        // Parse the generics again and add appropriate lifetime bounds.
        let generics: syn::Generics = syn::parse_str(&generics).unwrap();
        let mut impl_generics = generics.clone();
        for ltdef in impl_generics.lifetimes_mut() {
            ltdef.bounds.push(lt.clone());
        }

        // Render the corresponding call.
        quote! {
            fn #name #impl_generics (&mut self, node: &#lt #ty #generics) {
                node.accept(self);
            }
        }
    });

    let output = quote! {
        pub trait Visitor<#lt> {
            #(#calls)*
        }
    };
    output.into()
}

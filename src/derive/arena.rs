// Copyright (c) 2016-2021 Fabian Schuiki

use heck::SnakeCase;
use proc_macro::TokenStream;
use proc_macro2::Ident;
use quote::{format_ident, quote, ToTokens};
use std::{cell::RefCell, collections::BTreeMap};
use syn::{Generics, Item};

// CAUTION: This is all wildly unstable and relies on the compiler maintaining
// a certain order between proc macro expansions. So this could break any
// minute. Better have a robust CI.
thread_local! {
    static TYPES: RefCell<Vec<Type>> = Default::default();
}

struct Type {
    name: String,
    generics: String,
}

/// Add an item to the collection of arena types.
pub(crate) fn add_node(name: &Ident, generics: &Generics) {
    // Map everything to a string here. Compiler panics horribly if we hand out
    // the actual idents and generics.
    let node = Type {
        name: name.to_string(),
        generics: generics.to_token_stream().to_string(),
    };
    TYPES.with(|c| c.borrow_mut().push(node));
}

/// Mark an item as to be allocated into an arena.
pub(crate) fn mark_arena(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as Item);
    let (name, generics) = match &input {
        Item::Enum(item) => (&item.ident, &item.generics),
        Item::Struct(item) => (&item.ident, &item.generics),
        Item::Type(item) => (&item.ident, &item.generics),
        _ => panic!("unsupported item for arena allocation"),
    };
    add_node(&name, &generics);
    let output = quote! {
        #input
    };
    output.into()
}

pub(crate) fn derive_arena(_args: TokenStream) -> TokenStream {
    // Flush the accumulated types.
    let types = TYPES.with(|c| std::mem::replace(&mut *c.borrow_mut(), Default::default()));

    // Convert the name back to identifiers and re-parse the generics.
    let types: Vec<(syn::Ident, syn::Generics)> = types
        .iter()
        .map(|ty| {
            (
                format_ident!("{}", ty.name),
                syn::parse_str(&ty.generics).unwrap(),
            )
        })
        .collect();

    // Determine the generics for the arena.
    let mut ltset = BTreeMap::new();
    for (_, generics) in &types {
        for ltdef in generics.lifetimes() {
            ltset.insert(ltdef.lifetime.ident.to_string(), ltdef.clone());
        }
    }
    // println!("Arena lifetimes: {:?}", ltset);

    // Introduce a lifetime for the self-reference in Alloc.
    let arena_ltdef: syn::LifetimeDef = syn::parse_str("'arena").unwrap();
    assert!(
        !ltset.contains_key(&arena_ltdef.lifetime.ident.to_string()),
        "'arena lifetime is reserved"
    );
    let arena_lt = arena_ltdef.lifetime.clone();

    // Assemble the arena generics.
    let mut arena_generics = syn::Generics::default();
    for (_, v) in ltset {
        arena_generics.params.push(syn::GenericParam::Lifetime(v));
    }
    // println!(
    //     "Arena generics: {}",
    //     arena_generics.to_token_stream().to_string()
    // );

    // Decide on a name for the arena.
    let arena_name = format_ident!("Arena");

    // Generate the various bits and pieces.
    let mut fields = vec![];
    let mut allocs = vec![];

    for (name, generics) in types {
        // Assemble the generics for the alloc implementation.
        let mut alloc_generics = generics.clone();
        let whc = alloc_generics.make_where_clause();
        for ltdef in generics.lifetimes() {
            whc.predicates.push(
                syn::PredicateLifetime {
                    lifetime: ltdef.lifetime.clone(),
                    colon_token: Default::default(),
                    bounds: Some(arena_lt.clone()).into_iter().collect(),
                }
                .into(),
            );
        }
        alloc_generics
            .params
            .insert(0, syn::GenericParam::Lifetime(arena_ltdef.clone()));

        // Render the corresponding field.
        let field_name = format_ident!("{}_arena", name.to_string().to_snake_case());
        fields.push(quote! {
            #field_name: moore_common::arenas::TypedArena<#name #generics>
        });

        // Render the corresponding alloc function.
        let (alloc_generics, _, whc) = alloc_generics.split_for_impl();
        allocs.push(quote! {
            impl #alloc_generics
                moore_common::arenas::Alloc<#arena_lt, #arena_lt, #name #generics>
                for #arena_name #arena_generics #whc
            {
                fn alloc(&#arena_lt self, value: #name #generics) -> &#arena_lt mut #name #generics {
                    self.#field_name.alloc(value)
                }
            }
        });
    }

    // Render the struct and alloc impls.
    let output = quote! {
        /// An arena.
        #[derive(Default)]
        pub struct #arena_name #arena_generics {
            #(#fields,)*
        }

        #(#allocs)*
    };
    // println!("{}", output);
    output.into()
}

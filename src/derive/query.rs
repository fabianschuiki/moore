// Copyright (c) 2016-2020 Fabian Schuiki

use heck::CamelCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote, quote_spanned, ToTokens};
use std::cell::RefCell;
use syn::{
    parse::{Parse, ParseStream},
    spanned::Spanned,
    Item,
};

// CAUTION: This is all wildly unstable and relies on the compiler maintaining
// a certain order between proc macro expansions. So this could break any
// minute. Better have a robust CI.
thread_local! {
    static QUERIES: RefCell<Vec<String>> = Default::default();
}

pub(crate) fn mark_query(_args: TokenStream, input: TokenStream) -> TokenStream {
    // Parse the input.
    let input = syn::parse_macro_input!(input as syn::ItemFn);

    // Map everything to a string here. Compiler panics horribly if we hand out
    // the actual idents and generics.
    QUERIES.with(|c| c.borrow_mut().push(input.to_token_stream().to_string()));

    // Produce some output.
    let output = quote! { #input };
    output.into()
}

pub(crate) fn derive_query_db(input: TokenStream) -> TokenStream {
    let mut output = proc_macro2::TokenStream::new();

    // Flush the accumulated queries.
    let queries = QUERIES.with(|c| std::mem::replace(&mut *c.borrow_mut(), Default::default()));
    println!("Queries: {:#?}", queries);

    // Process the queries.
    let mut funcs = vec![];
    for raw_query in &queries {
        let query: syn::ItemFn = syn::parse_str(raw_query).unwrap();
        let name = query.sig.ident.clone();
        let generics = query.sig.generics.clone();
        let args = query.sig.inputs.iter().skip(1);
        let result = query.sig.output.clone();
        let doc_attrs = query.attrs.iter().filter(|a| a.path.is_ident("doc"));
        println!("Generating query {}:", name);

        funcs.push(quote! {
            #(#doc_attrs)*
            fn #name #generics (&self, #(#args),*) #result {
                unimplemented!();
            }
        });
    }

    output.extend(quote! {
        pub trait QueryDatabase {
            #(#funcs)*
        }
    });

    // // Parse the input.
    // let input = syn::parse_macro_input!(input as syn::ItemFn);
    // // let func = match &input {
    // //     Item::Fn(func) => func,
    // //     _ => {
    // //         output.extend(quote_spanned! {
    // //             input.span() => compile_error!("expected fn");
    // //         });
    // //         return output.into();
    // //     }
    // // };

    // // Extract the name of the query.
    // let query_sig = &input.sig;
    // let query_name = &query_sig.ident;
    // let query_inputs = &query_sig.inputs;
    // let query_output = &query_sig.output;

    // println!("Query `{}`:", query_name);
    // println!(" - Inputs: {:?}", query_inputs);
    // println!(" - Output: {:?}", query_output);

    // // Generate the implementation trait for the query.
    // let trait_name = format_ident!("{}QueryImpl", query_name.to_string().to_camel_case());
    // output.extend(quote! {
    //     pub trait #trait_name {
    //         fn #query_name();
    //     }
    // });

    // Produce some output.
    println!("{}", output);
    output.into()
}

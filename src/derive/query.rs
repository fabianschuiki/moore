// Copyright (c) 2016-2020 Fabian Schuiki

use heck::CamelCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote, ToTokens};
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashSet},
};
use syn::visit::Visit;

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
    let note = format!("call query via database: cx.{}(...)", input.sig.ident);
    let output = quote! {
        #[deprecated(note = #note)]
        #input
    };
    output.into()
}

pub(crate) fn derive_query_db(input: TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut output = proc_macro2::TokenStream::new();

    // Flush the accumulated queries.
    let queries = QUERIES.with(|c| std::mem::replace(&mut *c.borrow_mut(), Default::default()));

    // Make a set of conflicting argument names.
    let reserved: HashSet<_> = ["query_key", "query_storage", "query_tag", "query_result"]
        .iter()
        .copied()
        .collect();

    // Collect all query lifetimes.
    let mut ltset = BTreeSet::new();

    // Process the queries.
    let mut funcs = vec![];
    let mut caches = vec![];
    let mut tags = vec![];
    let mut tag_debugs = vec![];
    let mut keys = vec![];

    for raw_query in &queries {
        // Parse the fn.
        let query: syn::ItemFn = syn::parse_str(raw_query).unwrap();

        // Disect a few things.
        let name = query.sig.ident.clone();
        let mut generics = query.sig.generics.clone();
        let args = query.sig.inputs.iter().skip(1);
        let result = match query.sig.output {
            syn::ReturnType::Type(_, ty) => ty.as_ref().clone(),
            _ => panic!("query {} has no return type", name),
        };

        // Filter out the doc comments such that we can apply them to the trait
        // fn as well.
        let doc_attrs = query.attrs.iter().filter(|a| a.path.is_ident("doc"));

        // Determine the argument list of the query.
        let arg_pats = args.clone().map(|arg| match arg {
            syn::FnArg::Typed(pat) => pat,
            _ => unreachable!("there should be no self args left at this point"),
        });
        let arg_names: Vec<_> = arg_pats
            .clone()
            .enumerate()
            .map(|(i, pat)| match pat.pat.as_ref() {
                syn::Pat::Ident(id) if !reserved.contains(id.ident.to_string().as_str()) => {
                    id.ident.clone()
                }
                _ => format_ident!("arg{}", i),
            })
            .collect();
        let arg_types: Vec<_> = arg_pats
            .clone()
            .map(|pat| pat.ty.as_ref().clone())
            .collect();

        // Collect lifetimes and strip them from the generics.
        let original_generics = generics.clone();
        for param in std::mem::replace(&mut generics.params, Default::default()) {
            match param {
                syn::GenericParam::Lifetime(ltdef) => {
                    ltset.insert(ltdef.lifetime);
                }
                _ => generics.params.push(param),
            }
        }

        // Determine the generics that go into the key.
        struct KeyGenerics(HashSet<String>);
        impl Visit<'_> for KeyGenerics {
            fn visit_lifetime(&mut self, node: &syn::Lifetime) {
                self.0.insert(node.to_string());
                syn::visit::visit_lifetime(self, node);
            }

            fn visit_type(&mut self, node: &syn::Type) {
                match node {
                    syn::Type::Path(x) => {
                        if let Some(x) = x.path.get_ident() {
                            self.0.insert(x.to_string());
                        }
                    }
                    _ => (),
                }
                syn::visit::visit_type(self, node);
            }
        }

        let mut key_generics_set = KeyGenerics(Default::default());
        for arg_type in &arg_types {
            key_generics_set.visit_type(&arg_type);
        }
        // println!("Key generics of {}: {:?}", name, key_generics_set.0);

        let mut key_generics = syn::Generics {
            lt_token: original_generics.lt_token,
            params: Default::default(),
            gt_token: original_generics.gt_token,
            where_clause: None,
        };
        for param in original_generics.params.iter() {
            let keep = match param {
                syn::GenericParam::Type(x) => key_generics_set.0.contains(&x.ident.to_string()),
                syn::GenericParam::Lifetime(x) => {
                    key_generics_set.0.contains(&x.lifetime.to_string())
                }
                syn::GenericParam::Const(x) => key_generics_set.0.contains(&x.ident.to_string()),
            };
            if keep {
                key_generics.params.push(param.clone());
            }
        }
        // println!("Key generics: {}", quote! { #key_generics });

        // Render the key type that we use to look up things in the database.
        let key_name = format_ident!("{}QueryKey", name.to_string().to_camel_case());
        let key_indices = (0..arg_types.len()).map(syn::Index::from);
        let doc = format!("The arguments passed to the `{}` query.", name);
        keys.push(quote! {
            #[doc = #doc]
            #[derive(Clone, PartialEq, Eq, Hash)]
            pub struct #key_name #key_generics (#(pub #arg_types),*);

            impl #key_generics std::fmt::Debug for #key_name #key_generics {
                fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                    f.debug_tuple("")#(.field(&self.#key_indices))*.finish()
                }
            }
        });

        // Determine the cache field name.
        let cache_name = format_ident!("cached_{}", name);

        // Render a query tag that can be pushed onto the query stack to break
        // cycles.
        let tag_name = format_ident!("{}", name.to_string().to_camel_case());
        let doc = format!("The `{}` query.", name);
        tags.push(quote! {
            #[doc = #doc]
            #tag_name (#key_name #key_generics),
        });
        tag_debugs.push(quote! {
            QueryTag::#tag_name (x) => write!(f, "{}{:?}", stringify!(#name), x),
        });

        // Render the query for the database trait.
        funcs.push(quote! {
            #(#doc_attrs)*
            fn #name #generics (&self, #(#arg_names: #arg_types),*) -> #result {
                let query_storage = self.storage();
                let query_key = #key_name(#(Clone::clone(&#arg_names)),*);
                let query_tag = QueryTag::#tag_name(query_key.clone());
                self.before_query(&query_tag);

                // Check if we already have a result for this query.
                if let Some(result) = query_storage.#cache_name.borrow().get(&query_key) {
                    trace!("Serving {}{:?} from cache", stringify!(#name), query_key);
                    return Clone::clone(&result);
                }
                trace!("Executing {}{:?}", stringify!(#name), query_key);

                // Push the query onto the stack, checking if it is already in
                // flight.
                query_storage.stack.borrow_mut().push(query_tag.clone());
                if !query_storage.inflight.borrow_mut().insert(query_tag.clone()) {
                    self.handle_cycle();
                    // The above never returns.
                }

                // Execute the query.
                #[allow(deprecated)]
                let query_result = #name(self.context(), #(#arg_names),*);
                query_storage.#cache_name.borrow_mut().insert(query_key, Clone::clone(&query_result));

                // Pop the query from the stack.
                query_storage.inflight.borrow_mut().remove(&query_tag);
                query_storage.stack.borrow_mut().pop();
                self.after_query(&query_tag);
                query_result
            }
        });

        // Render the cache field for the storage struct.
        let doc = format!("Cached results of the `{}` query.", name);
        caches.push(quote! {
            #[doc = #doc]
            pub #cache_name: RefCell<HashMap<#key_name #key_generics, #result>>,
        });
    }

    // Extract query lifetimes.
    let lts = if ltset.is_empty() {
        quote! {}
    } else {
        let lts = ltset.iter();
        quote! { <#(#lts),*> }
    };

    // Generate the query database trait.
    output.extend(quote! {
        #input
        pub trait QueryDatabase #lts {
            /// The type passed as first argument to compiler query
            /// implementations.
            type Context: crate::Context #lts;

            /// Get the context that is passed to compiler query
            /// implementations.
            fn context(&self) -> &Self::Context;

            /// Get the query caches and runtime data.
            fn storage(&self) -> &QueryStorage #lts;

            /// Called when a query cycle is detected.
            fn handle_cycle(&self) -> ! {
                error!("Query cycle detected:");
                for x in self.storage().stack.borrow().iter() {
                    error!(" - {:?}", x);
                }
                panic!("query cycle detected");
            }

            /// Called before a query is executed.
            fn before_query(&self, tag: &QueryTag #lts) {}

            /// Called after a query is executed.
            fn after_query(&self, tag: &QueryTag #lts) {}

            #(#funcs)*
        }
    });

    // Generate the query storage struct.
    output.extend(quote! {
        /// A collection of query caches and runtime data for a `QueryDatabase`.
        #[derive(Default)]
        pub struct QueryStorage #lts {
            /// A stack of the currently-executing queries.
            pub stack: RefCell<Vec<QueryTag #lts>>,
            /// A set of the currently-executing queries.
            pub inflight: RefCell<HashSet<QueryTag #lts>>,

            #(#caches)*
        }
    });

    // Generate the query tag enum.
    output.extend(quote! {
        /// A tag identifying any of the queries in `QueryDatabase`.
        #[derive(Clone, Hash, Eq, PartialEq)]
        pub enum QueryTag #lts {
            #(#tags)*
        }

        impl #lts std::fmt::Debug for QueryTag #lts {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    #(#tag_debugs)*
                }
            }
        }
    });

    // Generate the query keys.
    output.extend(quote! {
        #(#keys)*
    });

    // Produce some output.
    // println!("{}", output);
    output.into()
}

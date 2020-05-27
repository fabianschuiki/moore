// Copyright (c) 2016-2020 Fabian Schuiki

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::DeriveInput;

pub(crate) fn node_data(input: TokenStream) -> TokenStream {
    // Parse the input.
    let input = syn::parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let generics = &input.generics;

    // Generate the match that visits the relevant fields of the input.
    let mut arms = MatchArms::default();

    match &input.data {
        syn::Data::Struct(instruct) => {
            visit_fields(
                &input.attrs,
                &input.attrs,
                &instruct.fields,
                quote! { #name },
                &mut arms,
            );
        }
        syn::Data::Enum(inenum) => {
            for variant in &inenum.variants {
                let variant_name = &variant.ident;
                visit_fields(
                    &input.attrs,
                    &variant.attrs,
                    &variant.fields,
                    quote! { #name::#variant_name },
                    &mut arms,
                );
            }
        }
        _ => panic!("unsupported item for AnyNodeData"),
    };

    // Apply default match arms for attributes defined on the entire struct or
    // enum.
    if let Some(fmt) = get_indefinite(&input.attrs) {
        arms.indefinite.push(quote! {
            _ => write!(fmt, #fmt),
        });
    }
    if let Some(fmt) = get_definite(&input.attrs) {
        arms.definite.push(quote! {
            _ => write!(fmt, #fmt),
        });
    }
    arms.definite.push(quote! {
        _ => {
            self.fmt_indefinite(fmt)?;
            if let Some(name) = self.get_name() {
                write!(fmt, " `{}`", name)?
            }
            Ok(())
        },
    });
    arms.name.push(quote! {
        _ => None,
    });

    if arms.indefinite.is_empty() {
        panic!(
            "`AnyNodeData` requires at least a `#[indefinite(...)]` attribute on `{}`",
            name
        );
    }

    assert!(!arms.name.is_empty());
    assert!(!arms.indefinite.is_empty());
    assert!(!arms.definite.is_empty());

    // Generate the implementation of the `AnyNodeData` trait.
    let MatchArms {
        name: arms_name,
        indefinite: arms_indefinite,
        definite: arms_definite,
    } = arms;
    let output = quote! {
        impl #generics AnyNodeData for #name #generics {
            fn get_name(&self) -> Option<Spanned<Name>> {
                match self {
                    #(#arms_name)*
                }
            }

            fn fmt_indefinite(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    #(#arms_indefinite)*
                }
            }

            fn fmt_definite(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    #(#arms_definite)*
                }
            }
        }
    };
    // println!("{}", output);
    output.into()
}

/// Check if a `#[name]` attribute is present.
fn has_name(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.path.is_ident("name"))
}

/// Check if a `#[forward]` attribute is present.
fn has_forward(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.path.is_ident("forward"))
}

/// Check if a `#[indefinite(...)]` attribute is present.
fn get_indefinite(attrs: &[syn::Attribute]) -> Option<proc_macro2::TokenStream> {
    for attr in attrs {
        if !attr.path.is_ident("indefinite") {
            continue;
        }
        return Some(attr.parse_args().unwrap());
    }
    None
}

/// Check if a `#[definite(...)]` attribute is present.
fn get_definite(attrs: &[syn::Attribute]) -> Option<proc_macro2::TokenStream> {
    for attr in attrs {
        if !attr.path.is_ident("definite") {
            continue;
        }
        return Some(attr.parse_args().unwrap());
    }
    None
}

#[derive(Default)]
struct MatchArms {
    name: Vec<proc_macro2::TokenStream>,
    indefinite: Vec<proc_macro2::TokenStream>,
    definite: Vec<proc_macro2::TokenStream>,
}

/// Generate the code to visit fields in a struct-like item.
#[allow(unused_assignments)]
fn visit_fields(
    global_attrs: &[syn::Attribute],
    attrs: &[syn::Attribute],
    fields: &syn::Fields,
    pat_prefix: proc_macro2::TokenStream,
    arms: &mut MatchArms,
) {
    // Generate a destructuring pattern that assigns predictable names to all
    // fields.
    let mut mapped_fields = vec![];
    let pat = match fields {
        syn::Fields::Named(ref fields) => {
            let mut mapping = vec![];
            for (i, field) in fields.named.iter().enumerate() {
                let field_name = &field.ident;
                let name = format_ident!("arg{}", i);
                mapped_fields.push((name.clone(), field));
                mapping.push(quote! {
                    #field_name: #name
                });
            }
            quote! { {#(#mapping),*} }
        }
        syn::Fields::Unnamed(ref fields) => {
            let mut mapping = vec![];
            for (i, field) in fields.unnamed.iter().enumerate() {
                let name = format_ident!("arg{}", i);
                mapped_fields.push((name.clone(), field));
                mapping.push(name);
            }
            quote! { (#(#mapping),*) }
        }
        syn::Fields::Unit => {
            quote! {}
        }
    };

    // Keep track of what we have emitted, for later forwarding.
    let mut had_name = false;
    let mut had_indefinite = false;
    let mut had_definite = false;

    // Check if a field was marked as `name`.
    for (name, field) in &mapped_fields {
        if has_name(&field.attrs) {
            had_name = true;
            arms.name.push(quote! {
                #pat_prefix #pat => #name.clone().into(),
            });
            break;
        }
    }

    // Check if a field was marked as `forward`, in which case we fill in the
    // missing details based on that field.
    for (name, field) in &mapped_fields {
        if has_forward(&field.attrs) {
            if !had_name {
                had_name = true;
                arms.name.push(quote! {
                    #pat_prefix #pat => #name.get_name(),
                });
            }
            if !had_indefinite {
                had_indefinite = true;
                arms.indefinite.push(quote! {
                    #pat_prefix #pat => #name.fmt_indefinite(fmt),
                });
            }
            if !had_definite {
                had_definite = true;
                arms.definite.push(quote! {
                    #pat_prefix #pat => #name.fmt_definite(fmt),
                });
            }
            break;
        }
    }

    // Apply any `forward` attribute on the entire struct.
    if (has_forward(attrs) || has_forward(global_attrs)) && !had_name && !mapped_fields.is_empty() {
        let (name, _field) = &mapped_fields[0];
        if !had_name {
            had_name = true;
            arms.name.push(quote! {
                #pat_prefix #pat => #name.get_name(),
            });
        }
    }
    if (has_forward(attrs) || has_forward(global_attrs)) && !had_indefinite {
        if mapped_fields.is_empty() {
            panic!(
                "`#[forward]` on `{0}` with no fields (consider explicit `#[indefinite]` on `{0}`)",
                pat_prefix
            );
        }
        let (name, _field) = &mapped_fields[0];
        had_indefinite = true;
        arms.indefinite.push(quote! {
            #pat_prefix #pat => #name.fmt_indefinite(fmt),
        });
    }
    if (has_forward(attrs) || has_forward(global_attrs))
        && !had_definite
        && !mapped_fields.is_empty()
    {
        let (name, _field) = &mapped_fields[0];
        had_definite = true;
        arms.definite.push(quote! {
            #pat_prefix #pat => #name.fmt_definite(fmt),
        });
    }

    // Apply any `indefinite` or `definite` attribute on the entire struct.
    if let Some(fmt) = get_indefinite(attrs).or(get_indefinite(global_attrs)) {
        had_indefinite = true;
        arms.indefinite.push(quote! {
            #pat_prefix #pat => write!(fmt, #fmt),
        });
    }
    if let Some(fmt) = get_definite(attrs).or(get_definite(global_attrs)) {
        had_definite = true;
        arms.definite.push(quote! {
            #pat_prefix #pat => write!(fmt, #fmt),
        });
    }
}

// Copyright (C) 2018-2019 Stephane Raux. Distributed under the MIT license.

//! Procedural macro to derive `IntoEnumIterator` for field-less enums.
//!
//! See crate [enum-iterator](https://docs.rs/enum-iterator) for details.

#![recursion_limit = "128"]
#![deny(warnings)]

extern crate proc_macro;

use itertools::izip;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use std::fmt::{Display, self};
use std::iter;
use syn::{Ident, DeriveInput, Token, punctuated::Punctuated};

/// Derives `IntoEnumIterator` for field-less enums.
#[proc_macro_derive(IntoEnumIterator)]
pub fn into_enum_iterator(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input).unwrap_or_else(|e| e.to_compile_error()).into()
}

fn derive(input: proc_macro::TokenStream) -> Result<TokenStream, syn::Error> {
    let ast = syn::parse::<DeriveInput>(input)?;
    if !ast.generics.params.is_empty() {
        return Err(Error::GenericsUnsupported.with_tokens(&ast.generics));
    }
    let ty = &ast.ident;
    let vis = &ast.vis;
    let ty_doc = format!("Iterator over the variants of {}", ty);
    let iter_ty = Ident::new(&(ty.to_string() + "EnumIterator"), Span::call_site());
    let variants = match &ast.data {
        syn::Data::Enum(e) => &e.variants,
        _ => return Err(Error::ExpectedEnum.with_tokens(&ast)),
    };
    let iter_variants = variants.iter()
        .map(|v| {
            let id = &v.ident;
            match v.fields {
                syn::Fields::Unit => quote!(#id),
                syn::Fields::Unnamed(syn::FieldsUnnamed { ref unnamed, .. }) => {
                    let field_iters = unnamed.iter().map(|field| {
                        let field_ty = &field.ty;
                        quote!((<#field_ty as ::enum_iterator::IntoEnumIterator>::Iterator, Option<<<#field_ty as ::enum_iterator::IntoEnumIterator>::Iterator as ::core::iter::Iterator>::Item>))
                    });
                    quote!(#id(#(#field_iters,)*))
                }
                syn::Fields::Named(syn::FieldsNamed { ref named, .. }) => {
                    let field_iters = named.iter().map(|field| {
                        let field_name = &field.ident.as_ref().expect("named field should have a name");
                        let field_ty = &field.ty;
                        quote!(#field_name: (<#field_ty as ::enum_iterator::IntoEnumIterator>::Iterator, Option<<<#field_ty as ::enum_iterator::IntoEnumIterator>::Iterator as ::core::iter::Iterator>::Item>))
                    });
                    quote!(#id { #(#field_iters,)* })
                }
            }
        });
    let mut constructors = variants.iter()
        .map(|v| {
            let id = &v.ident;
            match v.fields {
                syn::Fields::Unit => quote!(#iter_ty::#id),
                syn::Fields::Unnamed(syn::FieldsUnnamed { ref unnamed, .. }) => {
                    let field_iters = unnamed.iter().map(|field| {
                        let field_ty = &field.ty;
                        quote!((<#field_ty as ::enum_iterator::IntoEnumIterator>::Iterator::__EnumIterStart, ::core::option::Option::None))
                    });
                    quote!(#iter_ty::#id(#(#field_iters,)*))
                }
                syn::Fields::Named(syn::FieldsNamed { ref named, .. }) => {
                    let field_iters = named.iter().map(|field| {
                        let field_name = &field.ident.as_ref().expect("named field should have a name");
                        let field_ty = &field.ty;
                        quote!(#field_name: (<#field_ty as ::enum_iterator::IntoEnumIterator>::Iterator::__EnumIterStart, ::core::option::Option::None))
                    });
                    quote!(#iter_ty::#id { #(#field_iters,)* })
                }
            }
        });
    let first_constructor = constructors.next().unwrap_or(quote!(#iter_ty::__EnumIterDone));
    let arms = variants.iter().zip(constructors.chain(iter::once(quote!(#iter_ty::__EnumIterDone))))
        .map(|(v, next_constructor)| {
            let id = &v.ident;
            match v.fields {
                syn::Fields::Unit => quote! {
                    #iter_ty::#id => {
                        *self = #next_constructor;
                        break ::core::option::Option::Some(#ty::#id)
                    }
                },
                syn::Fields::Unnamed(syn::FieldsUnnamed { ref unnamed, .. }) => {
                    let (field_iters, field_caches, elt_defs, elts) = variant_iter(next_constructor, unnamed);
                    quote! {
                        #iter_ty::#id(#((#field_iters, #field_caches),)*) => {
                            #(#elt_defs)*
                            break ::core::option::Option::Some(#ty::#id(#(#elts,)*))
                        }
                    }
                }
                syn::Fields::Named(syn::FieldsNamed { ref named, .. }) => {
                    let field_names = named.iter().map(|field| field.ident.as_ref().expect("unnamed field in struct variant")).collect::<Vec<_>>();
                    let (field_iters, field_caches, elt_defs, elts) = variant_iter(next_constructor, named);
                    quote! {
                        #iter_ty::#id { #(#field_names: (#field_iters, #field_caches),)* } => {
                            #(#elt_defs)*
                            break ::core::option::Option::Some(#ty::#id { #(#field_names: #elts,)* })
                        }
                    }
                }
            }
        });
    let tokens = quote! {
        #[doc = #ty_doc]
        #[derive(Clone, Copy, Debug)]
        #vis enum #iter_ty {
            __EnumIterStart,
            #(#iter_variants,)*
            __EnumIterDone,
        }

        impl ::core::iter::Iterator for #iter_ty {
            type Item = #ty;

            fn next(&mut self) -> ::core::option::Option<Self::Item> {
                loop {
                    match self {
                        Self::__EnumIterStart => *self = #first_constructor,
                        #(#arms)*
                        Self::__EnumIterDone => break ::core::option::Option::None,
                    }
                }
            }

            /*
            fn size_hint(&self) -> (usize, ::core::option::Option<usize>) {
                //TODO use previous impl if fieldless enum
                (0, ::core::option::Option::Some(#nb_elts))
            }
            */
        }

        //TODO “uncomment” if fieldless enum
        //impl ::core::iter::ExactSizeIterator for #iter_ty {}
        impl ::core::iter::FusedIterator for #iter_ty {}

        impl ::enum_iterator::IntoEnumIterator for #ty {
            type Iterator = #iter_ty;

            //TODO
            //const VARIANT_COUNT: usize = #nb_variants;
            //const ELEMENT_COUNT: usize = #nb_elts;

            fn into_enum_iter() -> Self::Iterator {
                #iter_ty::__EnumIterStart
            }
        }
    };
    let tokens = quote! {
        const _: () = {
            #tokens
        };
    };
    Ok(tokens)
}

fn variant_iter(next_constructor: TokenStream, fields: &Punctuated<syn::Field, Token![,]>) -> (Vec<Ident>, Vec<Ident>, Vec<TokenStream>, Vec<Ident>) {
    let field_types = fields.iter().map(|field| &field.ty);
    let field_iters = (0..fields.len()).map(|idx| Ident::new(&format!("__iter{}", idx), Span::call_site())).collect::<Vec<_>>();
    let field_caches = (0..fields.len()).map(|idx| Ident::new(&format!("__cache{}", idx), Span::call_site())).collect::<Vec<_>>();
    let elts = (0..fields.len()).map(|idx| Ident::new(&format!("__elt{}", idx), Span::call_site())).collect::<Vec<_>>();
    let elt_defs = izip!(field_types, &field_iters, &field_caches, &elts).enumerate().map(|(idx, (field_ty, iter, cache, elt))| {
        let cache_lookup = if idx == fields.len() - 1 { quote!(#cache.take()) } else { quote!(#cache.as_ref()) };
        let cache_read = if idx == fields.len() - 1 { quote!(#elt) } else { quote!(#elt.clone()) };
        let cache_write = if idx == fields.len() - 1 { quote!(#elt) } else { quote!({
            #cache = ::core::option::Option::Some(#elt.clone());
            #elt
        }) };
        let handle_end = if idx == 0 {
            quote!({
                *self = #next_constructor;
                continue
            })
        } else {
            let prev_cache = &field_caches[idx - 1];
            let cache_writes = (idx + 1..fields.len()).map(|idx| {
                let cache = &field_caches[idx];
                let elt = &elts[idx];
                quote!(*#cache = ::core::option::Option::Some(#elt);)
            });
            quote!({
                *#prev_cache = ::core::option::Option::None;
                *#iter = <#field_ty as ::enum_iterator::IntoEnumIterator>::Iterator::__EnumIterStart;
                #(#cache_writes)*
                continue
            })
        };
        quote! {
            let #elt = match #cache_lookup {
                ::core::option::Option::Some(#elt) => #cache_read,
                ::core::option::Option::None => match #iter.next() {
                    ::core::option::Option::Some(#elt) => #cache_write,
                    ::core::option::Option::None => #handle_end,
                }
            };
        }
    }).collect();
    (field_iters, field_caches, elt_defs, elts)
}

#[derive(Debug)]
enum Error {
    ExpectedEnum,
    GenericsUnsupported,
}

impl Error {
    fn with_tokens<T: ToTokens>(self, tokens: T) -> syn::Error {
        syn::Error::new_spanned(tokens, self)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ExpectedEnum =>
                f.write_str("IntoEnumIterator can only be derived for enum types"),
            Error::GenericsUnsupported =>
                f.write_str("IntoEnumIterator cannot be derived for generic types"),
        }
    }
}

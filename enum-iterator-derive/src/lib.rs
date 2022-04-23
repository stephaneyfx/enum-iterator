// Copyright (C) 2018-2022 Stephane Raux. Distributed under the 0BSD license.

//! # Overview
//! - [📦 crates.io](https://crates.io/crates/enum-iterator-derive)
//! - [📖 Documentation](https://docs.rs/enum-iterator-derive)
//! - [⚖ 0BSD license](https://spdx.org/licenses/0BSD.html)
//!
//! Procedural macro to derive `IntoEnumIterator`.
//!
//! See crate [enum-iterator](https://docs.rs/enum-iterator) for details.
//!
//! # Contribute
//! All contributions shall be licensed under the [0BSD license](https://spdx.org/licenses/0BSD.html).

#![recursion_limit = "128"]
#![deny(warnings)]

extern crate proc_macro;

use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use std::{
    fmt::{self, Display},
    iter::DoubleEndedIterator,
};
use syn::{
    punctuated::Punctuated, token::Comma, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
    Ident, Member, Variant, Visibility,
};

/// Derives `IntoEnumIterator`.
#[proc_macro_derive(IntoEnumIterator)]
pub fn into_enum_iterator(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input)
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

fn derive(input: proc_macro::TokenStream) -> Result<TokenStream, syn::Error> {
    let ast = syn::parse::<DeriveInput>(input)?;
    if !ast.generics.params.is_empty() {
        return Err(Error::UnsupportedGenerics.with_tokens(&ast.generics));
    }
    let ty = &ast.ident;
    let vis = &ast.vis;
    match &ast.data {
        syn::Data::Struct(s) => derive_for_struct(vis, ty, &s.fields),
        syn::Data::Enum(e) => derive_for_enum(vis, ty, &e.variants),
        syn::Data::Union(_) => Err(Error::UnsupportedUnion.with_tokens(&ast)),
    }
}

fn derive_for_struct(
    vis: &Visibility,
    ty: &Ident,
    fields: &Fields,
) -> Result<TokenStream, syn::Error> {
    let ty_doc = format!("Iterator over values of type {ty}");
    let iter_ty = Ident::new(&format!("{ty}EnumIterator"), Span::call_site());
    let tuple_ty = tuple_type(fields);
    let pattern = tuple_pattern(fields.len());
    let assignments = field_assignments(fields);
    let tokens = quote! {
        #[doc = #ty_doc]
        #[derive(Clone)]
        #vis struct #iter_ty(<#tuple_ty as ::enum_iterator::IntoEnumIterator>::Iterator);

        impl ::core::iter::Iterator for #iter_ty {
            type Item = #ty;

            fn next(&mut self) -> ::core::option::Option<Self::Item> {
                let #pattern = self.0.next()?;
                Some(#ty {
                    #assignments
                })
            }
        }

        impl ::enum_iterator::IntoEnumIterator for #ty {
            type Iterator = #iter_ty;

            const ITEM_COUNT: usize = <#tuple_ty as ::enum_iterator::IntoEnumIterator>::ITEM_COUNT;

            fn into_enum_iter() -> Self::Iterator {
                #iter_ty(<#tuple_ty as ::enum_iterator::IntoEnumIterator>::into_enum_iter())
            }
        }
    };
    Ok(isolate_code(tokens))
}

fn derive_for_enum(
    vis: &Visibility,
    ty: &Ident,
    variants: &Punctuated<Variant, Comma>,
) -> Result<TokenStream, syn::Error> {
    let ty_doc = format!("Iterator over values of type {ty}");
    let iter_ty = Ident::new(&format!("{ty}EnumIterator"), Span::call_site());
    let iter_inner_ty = Ident::new(&format!("{ty}EnumIteratorInner"), Span::call_site());
    let iter_variants = build_iterator_variants(variants);
    let arms = build_arms(ty, &iter_inner_ty, variants);
    let lengths = build_length_expr(variants);
    let first = match variants.first() {
        Some(first) => init_variant(&iter_inner_ty, first),
        None => quote! { loop {} },
    };
    let tokens = quote! {
        #[derive(Clone)]
        enum #iter_inner_ty {
            #(#iter_variants,)*
        }

        #[doc = #ty_doc]
        #[derive(Clone)]
        #vis struct #iter_ty(#iter_inner_ty);

        impl ::core::iter::Iterator for #iter_ty {
            type Item = #ty;

            fn next(&mut self) -> ::core::option::Option<Self::Item> {
                loop {
                    match &mut self.0 {
                        #(#arms)*
                    }
                }
            }
        }

        impl ::enum_iterator::IntoEnumIterator for #ty {
            type Iterator = #iter_ty;

            const ITEM_COUNT: usize = 0 #(+ #lengths)*;

            fn into_enum_iter() -> Self::Iterator {
                #iter_ty(#first)
            }
        }
    };
    Ok(isolate_code(tokens))
}

fn build_length_expr(variants: &Punctuated<Variant, Comma>) -> Vec<TokenStream> {
    variants
        .iter()
        .map(|variant| match &variant.fields {
            Fields::Named(FieldsNamed { named: fields, .. })
            | Fields::Unnamed(FieldsUnnamed {
                unnamed: fields, ..
            }) => {
                let ty = tuple_type(fields);
                quote! {
                    <#ty as ::enum_iterator::IntoEnumIterator>::ITEM_COUNT
                }
            }
            Fields::Unit => quote! { 1 },
        })
        .collect()
}

fn build_iterator_variants(variants: &Punctuated<Variant, Comma>) -> Vec<TokenStream> {
    variants
        .iter()
        .map(|variant| {
            let id = &variant.ident;
            match &variant.fields {
                Fields::Named(FieldsNamed { named: fields, .. })
                | Fields::Unnamed(FieldsUnnamed {
                    unnamed: fields, ..
                }) => {
                    let ty = tuple_type(fields);
                    quote! {
                        #id(<#ty as ::enum_iterator::IntoEnumIterator>::Iterator)
                    }
                }
                Fields::Unit => quote! { #id },
            }
        })
        .chain(Some(quote! { __EnumIteratorEnd }))
        .collect()
}

fn tuple_type<'a, I>(fields: I) -> TokenStream
where
    I: IntoIterator<Item = &'a Field>,
    I::IntoIter: DoubleEndedIterator,
{
    fields
        .into_iter()
        .rev()
        .map(|field| &field.ty)
        .fold(quote! {}, |acc, ty| {
            quote! {
                (#ty, #acc)
            }
        })
}

fn init_variant(iter_inner_ty: &Ident, variant: &Variant) -> TokenStream {
    let id = &variant.ident;
    match &variant.fields {
        Fields::Named(FieldsNamed { named: fields, .. })
        | Fields::Unnamed(FieldsUnnamed {
            unnamed: fields, ..
        }) => {
            let ty = tuple_type(fields);
            quote! {
                #iter_inner_ty::#id(
                    <#ty as ::enum_iterator::IntoEnumIterator>::into_enum_iter(),
                )
            }
        }
        Fields::Unit => quote! { #iter_inner_ty::#id },
    }
}

fn tuple_pattern(len: usize) -> TokenStream {
    (0..len).rev().fold(quote! {}, |acc, i| {
        let id = Ident::new(&format!("x{i}"), Span::call_site());
        quote! { (#id, #acc) }
    })
}

fn field_assignments<'a, I>(fields: I) -> TokenStream
where
    I: IntoIterator<Item = &'a Field>,
{
    let assignments = fields.into_iter().enumerate().map(|(i, field)| {
        let field_id = field.ident.clone().map(Member::Named).unwrap_or_else(|| {
            Member::Unnamed(syn::Index {
                index: i.try_into().unwrap(),
                span: Span::call_site(),
            })
        });
        let value = Ident::new(&format!("x{i}"), Span::call_site());
        quote! { #field_id: #value }
    });
    quote! { #(#assignments,)* }
}

fn build_arms(
    ty: &Ident,
    iter_inner_ty: &Ident,
    variants: &Punctuated<Variant, Comma>,
) -> Vec<TokenStream> {
    let next_variants = variants
        .iter()
        .skip(1)
        .map(|variant| init_variant(iter_inner_ty, variant))
        .chain(Some(quote! { #iter_inner_ty::__EnumIteratorEnd }));
    variants
        .iter()
        .zip(next_variants)
        .map(|(variant, next)| {
            let id = &variant.ident;
            match &variant.fields {
                Fields::Named(FieldsNamed { named: fields, .. })
                | Fields::Unnamed(FieldsUnnamed {
                    unnamed: fields, ..
                }) => {
                    let pattern = tuple_pattern(fields.len());
                    let assignments = field_assignments(fields);
                    quote! {
                        #iter_inner_ty::#id(inner) => match ::core::iter::Iterator::next(inner) {
                            ::core::option::Option::Some(#pattern) => {
                                break ::core::option::Option::Some(#ty::#id {
                                    #assignments
                                })
                            }
                            ::core::option::Option::None => self.0 = #next,
                        }
                    }
                }
                Fields::Unit => quote! {
                    #iter_inner_ty::#id => {
                        self.0 = #next;
                        break ::core::option::Option::Some(#ty::#id);
                    }
                },
            }
        })
        .chain(Some(
            quote! { #iter_inner_ty::__EnumIteratorEnd => break None, },
        ))
        .collect()
}

fn isolate_code(code: TokenStream) -> TokenStream {
    quote! {
        const _: () = {
            #code
        };
    }
}

#[derive(Debug)]
enum Error {
    UnsupportedUnion,
    UnsupportedGenerics,
}

impl Error {
    fn with_tokens<T: ToTokens>(self, tokens: T) -> syn::Error {
        syn::Error::new_spanned(tokens, self)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::UnsupportedUnion => {
                f.write_str("IntoEnumIterator cannot be derived for union types")
            }
            Error::UnsupportedGenerics => {
                f.write_str("IntoEnumIterator cannot be derived for generic types")
            }
        }
    }
}

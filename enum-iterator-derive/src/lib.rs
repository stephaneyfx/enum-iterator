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
    collections::HashMap,
    fmt::{self, Display},
    iter::{self, once, repeat, DoubleEndedIterator},
};
use syn::{
    punctuated::Punctuated, token::Comma, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
    Generics, Ident, Member, Path, PathSegment, PredicateType, TraitBound, TraitBoundModifier,
    Type, TypeParamBound, Variant, Visibility, WhereClause, WherePredicate,
};

/// Derives `IntoEnumIterator`.
#[proc_macro_derive(IntoEnumIterator)]
pub fn into_enum_iterator(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input)
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

fn derive(input: proc_macro::TokenStream) -> Result<TokenStream, syn::Error> {
    derive_for_ast(syn::parse(input)?)
}

fn derive_for_ast(ast: DeriveInput) -> Result<TokenStream, syn::Error> {
    let ty = &ast.ident;
    let vis = &ast.vis;
    let generics = &ast.generics;
    match &ast.data {
        syn::Data::Struct(s) => derive_for_struct(vis, ty, generics, &s.fields),
        syn::Data::Enum(e) => derive_for_enum(vis, ty, generics, &e.variants),
        syn::Data::Union(_) => Err(Error::UnsupportedUnion.with_tokens(&ast)),
    }
}

fn derive_for_struct(
    vis: &Visibility,
    ty: &Ident,
    generics: &Generics,
    fields: &Fields,
) -> Result<TokenStream, syn::Error> {
    let ty_doc = format!("Iterator over values of type {ty}");
    let iter_ty = Ident::new(&format!("{ty}EnumIterator"), Span::call_site());
    let tuple_ty = tuple_type(fields);
    let pattern = tuple_pattern(fields.len());
    let assignments = field_assignments(fields);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let where_clause = if generics.params.is_empty() {
        where_clause.cloned()
    } else {
        let mut clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
            where_token: Default::default(),
            predicates: Default::default(),
        });
        clause.predicates.extend(
            trait_bounds(group_type_requirements(
                fields.iter().zip(tuple_type_requirements()),
            ))
            .map(WherePredicate::Type),
        );
        Some(clause)
    };
    let tokens = quote! {
        #[doc = #ty_doc]
        #vis struct #iter_ty #impl_generics(<#tuple_ty as ::enum_iterator::IntoEnumIterator>::Iterator) #where_clause;

        impl #impl_generics ::core::clone::Clone for #iter_ty #ty_generics #where_clause {
            fn clone(&self) -> Self {
                Self(::core::clone::Clone::clone(&self.0))
            }
        }

        impl #impl_generics ::core::iter::Iterator for #iter_ty #ty_generics #where_clause {
            type Item = #ty #ty_generics;

            fn next(&mut self) -> ::core::option::Option<Self::Item> {
                let #pattern = self.0.next()?;
                Some(#ty {
                    #assignments
                })
            }
        }

        impl #impl_generics ::enum_iterator::IntoEnumIterator for #ty #ty_generics #where_clause {
            type Iterator = #iter_ty #ty_generics;

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
    generics: &Generics,
    variants: &Punctuated<Variant, Comma>,
) -> Result<TokenStream, syn::Error> {
    let ty_doc = format!("Iterator over values of type {ty}");
    let iter_ty = Ident::new(&format!("{ty}EnumIterator"), Span::call_site());
    let iter_inner_ty = Ident::new(&format!("{ty}EnumIteratorInner"), Span::call_site());
    let iter_variants = build_iterator_variants(variants);
    let arms = build_arms(ty, &iter_inner_ty, variants);
    let lengths = build_length_operands(variants);
    let first = match variants.first() {
        Some(first) => init_variant(&iter_inner_ty, first),
        None => quote! { loop {} },
    };
    let iter_inner_ty_clone = impl_clone_arms_for_iter_inner_ty(&iter_inner_ty, variants);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let where_clause = if generics.params.is_empty() {
        where_clause.cloned()
    } else {
        let mut clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
            where_token: Default::default(),
            predicates: Default::default(),
        });
        clause.predicates.extend(
            trait_bounds(group_type_requirements(variants.iter().flat_map(
                |variant| variant.fields.iter().zip(tuple_type_requirements()),
            )))
            .map(WherePredicate::Type),
        );
        Some(clause)
    };
    let tokens = quote! {
        enum #iter_inner_ty #impl_generics #where_clause {
            #(#iter_variants,)*
        }

        impl #impl_generics ::core::clone::Clone for #iter_inner_ty #ty_generics #where_clause {
            fn clone(&self) -> Self {
                match self {
                    #iter_inner_ty_clone
                }
            }
        }

        #[doc = #ty_doc]
        #vis struct #iter_ty #impl_generics(#iter_inner_ty #ty_generics) #where_clause;

        impl #impl_generics ::core::clone::Clone for #iter_ty #ty_generics #where_clause {
            fn clone(&self) -> Self {
                Self(::core::clone::Clone::clone(&self.0))
            }
        }

        impl #impl_generics ::core::iter::Iterator for #iter_ty #ty_generics #where_clause {
            type Item = #ty #ty_generics;

            fn next(&mut self) -> ::core::option::Option<Self::Item> {
                loop {
                    match &mut self.0 {
                        #(#arms)*
                    }
                }
            }
        }

        impl #impl_generics ::enum_iterator::IntoEnumIterator for #ty #ty_generics #where_clause {
            type Iterator = #iter_ty #ty_generics;

            const ITEM_COUNT: usize = 0 #(+ #lengths)*;

            fn into_enum_iter() -> Self::Iterator {
                #iter_ty(#first)
            }
        }
    };
    Ok(isolate_code(tokens))
}

fn build_length_operands(variants: &Punctuated<Variant, Comma>) -> Vec<TokenStream> {
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
    fields
        .into_iter()
        .enumerate()
        .map(|(i, field)| {
            let field_id = field.ident.clone().map(Member::Named).unwrap_or_else(|| {
                Member::Unnamed(syn::Index {
                    index: i.try_into().unwrap(),
                    span: Span::call_site(),
                })
            });
            let value = Ident::new(&format!("x{i}"), Span::call_site());
            quote! { #field_id: #value, }
        })
        .collect()
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
            quote! { #iter_inner_ty::__EnumIteratorEnd => break ::core::option::Option::None, },
        ))
        .collect()
}

fn impl_clone_arms_for_iter_inner_ty(
    iter_inner_ty: &Ident,
    variants: &Punctuated<Variant, Comma>,
) -> TokenStream {
    variants
        .iter()
        .map(|variant| {
            let id = &variant.ident;
            match &variant.fields {
                Fields::Named(FieldsNamed { .. }) | Fields::Unnamed(FieldsUnnamed { .. }) => {
                    quote! {
                        #iter_inner_ty::#id(inner) => {
                            #iter_inner_ty::#id(::core::clone::Clone::clone(inner))
                        },
                    }
                }
                Fields::Unit => quote! { #iter_inner_ty::#id => #iter_inner_ty::#id, },
            }
        })
        .chain(Some(
            quote! { #iter_inner_ty::__EnumIteratorEnd => #iter_inner_ty::__EnumIteratorEnd, },
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

fn trait_bounds<I>(types: I) -> impl Iterator<Item = PredicateType>
where
    I: IntoIterator<Item = (Type, TypeRequirements)>,
{
    types
        .into_iter()
        .map(|(bounded_ty, requirements)| PredicateType {
            lifetimes: None,
            bounded_ty,
            colon_token: Default::default(),
            bounds: requirements
                .into_iter()
                .map(|req| match req {
                    TypeRequirement::Clone => clone_trait_path(),
                    TypeRequirement::IntoEnumIterator => trait_path(),
                })
                .map(trait_bound)
                .collect(),
        })
}

fn trait_bound(path: Path) -> TypeParamBound {
    TypeParamBound::Trait(TraitBound {
        paren_token: None,
        modifier: TraitBoundModifier::None,
        lifetimes: None,
        path,
    })
}

fn trait_path() -> Path {
    Path {
        leading_colon: Some(Default::default()),
        segments: [
            PathSegment::from(Ident::new("enum_iterator", Span::call_site())),
            Ident::new("IntoEnumIterator", Span::call_site()).into(),
        ]
        .into_iter()
        .collect(),
    }
}

fn clone_trait_path() -> Path {
    Path {
        leading_colon: Some(Default::default()),
        segments: [
            PathSegment::from(Ident::new("core", Span::call_site())),
            Ident::new("clone", Span::call_site()).into(),
            Ident::new("Clone", Span::call_site()).into(),
        ]
        .into_iter()
        .collect(),
    }
}

fn tuple_type_requirements() -> impl Iterator<Item = TypeRequirements> {
    once([TypeRequirement::IntoEnumIterator].into()).chain(repeat(
        [TypeRequirement::IntoEnumIterator, TypeRequirement::Clone].into(),
    ))
}

fn group_type_requirements<'a, I>(bounds: I) -> Vec<(Type, TypeRequirements)>
where
    I: IntoIterator<Item = (&'a Field, TypeRequirements)>,
{
    bounds
        .into_iter()
        .fold(
            (HashMap::<_, usize>::new(), Vec::new()),
            |(mut indexes, mut acc), (field, requirements)| {
                let i = *indexes.entry(field.ty.clone()).or_insert_with(|| {
                    acc.push((field.ty.clone(), TypeRequirements::new()));
                    acc.len() - 1
                });
                acc[i].1.extend(requirements);
                (indexes, acc)
            },
        )
        .1
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum TypeRequirement {
    IntoEnumIterator,
    Clone,
}

#[derive(Clone, Debug, Default, PartialEq)]
struct TypeRequirements(u8);

impl TypeRequirements {
    const INTO_ENUM_ITERATOR: u8 = 0x1;
    const CLONE: u8 = 0x2;

    fn new() -> Self {
        Self::default()
    }

    fn insert(&mut self, req: TypeRequirement) {
        self.0 |= Self::enum_to_mask(req);
    }

    fn into_iter(self) -> impl Iterator<Item = TypeRequirement> {
        let mut n = self.0;
        iter::from_fn(move || {
            if n & Self::INTO_ENUM_ITERATOR != 0 {
                n &= !Self::INTO_ENUM_ITERATOR;
                Some(TypeRequirement::IntoEnumIterator)
            } else if n & Self::CLONE != 0 {
                n &= !Self::CLONE;
                Some(TypeRequirement::Clone)
            } else {
                None
            }
        })
    }

    fn extend(&mut self, other: Self) {
        self.0 |= other.0;
    }

    fn enum_to_mask(req: TypeRequirement) -> u8 {
        match req {
            TypeRequirement::IntoEnumIterator => Self::INTO_ENUM_ITERATOR,
            TypeRequirement::Clone => Self::CLONE,
        }
    }
}

impl<const N: usize> From<[TypeRequirement; N]> for TypeRequirements {
    fn from(reqs: [TypeRequirement; N]) -> Self {
        reqs.into_iter()
            .fold(TypeRequirements::new(), |mut acc, req| {
                acc.insert(req);
                acc
            })
    }
}

#[derive(Debug)]
enum Error {
    UnsupportedUnion,
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
        }
    }
}

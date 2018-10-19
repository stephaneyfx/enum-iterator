// Copyright (C) 2018 Stephane Raux. Distributed under the MIT license.

//! Procedural macro to derive `IntoEnumIterator` for field-less enums.
//!
//! See crate [enum-iterator](https://docs.rs/enum-iterator) for details.

#![recursion_limit = "128"]
#![deny(warnings)]

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate quote;
extern crate syn;

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::{Ident, DeriveInput};

/// Derives `IntoEnumIterator` for field-less enums.
#[proc_macro_derive(IntoEnumIterator)]
pub fn into_enum_iterator(input: TokenStream) -> TokenStream {
    let ast = syn::parse::<DeriveInput>(input).unwrap();
    if !ast.generics.params.is_empty() {
        panic!("IntoEnumIterator cannot be derived for generic types")
    }
    let ty = &ast.ident;
    let ty_doc = format!("Iterator over the variants of {}", ty);
    let iter_ty = Ident::new(&(ty.to_string() + "EnumIterator"),
        Span::call_site());
    let vis = &ast.vis;
    let variants = match &ast.data {
        syn::Data::Enum(e) => &e.variants,
        _ => abort(),
    };
    let arms = variants.iter().map(field_less).enumerate()
        .map(|(idx, id)| quote! {
            #idx => #ty::#id,
        });
    let nb_variants = arms.len();
    let tokens = quote! {
        #[doc = #ty_doc]
        #[derive(Clone, Copy)]
        #vis struct #iter_ty {
            idx: usize,
        }

        impl ::std::iter::Iterator for #iter_ty {
            type Item = #ty;

            fn next(&mut self) -> ::std::option::Option<Self::Item> {
                let id = match self.idx {
                    #(#arms)*
                    _ => return ::std::option::Option::None,
                };
                self.idx += 1;
                ::std::option::Option::Some(id)
            }

            fn size_hint(&self) -> (usize, ::std::option::Option<usize>) {
                let n = #nb_variants - self.idx;
                (n, Some(n))
            }
        }

        impl ::std::iter::ExactSizeIterator for #iter_ty {}
        impl ::std::iter::FusedIterator for #iter_ty {}

        impl ::enum_iterator::IntoEnumIterator for #ty {
            type Iterator = #iter_ty;

            fn into_enum_iter() -> Self::Iterator {
                #iter_ty {idx: 0}
            }
        }
    };
    tokens.into()
}

fn field_less(v: &syn::Variant) -> &Ident {
    if let syn::Fields::Unit = v.fields {
        &v.ident
    } else {
        abort()
    }
}

fn abort() -> ! {
    panic!("IntoEnumIterator can only be derived for field-less enums")
}

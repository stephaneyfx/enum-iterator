// Copyright (C) 2018-2022 Stephane Raux. Distributed under the 0BSD license.

//! # Overview
//! - [📦 crates.io](https://crates.io/crates/enum-iterator)
//! - [📖 Documentation](https://docs.rs/enum-iterator)
//! - [⚖ 0BSD license](https://spdx.org/licenses/0BSD.html)
//!
//! Tools to iterate over the values of a type.
//!
//! See the [`IntoEnumIterator`] trait.
//!
//! # Example
//! ```
//! use enum_iterator::IntoEnumIterator;
//!
//! #[derive(Debug, IntoEnumIterator, PartialEq)]
//! enum Day { Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday }
//!
//! assert_eq!(Day::into_enum_iter().next(), Some(Day::Monday));
//! assert_eq!(Day::into_enum_iter().last(), Some(Day::Sunday));
//! ```
//!
//! # Contribute
//! All contributions shall be licensed under the [0BSD license](https://spdx.org/licenses/0BSD.html).

#![deny(missing_docs)]
#![deny(warnings)]
#![no_std]

pub use enum_iterator_derive::IntoEnumIterator;

/// Trait to iterate over the values of a type.
///
/// # Derivation
///
/// `IntoEnumIterator` can be derived for `enum` and `struct` types. Specifically, it can be derived
/// for:
/// - Enumerations whose variants meet one of the following criteria:
///   - The variant does not have fields.
///   - The variant has fields such that:
///     - Every field has a type that implements `IntoEnumIterator`.
///     - Every field but the first one has a type that implements `Clone`.
/// - Structures whose fields are such that:
///     - Every field has a type that implements `IntoEnumIterator`.
///     - Every field but the first one has a type that implements `Clone`.
///
/// The number of values of the type must not exceed `usize::MAX`.
///
/// # Examples
/// ## C-like enumeration
///
/// ```
/// use enum_iterator::IntoEnumIterator;
///
/// #[derive(Clone, Copy, IntoEnumIterator, PartialEq)]
/// enum Direction { North, South, West, East }
///
/// assert_eq!(Direction::ITEM_COUNT, 4);
/// assert!(Direction::into_enum_iter().eq([
///     Direction::North,
///     Direction::South,
///     Direction::West,
///     Direction::East,
/// ]));
/// ```
///
/// ## Enumeration with data
///
/// ```
/// use enum_iterator::IntoEnumIterator;
///
/// #[derive(Clone, Copy, IntoEnumIterator, PartialEq)]
/// enum Direction { North, South, West, East }
///
/// #[derive(Clone, Copy, IntoEnumIterator, PartialEq)]
/// enum Greeting {
///     Hi,
///     Bye,
/// }
///
/// #[derive(Clone, Copy, IntoEnumIterator, PartialEq)]
/// enum Action {
///     Move(Direction),
///     Jump,
///     Talk { greeting: Greeting, loud: bool },
/// }
///
/// assert_eq!(Action::ITEM_COUNT, 4 + 1 + 2 * 2);
/// assert!(Action::into_enum_iter().eq([
///     Action::Move(Direction::North),
///     Action::Move(Direction::South),
///     Action::Move(Direction::West),
///     Action::Move(Direction::East),
///     Action::Jump,
///     Action::Talk { greeting: Greeting::Hi, loud: false },
///     Action::Talk { greeting: Greeting::Bye, loud: false },
///     Action::Talk { greeting: Greeting::Hi, loud: true },
///     Action::Talk { greeting: Greeting::Bye, loud: true },
/// ]));
/// ```
///
/// ## Structure
///
/// ```
/// use enum_iterator::IntoEnumIterator;
///
/// #[derive(Clone, Copy, IntoEnumIterator, PartialEq)]
/// enum Side {
///     Left,
///     Right,
/// }
///
/// #[derive(Clone, Copy, IntoEnumIterator, PartialEq)]
/// enum LimbKind {
///     Arm,
///     Leg,
/// }
///
/// #[derive(IntoEnumIterator, PartialEq)]
/// struct Limb {
///     kind: LimbKind,
///     side: Side,
/// }
///
/// assert_eq!(Limb::ITEM_COUNT, 4);
/// assert!(Limb::into_enum_iter().eq([
///     Limb { kind: LimbKind::Arm, side: Side::Left },
///     Limb { kind: LimbKind::Leg, side: Side::Left },
///     Limb { kind: LimbKind::Arm, side: Side::Right },
///     Limb { kind: LimbKind::Leg, side: Side::Right },
/// ]));
/// ```
pub trait IntoEnumIterator: Sized {
    /// Type of the iterator returned by [`IntoEnumIterator::into_enum_iter`].
    type Iterator: Iterator<Item = Self> + Clone;

    /// Number of values in `Self`.
    const ITEM_COUNT: usize;

    /// Returns an iterator over the values of `Self`.
    fn into_enum_iter() -> Self::Iterator;
}

impl IntoEnumIterator for bool {
    type Iterator = core::array::IntoIter<bool, 2>;
    const ITEM_COUNT: usize = 2;

    fn into_enum_iter() -> Self::Iterator {
        [false, true].into_iter()
    }
}

impl IntoEnumIterator for i8 {
    type Iterator = core::ops::RangeInclusive<i8>;
    const ITEM_COUNT: usize = 1 << 8;

    fn into_enum_iter() -> Self::Iterator {
        i8::MIN..=i8::MAX
    }
}

impl IntoEnumIterator for u8 {
    type Iterator = core::ops::RangeInclusive<u8>;
    const ITEM_COUNT: usize = 1 << 8;

    fn into_enum_iter() -> Self::Iterator {
        u8::MIN..=u8::MAX
    }
}

impl IntoEnumIterator for i16 {
    type Iterator = core::ops::RangeInclusive<i16>;
    const ITEM_COUNT: usize = 1 << 16;

    fn into_enum_iter() -> Self::Iterator {
        i16::MIN..=i16::MAX
    }
}

impl IntoEnumIterator for u16 {
    type Iterator = core::ops::RangeInclusive<u16>;
    const ITEM_COUNT: usize = 1 << 16;

    fn into_enum_iter() -> Self::Iterator {
        u16::MIN..=u16::MAX
    }
}

impl IntoEnumIterator for () {
    type Iterator = TupleEnumIterator<bool>;
    const ITEM_COUNT: usize = 1;

    fn into_enum_iter() -> Self::Iterator {
        TupleEnumIterator(false)
    }
}

impl Iterator for TupleEnumIterator<bool> {
    type Item = ();

    fn next(&mut self) -> Option<()> {
        if self.0 {
            None
        } else {
            self.0 = true;
            Some(())
        }
    }
}

impl<T: IntoEnumIterator> IntoEnumIterator for Option<T> {
    type Iterator = OptionEnumIterator<T>;
    const ITEM_COUNT: usize = T::ITEM_COUNT + 1;

    fn into_enum_iter() -> Self::Iterator {
        OptionEnumIterator::new()
    }
}

macro_rules! tuple_next {
    ($this:ident, $carry:expr, $($values:expr,)* @ $($placeholders:pat,)* @) => {
        Some(($($values,)*)).filter(|_| !$carry)
    };

    ($this:ident, $carry:expr, $($values:expr,)* @ $($placeholders:pat,)* @ $head:ty, $($tail:ty,)*) => {{
        let ($($placeholders,)* cache, it, ..) = $this;
        let (x, new_carry) = match cache.as_ref().filter(|_| !$carry).cloned() {
            Some(x) => Some((x, false)),
            None => {
                let (x, new_carry) = match it.next() {
                    Some(x) => Some((x, false)),
                    None => {
                        *it = <$head as IntoEnumIterator>::into_enum_iter();
                        it.next().map(|x| (x, true))
                    }
                }?;
                *cache = Some(x.clone());
                Some((x, new_carry))
            }
        }?;
        tuple_next!($this, new_carry, $($values,)* x, @ $($placeholders,)* _, _, @ $($tail,)*)
    }};
}

macro_rules! impl_tuple {
    ($head:ident, $($tail:ident,)*) => {
        impl<$head, $($tail),*> IntoEnumIterator for ($head, $($tail,)*)
        where
            $head: IntoEnumIterator,
            $($tail: IntoEnumIterator + Clone),*
        {
            type Iterator = TupleEnumIterator<(
                core::marker::PhantomData<$head>,
                <$head as IntoEnumIterator>::Iterator,
                $(Option<$tail>, <$tail as IntoEnumIterator>::Iterator,)*
            )>;
            const ITEM_COUNT: usize = <$head as IntoEnumIterator>::ITEM_COUNT $(* <$tail as IntoEnumIterator>::ITEM_COUNT)*;

            fn into_enum_iter() -> Self::Iterator {
                TupleEnumIterator((
                    core::marker::PhantomData,
                    <$head as IntoEnumIterator>::into_enum_iter(),
                    $(None, <$tail as IntoEnumIterator>::into_enum_iter(),)*
                ))
            }
        }

        impl<$head, $($tail),*> Iterator for TupleEnumIterator<(
            core::marker::PhantomData<$head>,
            <$head as IntoEnumIterator>::Iterator,
            $(Option<$tail>, <$tail as IntoEnumIterator>::Iterator,)*
        )>
        where
            $head: IntoEnumIterator,
            $($tail: IntoEnumIterator + Clone),*
        {
            type Item = ($head, $($tail,)*);

            fn next(&mut self) -> Option<Self::Item> {
                let inner = &mut self.0;
                let (x, carry) = match inner.1.next() {
                    Some(x) => Some((x, false)),
                    None => {
                        inner.1 = <$head as IntoEnumIterator>::into_enum_iter();
                        inner.1.next().map(|x| (x, true))
                    }
                }?;
                tuple_next!(inner, carry, x, @ _, _, @ $($tail,)*)
            }
        }
    };
}

macro_rules! impl_tuples {
    ($($types:ident,)*) => {
        impl_tuples!(@ $($types,)*);
    };
    ($($types:ident,)* @ $head:ident, $($tail:ident,)*) => {
        impl_tuple!($($types,)* $head,);
        impl_tuples!($($types,)* $head, @ $($tail,)*);
    };
    ($($types:ident,)* @) => {};
}

impl_tuples!(
    T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20,
    T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31,
);

mod prv {
    use crate::IntoEnumIterator;

    #[derive(Clone, Debug)]
    pub struct TupleEnumIterator<T>(pub(crate) T);

    pub struct OptionEnumIterator<T: IntoEnumIterator>(OptionEnumIteratorInner<T>);

    impl<T: IntoEnumIterator> OptionEnumIterator<T> {
        pub(crate) fn new() -> Self {
            Self(OptionEnumIteratorInner::None)
        }
    }

    impl<T: IntoEnumIterator> Clone for OptionEnumIterator<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: IntoEnumIterator> Iterator for OptionEnumIterator<T> {
        type Item = Option<T>;

        fn next(&mut self) -> Option<Option<T>> {
            match &mut self.0 {
                OptionEnumIteratorInner::None => {
                    self.0 = OptionEnumIteratorInner::Some(T::into_enum_iter());
                    Some(None)
                }
                OptionEnumIteratorInner::Some(it) => it.next().map(Some),
            }
        }
    }

    enum OptionEnumIteratorInner<T: IntoEnumIterator> {
        None,
        Some(T::Iterator),
    }

    impl<T: IntoEnumIterator> Clone for OptionEnumIteratorInner<T> {
        fn clone(&self) -> Self {
            match self {
                Self::None => Self::None,
                Self::Some(it) => Self::Some(it.clone()),
            }
        }
    }
}

use prv::{OptionEnumIterator, TupleEnumIterator};

#[cfg(test)]
mod tests {
    use crate::IntoEnumIterator;

    fn item_count_matches_length<T: IntoEnumIterator>() {
        assert_eq!(T::ITEM_COUNT, T::into_enum_iter().count());
    }

    #[test]
    fn item_count_matches_length_for_bool() {
        item_count_matches_length::<bool>();
    }

    #[test]
    fn item_count_matches_length_for_i8() {
        item_count_matches_length::<i8>();
    }

    #[test]
    fn item_count_matches_length_for_u8() {
        item_count_matches_length::<u8>();
    }

    #[test]
    fn item_count_matches_length_for_i16() {
        item_count_matches_length::<i16>();
    }

    #[test]
    fn item_count_matches_length_for_u16() {
        item_count_matches_length::<u16>();
    }

    #[test]
    fn item_count_matches_length_for_unit() {
        item_count_matches_length::<()>();
    }

    #[test]
    fn item_count_matches_length_for_singleton() {
        item_count_matches_length::<(u8,)>();
    }

    #[test]
    fn item_count_matches_length_for_pair() {
        item_count_matches_length::<(u8, bool)>();
    }

    #[test]
    fn item_count_matches_length_for_triple() {
        item_count_matches_length::<(bool, u8, bool)>();
    }

    #[test]
    fn item_count_matches_length_for_option() {
        item_count_matches_length::<Option<u8>>();
    }

    #[test]
    fn check_option_items() {
        assert!(Option::<bool>::into_enum_iter().eq([None, Some(false), Some(true)]));
    }
}

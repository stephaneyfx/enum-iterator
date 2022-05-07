<!-- cargo-sync-readme start -->

# Overview
- [📦 crates.io](https://crates.io/crates/enum-iterator)
- [📖 Documentation](https://docs.rs/enum-iterator)
- [⚖ 0BSD license](https://spdx.org/licenses/0BSD.html)

Tools to iterate over the values of a type.

See the [`IntoEnumIterator`] trait.

# Examples
```rust
use enum_iterator::IntoEnumIterator;

#[derive(Debug, IntoEnumIterator, PartialEq)]
enum Day { Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday }

assert_eq!(Day::into_enum_iter().next(), Some(Day::Monday));
assert_eq!(Day::into_enum_iter().last(), Some(Day::Sunday));
```

```rust
use enum_iterator::IntoEnumIterator;

#[derive(Debug, IntoEnumIterator, PartialEq)]
struct Foo {
    a: bool,
    b: u8,
}

assert_eq!(Foo::into_enum_iter().next(), Some(Foo { a: false, b: 0 }));
assert_eq!(Foo::into_enum_iter().last(), Some(Foo { a: true, b: 255 }));
```

# Contribute
All contributions shall be licensed under the [0BSD license](https://spdx.org/licenses/0BSD.html).

<!-- cargo-sync-readme end -->

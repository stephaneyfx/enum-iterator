use enum_iterator::IntoEnumIterator;

#[derive(Clone, IntoEnumIterator, PartialEq)]
enum Direction {
    North,
    South,
    West,
    East,
}

#[derive(Clone, IntoEnumIterator, PartialEq)]
enum Either<L, R> {
    Left(L),
    Right(R),
}

#[test]
fn into_enum_iterator_can_be_derived_for_generic_type() {
    assert!(Either::<bool, Direction>::into_enum_iter().eq([
        Either::Left(false),
        Either::Left(true),
        Either::Right(Direction::North),
        Either::Right(Direction::South),
        Either::Right(Direction::West),
        Either::Right(Direction::East),
    ]))
}

#[derive(Clone, IntoEnumIterator, PartialEq)]
struct Foo<T: Copy> {
    x: T,
}

#[test]
fn into_enum_iterator_can_be_derived_for_generic_type_with_trait_bound() {
    assert!(Foo::<bool>::into_enum_iter().eq([Foo { x: false }, Foo { x: true }]));
}

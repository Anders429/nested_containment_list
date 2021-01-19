# nested_containment_list

Implementation of a Nested Containment List.

A Nested Containment List, as presented by Alexander V. Alekseyenko and Christopher J. Lee in their 
[2007 *Bioinformations* publication](https://doi.org/10.1093/bioinformatics/btl647), is a data
structure for efficiently storing and querying intervals.

## Usage

To allow a type to be stored and used with Nested Containment Lists, it must implement the
`Nestable` trait.

```rust
use nested_containment_list::Nestable;

impl Nestable<usize> for MyStruct {
    fn left_bound(&self) -> usize {
        ...
    }

    fn right_bound(&self) -> usize {
        ...
    }
}
```

The type can then be stored within a Nested Containment List.

Note that the `Nestable` trait is already implemented for `Range`. A `Range` can therefore be used
in Nested Containment Lists like so:

```rust
use nested_containment_list::NestedContainmentList;

let nclist = NestedContainmentList::new();

nclist.insert(1..5);
nclist.insert(2..4);
nclist.insert(6..7);
```

Data stored within the Nested Containment List structure can be accessed through a nested `Iterator`
structure obtained by either the `.sublist()` or `.overlapping()` method.

```rust
// .sublist() iterates over all stored data through a nested Iterator.
let mut sublist = nclist.sublist();

let first_element = sublist.next().unwrap();
// The first element will be the first interval.
assert_eq!(first_element.value, &(1..5));
// Within the first element's sublist, the next interval, 2..4, which is contained in 1..5, is
// found.
assert_eq!(first_element.sublist().next().unwrap().value, &(2..4));
// 6..7, which is not contained within 1..5, is the next element on the outer-most sublist.
let second_element = sublist.next().unwrap();
assert_eq!(second_element.value, &(6..7));

// .overlapping() iterates over only stored data overlapping with the query, again through a nested
// Iterator.
let mut overlapping = nclist.overlapping(5..7);

let first_element = overlapping.next().unwrap();
// The first element is 1..5, as before.
assert_eq!(first_element.value, &(1..5));
// But the first element doesn't contain next interval, 2..4, because it doesn't overlap with the
// query, 5..7.
assert_eq!(first_element.sublist().next(), None);
// 6..7 also overlaps with the query, so it is contained in the overlapping iterator.
let second_element = overlapping.next().unwrap();
assert_eq!(second_element.value, &(6..7));
```

## Minimum Supported Rust Version
This crate is guaranteed to compile on stable `rustc 1.0.0` and up.

# nested_containment_list

[![GitHub Workflow Status](https://img.shields.io/github/workflow/status/Anders429/nested_containment_list/Tests)](https://github.com/Anders429/nested_containment_list/actions)
[![codecov.io](https://img.shields.io/codecov/c/gh/Anders429/nested_containment_list)](https://codecov.io/gh/Anders429/nested_containment_list)
[![crates.io](https://img.shields.io/crates/v/nested_containment_list)](https://crates.io/crates/nested_containment_list)
[![docs.rs](https://docs.rs/nested_containment_list/badge.svg)](https://docs.rs/nested_containment_list)
[![MSRV](https://img.shields.io/badge/rustc-1.28.0+-yellow.svg)](#minimum-supported-rust-version)
[![License](https://img.shields.io/crates/l/nested_containment_list)](#license)

Implementation of a Nested Containment List.

A Nested Containment List is a data structure for efficiently storing and querying intervals. It is
based on the Nested Containment List data structure set forth by Alexander V. Alekseyenko and
Christopher J. Lee in their
[2007 *Bioinformatics* publication](https://doi.org/10.1093/bioinformatics/btl647). The
implementation provided here allows storage and querying of generic types using generical bounds.

## Usage

To allow a type to be stored and used with Nested Containment Lists, it must implement the
[`Interval`](https://docs.rs/nested_containment_list/*/nested_containment_list/trait.Interval.html)
trait.

```rust
use nested_containment_list::Interval;

impl Interval<usize> for MyStruct {
    fn start(&self) -> usize {
        ...
    }

    fn end(&self) -> usize {
        ...
    }
}
```

The type can then be stored within a Nested Containment List.

Note that the `Interval` trait is already implemented for
[`Range`](https://doc.rust-lang.org/std/ops/struct.Range.html). A `Range` can
therefore be used in Nested Containment Lists, like so:

```rust
use nested_containment_list::NestedContainmentList;

let nclist = NestedContainmentList::new();

nclist.insert(1..5);
nclist.insert(2..4);
nclist.insert(6..7);
nclist.insert(5..9);
```

Data stored within the Nested Containment List is typically accessed through a nested
[`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) structure, obtained by querying
using the
[`.overlapping()`](https://docs.rs/nested_containment_list/*/nested_containment_list/struct.NestedContainmentList.html#method.overlapping)
method.

```rust
let query = 3..6;
let mut overlapping = nclist.overlapping(&query);

// 1..5 overlaps with 3..6, so it is the first element.
let first_element = overlapping.next().unwrap();
assert_eq!(first_element.value, &(1..5));
// 2..4 is contained inside 1..5 and overlaps with 3..6, so it is accessed through the first
// element's sublist.
assert_eq!(first_element.sublist().next().unwrap().value, &(2..4));
// 5..9 overlaps with 3..6, so it is the second element.
let second_element = overlapping.next().unwrap();
assert_eq!(second_element.value, &(5..9));
// Even though 6..7 is contained inside 5..9, it does not overlap with 3..6, and therefore is not
// contained in the second element's sublist.
assert!(second_element.sublist().next().is_none())
```

## Performance

### Construction
Construction of a
[`NestedContainmentList`](https://docs.rs/nested_containment_list/*/nested_containment_list/struct.NestedContainmentList.html)
has temporal complexity *O(n log(n))*. Insertion using
[`NestedContainmentList::insert()`](https://docs.rs/nested_containment_list/*/nested_containment_list/struct.NestedContainmentList.html#method.insert)
has temporal complexity *O(log n)*. Similarly, removal using
[`NestedContainmentList::remove()`](https://docs.rs/nested_containment_list/*/nested_containment_list/struct.NestedContainmentList.html#method.remove)
also has temporal complexity *O(log n)*.

### Querying
Querying for overlapping intervals with
[`NestedContainmentList::overlapping()`](https://docs.rs/nested_containment_list/*/nested_containment_list/struct.NestedContainmentList.html#method.overlapping)
has temporal complexity *O(n + log(N))*, where *N* is the number of intervals stored within the
Nested Containment List, and *n* is the number of intervals overlapping with the query.

## Minimum Supported Rust Version
This crate is guaranteed to compile on stable `rustc 1.28.0` and up. Use in a
[`no_std`](https://doc.rust-lang.org/1.7.0/book/using-rust-without-the-standard-library.html)
environment requires stable `rustc 1.36.0` and up, due to the use of
[`alloc`](https://doc.rust-lang.org/alloc/index.html).

## License
This project is licensed under either of

* Apache License, Version 2.0
([LICENSE-APACHE](https://github.com/Anders429/nested_containment_list/blob/HEAD/LICENSE-APACHE) or
http://www.apache.org/licenses/LICENSE-2.0)
* MIT license
([LICENSE-MIT](https://github.com/Anders429/nested_containment_list/blob/HEAD/LICENSE-MIT) or
http://opensource.org/licenses/MIT)

at your option.

//! Implementation of a Nested Containment List.
//!
//! A Nested Containment List is a data structure for storing types that implement the [`Interval`]
//! trait. Elements stored in a [`NestedContainmentList`] are stored in a nested structure to allow
//! for easy querying using `Interval` queries.
//!
//! # Example Usage
//! Given that `Interval` is implemented on [`Range`], the following examples will store and query
//! on `Range`s.
//!
//! ## Construction
//!
//! Construction of [`NestedContainmentList`]s can be done using either the [`new()`] or
//! [`from_slice()`] methods. Construction from `from_slice()` has temporal complexity
//! *O(n log(n))*, where *n* is the length of the slice.
//!
//! ```
//! use nested_containment_list::NestedContainmentList;
//! use std::ops::Range;
//!
//! let nclist = NestedContainmentList::<usize, Range<usize>>::new();
//! ```
//!
//! ```
//! use nested_containment_list::NestedContainmentList;
//!
//! let nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 5..7]);
//! ```
//!
//! ## Mutation
//!
//! A [`NestedContainmentList`] allows for insertion and removal of [`Interval`] types. Both of
//! these methods have a temporal complexity of *O(log(n))*, where *n* is the number of `Interval`s
//! stored in the data structure.
//!
//! ```
//! use nested_containment_list::NestedContainmentList;
//!
//! let mut nclist = NestedContainmentList::new();
//!
//! nclist.insert(1..5);
//! nclist.remove(&(1..5));
//! ```
//!
//! ## Iteration
//!
//! Iterating over a [`NestedContainmentList`] is done in a nested manner. [`Iterator`]s obtained
//! from the [`sublist()`] and [`overlapping()`] methods iterate directly over the relevant top-most
//! sublist, with intervals contained within the top-most elements being accessed through nested
//! sublists.
//!
//! For example, iterating using [`sublist()`] can be done as follows:
//!
//! ```
//! use nested_containment_list::NestedContainmentList;
//!
//! let nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 6..7]);
//! let mut sublist = nclist.sublist();
//!
//! // The first element in the top-most sublist, 1..5.
//! let first_element = sublist.next().unwrap();
//! assert_eq!(first_element.value, &(1..5));
//!
//! // Contained inside the element's sublist is the interval 2..4.
//! assert_eq!(first_element.sublist().next().unwrap().value, &(2..4));
//!
//! // The next element in the top-most sublist is 6..7, so it is obtained like the first element.
//! let second_element = sublist.next().unwrap();
//! assert_eq!(second_element.value, &(6..7));
//! ```
//!
//! To remove a single level of nesting, one may use the [`Iterator::flatten()`] method.
//!
//! # no_std
//! This crate is usable in
//! [`no_std`](https://doc.rust-lang.org/1.7.0/book/using-rust-without-the-standard-library.html)
//! environments when compiled on stable `rustc 1.36.0` or higher. The version limitation is due to
//! the use of [`alloc`](https://doc.rust-lang.org/alloc/index.html), allowing for heap allocation
//! without use of [`std`](https://doc.rust-lang.org/std/).
//!
//! [`from_slice()`]: NestedContainmentList::from_slice()
//! [`new()`]: NestedContainmentList::new()
//! [`overlapping()`]: NestedContainmentList::overlapping()
//! [`sublist()`]: NestedContainmentList::sublist()
//! [`Iterator`]: core::iter::Iterator
//! [`Iterator::flatten()`]: core::iter::Iterator::flatten()
//! [`Range`]: core::ops::Range

#![cfg_attr(rustc_1_36, no_std)]

#[cfg(rustc_1_36)]
extern crate alloc;
#[cfg(not(rustc_1_36))]
extern crate std as alloc;
#[cfg(not(rustc_1_36))]
extern crate std as core;

#[cfg(test)]
#[macro_use]
extern crate claim;
#[cfg(test)]
extern crate more_ranges;

mod impls;
mod nestable;

use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::iter::Chain;
use core::iter::Iterator;
use core::marker::PhantomData;
use core::option;

/// Trait for values that are intervals.
///
/// Here, an interval contains all values between the interval's [`start()`] and [`end()`],
/// **including** [`start()`] and **excluding** [`end()`].
///
/// The bounding type `B` of the interval may be any type which implements [`Ord`].
///
/// # Example
/// ```
/// use nested_containment_list::Interval;
///
/// struct Foo {
///     start: usize,
///     end: usize,
/// }
///
/// impl Interval<usize> for Foo {
///     fn start(&self) -> usize {
///         self.start
///     }
///
///     fn end(&self) -> usize {
///         self.end
///     }
/// }
/// ```
///
/// [`start()`]: Self::start()
/// [`end()`]: Self::end()
/// ['Ord']: std::cmp::Ord
pub trait Interval<B>
where
    B: Ord,
{
    /// The lower bound of the interval (inclusive).
    fn start(&self) -> B;
    /// The upper bound of the interval (exclusive).
    fn end(&self) -> B;
}

fn nestable_contains<B, I>(a: &I, b: &I) -> bool
where
    B: Ord,
    I: Interval<B>,
{
    Interval::start(a) <= Interval::start(b)
        && Interval::start(b) <= Interval::end(b)
        && Interval::end(b) <= Interval::end(a)
}

fn nestable_ordering<B, I>(a: &I, b: &I) -> Ordering
where
    B: Ord,
    I: Interval<B>,
{
    if Interval::start(a) < Interval::start(b)
        || Interval::start(a) == Interval::start(b) && Interval::end(a) > Interval::end(b)
    {
        Ordering::Less
    } else if Interval::start(a) > Interval::start(b) || Interval::end(a) < Interval::end(b) {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

fn nestable_overlap<B, I>(a: &I, b: &I) -> bool
where
    B: Ord,
    I: Interval<B>,
{
    Interval::start(a) < Interval::end(b) && Interval::end(a) >= Interval::end(b)
        || Interval::start(b) < Interval::end(a) && Interval::end(b) >= Interval::end(a)
}

#[derive(Debug)]
struct Element<B, I>
where
    B: Ord,
    I: Interval<B>,
{
    value: I,
    sublist_len: usize,
    _marker: PhantomData<B>,
}

/// An element contained within a [`Sublist`].
///
/// This element allows access to its contained value `I` and its sub-elements.
///
/// A `SublistElement` is usually obtained from iterating over a `Sublist`.
///
/// # Example
/// ```
/// use nested_containment_list::NestedContainmentList;
///
/// let nclist = NestedContainmentList::from_slice(&[1..4, 2..3]);
/// let mut sublist = nclist.sublist();
///
/// let sublist_element = sublist.next().unwrap();
/// assert_eq!(sublist_element.value, &(1..4));
///
/// let inner_sublist_element = sublist_element.sublist().next().unwrap();
/// assert_eq!(inner_sublist_element.value, &(2..3));
/// ```
#[derive(Debug)]
pub struct SublistElement<'a, B, I>
where
    B: Ord + 'a,
    I: Interval<B> + 'a,
{
    /// The element's contained [`Interval`].
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..2]);
    /// let mut sublist = nclist.sublist();
    ///
    /// let sublist_element = sublist.next().unwrap();
    /// assert_eq!(sublist_element.value, &(1..2));
    pub value: &'a I,
    sublist_elements: &'a [Element<B, I>],
    _marker: PhantomData<B>,
}

impl<'a, B, I> SublistElement<'a, B, I>
where
    B: Ord,
    I: Interval<B>,
{
    /// Return a [`Sublist`] [`Iterator`] over this element's contained sublist.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5, 2..3, 3..4]);
    /// let mut sublist = nclist.sublist();
    ///
    /// let sublist_element = sublist.next().unwrap();
    /// assert_eq!(sublist_element.value, &(1..5));
    ///
    /// let mut inner_sublist = sublist_element.sublist();
    /// assert_eq!(inner_sublist.next().unwrap().value, &(2..3));
    /// assert_eq!(inner_sublist.next().unwrap().value, &(3..4));
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
    pub fn sublist(&self) -> Sublist<'a, B, I> {
        Sublist::new(self.sublist_elements)
    }
}

impl<'a, B, I> IntoIterator for SublistElement<'a, B, I>
where
    B: Ord,
    I: Interval<B>,
{
    type Item = Self;
    type IntoIter = Chain<option::IntoIter<Self::Item>, Sublist<'a, B, I>>;

    /// Convert the element into an iterator, first returning the element's `value`, then each of
    /// the topmost elements in the element's sublist.
    ///
    /// This can conceptually be thought of as flattening the element with its top-most sublist.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5, 2..3, 3..4]);
    /// let mut sublist = nclist.sublist();
    ///
    /// let sublist_element = sublist.next().unwrap();
    ///
    /// let mut sublist_element_iter = sublist_element.into_iter();
    /// assert_eq!(sublist_element_iter.next().unwrap().value, &(1..5));
    /// assert_eq!(sublist_element_iter.next().unwrap().value, &(2..3));
    /// assert_eq!(sublist_element_iter.next().unwrap().value, &(3..4));
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        Some(SublistElement {
            value: self.value,
            sublist_elements: &[],
            _marker: PhantomData,
        })
        .into_iter()
        .chain(self.sublist())
    }
}

/// An [`Iterator`] over all elements in a [`NestedContainmentList`].
///
/// This [`Iterator`] is typically created from the [`NestedContainmentList::sublist()`] method.
///
/// Iterates over all elements within the [`NestedContainmentList`] in a nested structure, with all
/// elements contained in other elements being accessed through those elements' [`sublist()`]
/// methods.
///
/// # Example
/// ```
/// use nested_containment_list::NestedContainmentList;
///
/// let nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 3..4, 5..7]);
/// let mut sublist = nclist.sublist();
///
/// let first_element = sublist.next().unwrap();
/// let second_element = sublist.next().unwrap();
///
/// // The outermost elements are accessed directly.
/// assert_eq!(first_element.value, &(1..5));
/// assert_eq!(second_element.value, &(5..7));
///
/// // Contained elements are accessed through their containing element's sublist.
/// let mut inner_sublist = first_element.sublist();
/// let inner_element = inner_sublist.next().unwrap();
/// assert_eq!(inner_element.value, &(2..4));
///
/// // Further nested elements are accessed in further nested iterators.
/// let mut inner_inner_sublist = inner_element.sublist();
/// let inner_inner_element = inner_inner_sublist.next().unwrap();
/// assert_eq!(inner_inner_element.value, &(3..4));
/// ```
///
/// [`sublist()`]: SublistElement::sublist()
/// [`Iterator`]: core::iter::Iterator
#[derive(Debug)]
pub struct Sublist<'a, B, I>
where
    B: Ord + 'a,
    I: Interval<B> + 'a,
{
    index: usize,
    elements: &'a [Element<B, I>],
}

impl<'a, B, I> Sublist<'a, B, I>
where
    B: Ord,
    I: Interval<B>,
{
    fn new(elements: &'a [Element<B, I>]) -> Self {
        Sublist {
            index: 0,
            elements: elements,
        }
    }
}

impl<'a, B, I> Iterator for Sublist<'a, B, I>
where
    B: Ord,
    I: Interval<B>,
{
    type Item = SublistElement<'a, B, I>;

    /// Returns the next outer-most element.
    ///
    /// Note that any values contained within a returned element must be accessed through the
    /// element's [`sublist()`] method.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5]);
    /// let mut sublist = nclist.sublist();
    ///
    /// assert_eq!(sublist.next().unwrap().value, &(1..5));
    /// assert!(sublist.next().is_none());
    /// ```
    ///
    /// [`sublist()`]: SublistElement::sublist()
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.elements.len() {
            return None;
        }

        let current_index = self.index;

        // Next element.
        let element = &self.elements[self.index];
        // Skip over element's sublist.
        self.index += element.sublist_len;
        // Increment index to move to next element.
        self.index += 1;
        Some(SublistElement {
            value: &element.value,
            sublist_elements: &self.elements[(current_index + 1)..self.index],
            _marker: PhantomData,
        })
    }
}

/// An element contained within an [`Overlapping`].
///
/// This element allows access to its contained value `I` and its sub-elements which also overlap
/// with the query `Q`.
///
/// An `OverlappingElement` is usually obtained from iterating over an `Overlapping`.
///
/// # Example
/// ```
/// use nested_containment_list::NestedContainmentList;
///
/// let nclist = NestedContainmentList::from_slice(&[1..4, 2..3]);
/// let query = 2..4;
/// let mut overlapping = nclist.overlapping(&query);
///
/// let overlapping_element = overlapping.next().unwrap();
/// assert_eq!(overlapping_element.value, &(1..4));
///
/// let inner_overlapping_element = overlapping_element.sublist().next().unwrap();
/// assert_eq!(inner_overlapping_element.value, &(2..3));
/// ```
#[derive(Debug)]
pub struct OverlappingElement<'a, B, Q, I>
where
    B: Ord + 'a,
    Q: Interval<B> + 'a,
    I: Interval<B> + Borrow<Q> + 'a,
{
    pub value: &'a I,
    sublist_elements: &'a [Element<B, I>],
    query: &'a Q,
    _marker: PhantomData<B>,
}

impl<'a, B, Q, I> OverlappingElement<'a, B, Q, I>
where
    B: Ord,
    Q: Interval<B>,
    I: Interval<B> + Borrow<Q>,
{
    /// Return an [`Overlapping`] [`Iterator`] over this element's contained sublist.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5, 2..3, 3..4]);
    /// let query = 2..4;
    /// let mut overlapping = nclist.overlapping(&query);
    ///
    /// let overlapping_element = overlapping.next().unwrap();
    /// assert_eq!(overlapping_element.value, &(1..5));
    ///
    /// let mut inner_overlapping = overlapping_element.sublist();
    /// assert_eq!(inner_overlapping.next().unwrap().value, &(2..3));
    /// assert_eq!(inner_overlapping.next().unwrap().value, &(3..4));
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
    pub fn sublist(&self) -> Overlapping<'a, B, Q, I> {
        Overlapping::new(self.sublist_elements, self.query)
    }
}

impl<'a, B, Q, I> IntoIterator for OverlappingElement<'a, B, Q, I>
where
    B: Ord,
    Q: Interval<B>,
    I: Interval<B> + Borrow<Q>,
{
    type Item = Self;
    type IntoIter = Chain<option::IntoIter<Self::Item>, Overlapping<'a, B, Q, I>>;

    /// Returns the next outer-most element that overlaps the query `Q`.
    ///
    /// Note that any values contained within a returned element must be accessed through the
    /// element's [`sublist()`] method.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5]);
    /// let query = 2..4;
    /// let mut overlapping = nclist.overlapping(&query);
    ///
    /// assert_eq!(overlapping.next().unwrap().value, &(1..5));
    /// assert!(overlapping.next().is_none());
    /// ```
    ///
    /// [`sublist()`]: OverlappingElement::sublist()
    fn into_iter(self) -> Self::IntoIter {
        Some(OverlappingElement {
            value: self.value,
            sublist_elements: &[],
            query: self.query,
            _marker: PhantomData,
        })
        .into_iter()
        .chain(self.sublist())
    }
}

/// An [`Iterator`] over elements in a [`NestedContainmentList`] that overlap a query.
///
/// This [`Iterator`] is typically created from the [`NestedContainmentList::overlapping()`] method.
///
/// Iterates over all elements within the [`NestedContainmentList`] that overlap with the query
/// interval. These elements are iterated in a nested structure, with all elements contained in
/// other elements being accessed through those elements' [`sublist()`] methods.
///
/// # Example
/// ```
/// use nested_containment_list::NestedContainmentList;
///
/// let nclist = NestedContainmentList::from_slice(&[1..5, 2..3, 2..4, 5..7]);
/// let query = 3..6;
/// let mut overlapping = nclist.overlapping(&query);
///
/// let first_element = overlapping.next().unwrap();
/// let second_element = overlapping.next().unwrap();
///
/// // The outermost elements are accessed directly.
/// assert_eq!(first_element.value, &(1..5));
/// assert_eq!(second_element.value, &(5..7));
///
/// // Contained elements are accessed through their containing element's sublist.
/// let mut inner_sublist = first_element.sublist();
/// let inner_element = inner_sublist.next().unwrap();
/// assert_eq!(inner_element.value, &(2..4));
///
/// // Note that 2..3 is not found within the nested iterators, since 2..3 does not overlap with 3..6.
/// ```
///
/// [`sublist()`]: OverlappingElement::sublist()
/// [`Iterator`]: core::iter::Iterator
pub struct Overlapping<'a, B, Q, I>
where
    B: Ord + 'a,
    Q: Interval<B> + 'a,
    I: Interval<B> + Borrow<Q> + 'a,
{
    sublist: Sublist<'a, B, I>,
    query: &'a Q,
}

impl<'a, B, Q, I> Overlapping<'a, B, Q, I>
where
    B: Ord,
    Q: Interval<B>,
    I: Interval<B> + Borrow<Q>,
{
    fn new(elements: &'a [Element<B, I>], query: &'a Q) -> Self {
        // Find the index of the first overlapping interval in the top-most sublist.
        let mut index = 0;
        while index < elements.len()
            && Interval::end(&elements[index].value) <= Interval::start(query)
        {
            index += elements[index].sublist_len + 1;
        }
        Overlapping {
            sublist: Sublist {
                index: index,
                elements: elements,
            },
            query: query,
        }
    }
}

impl<'a, B, Q, I> Iterator for Overlapping<'a, B, Q, I>
where
    B: Ord,
    Q: Interval<B>,
    I: Interval<B> + Borrow<Q>,
{
    type Item = OverlappingElement<'a, B, Q, I>;

    /// Returns the next outer-most element.
    ///
    /// Note that any values contained within a returned element must be accessed through the
    /// element's [`sublist()`] method.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5]);
    /// let query = 2..3;
    /// let mut overlapping = nclist.overlapping(&query);
    ///
    /// assert_eq!(overlapping.next().unwrap().value, &(1..5));
    /// assert!(overlapping.next().is_none());
    /// ```
    ///
    /// [`sublist()`]: OverlappingElement::sublist()
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(sublist_element) = self.sublist.next() {
            if nestable_overlap(Borrow::borrow(sublist_element.value), self.query) {
                return Some(OverlappingElement {
                    value: sublist_element.value,
                    sublist_elements: sublist_element.sublist_elements,
                    query: self.query,
                    _marker: PhantomData,
                });
            } else {
                // End iteration, since there will be no more overlaps.
                self.sublist.index = self.sublist.elements.len()
            }
        }
        None
    }
}

/// Data structure for efficient storage and querying of [`Interval`]s.
///
/// # Usage
///
/// A `NestedContainmentList` is a collection of [`Interval`]s, and can be used similar to other
/// collections. It has a [`len()`] and a [`capacity()`], allows for mutation through [`insert()`]
/// and [`remove()`]. A main difference between `NestedContainmentList` and other Rust collections
/// is how its contents are accessed: they may be iterated over through [`overlapping()`] and
/// [`sublist()`]. For further details, see [Data Access](#data-access).
///
/// ## Construction
///
/// A `NestedContainmentList` stores [`Interval`]s in a nested structure to allow for fast querying.
/// Construction of a `NestedContainmentList` has temporal complexity *O(n log(n))*, where *n* is
/// the number of [`Interval`]s being stored. Both insertion and removal, with [`insert()`] and
/// [`remove()`] respectively, into a `NestedContainmentList` has temporal complexity *O(log(n))*,
/// where *n* is the number of [`Interval`]s currently stored.
///
/// ### Example
/// Construction of a `NestedContainmentList` can be done as follows:
///
/// ```
/// use nested_containment_list::NestedContainmentList;
///
/// let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 5..7]);
/// ```
///
/// ## Data Access
///
/// When data is stored within a `NestedContainmentList`, it is typically accessed in two ways:
///
/// * Querying for [`Interval`]s overlapping an [`Interval`], using the [`overlapping()`] method.
/// * Interating through all [`Interval`]s in a nested [`Iterator`] structure, using the
/// [`sublist()`] method.
///
/// Both methods return a nested [`Iterator`] structure, with the difference being that access
/// through [`overlapping()`] only iterates over [`Interval`]s that overlap with the query
/// [`Interval`]. For details on the [`Iterator`]s returned by these methods, see the documentation
/// for [`Overlapping`] and [`Sublist`].
///
/// Querying using [`overlapping()`] has temporal complexity *O(n + log(N))*, where *N* is the
/// number of [`Interval`]s stored, and *n* is the number of intervals overlapping with the query
/// [`Interval`].
///
/// ### Example
/// Access using either method can be done as follows:
///
/// ```
/// use nested_containment_list::NestedContainmentList;
///
/// let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 5..7]);
///
/// // Creates a Sublist Iterator.
/// let mut sublist = nclist.sublist();
///
/// // Creates an Overlapping Iterator.
/// let query = 4..6;
/// let mut overlapping = nclist.overlapping(&query);
/// ```
///
/// [`capacity()`]: Self::capacity()
/// [`insert()`]: Self::insert()
/// [`len()`]: Self::len()
/// [`overlapping()`]: Self::overlapping()
/// [`remove()`]: Self::remove()
/// [`sublist()`]: Self::sublist()
/// [`Iterator`]: core::iter::Iterator
#[derive(Debug)]
pub struct NestedContainmentList<B, I>
where
    B: Ord,
    I: Interval<B>,
{
    elements: Vec<Element<B, I>>,
}

impl<B, I> NestedContainmentList<B, I>
where
    B: Ord,
    I: Interval<B>,
{
    /// Construct an empty `NestedContainmentList`.
    ///
    /// # Example
    /// The following example constructs a new `NestedContainmentList` to hold elements of type
    /// [`Range<usize>`].
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::ops::Range;
    ///
    /// let nclist = NestedContainmentList::<usize, Range<usize>>::new();
    /// ```
    ///
    /// [`Range<usize>`]: core::ops::Range
    pub fn new() -> Self {
        NestedContainmentList {
            elements: Vec::new(),
        }
    }

    /// Construct an empty `NestedContainmentList` with the specified capacity.
    ///
    /// The `NestedContainmentList` will be able to hold exactly `capacity` [`Interval`]s without
    /// reallocating. If `capacity` is `0`, the `NestedContainmentList` will not allocate.
    ///
    /// Note that `capacity` is not the same as `len`. `len` is how many elements are actually
    /// contained, while `capacity` is how many could be contained given the current allocation.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let mut nclist = NestedContainmentList::with_capacity(5);
    ///
    /// nclist.insert(1..2);  // Does not reallocate, since capacity is available.
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        NestedContainmentList {
            elements: Vec::with_capacity(capacity),
        }
    }

    /// Returns the number of elements contained in the `NestedContainmentList`, also referred to as
    /// its 'length'.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let mut nclist = NestedContainmentList::new();
    /// assert_eq!(nclist.len(), 0);
    ///
    /// nclist.insert(1..5);
    /// assert_eq!(nclist.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Returns `true` if the `NestedContainmentList` contains no elements.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let mut nclist = NestedContainmentList::new();
    /// assert!(nclist.is_empty());
    ///
    /// nclist.insert(1..5);
    /// assert!(!nclist.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns the number of elements the `NestedContainmentList` can hold without reallocating.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::ops::Range;
    ///
    /// let nclist = NestedContainmentList::<usize, Range<usize>>::with_capacity(10);
    /// assert_eq!(nclist.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.elements.capacity()
    }

    /// Returns a [`Sublist`] [`Iterator`] over all elements within the `NestedContainmentList`.
    ///
    /// The [`Sublist`] is a nested [`Iterator`] over the values contained. All [`Interval`]s
    /// contained within other [`Interval`]s in the collection are accessed as nested [`Sublist`]s
    /// under their outer-most values.
    ///
    /// Iterating using this method is very similar to iterating using the [`overlapping()`] method.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 3..4, 5..7]);
    /// let mut sublist = nclist.sublist();
    ///
    /// let first_element = sublist.next().unwrap();
    /// let second_element = sublist.next().unwrap();
    ///
    /// // The outermost elements are accessed directly.
    /// assert_eq!(first_element.value, &(1..5));
    /// assert_eq!(second_element.value, &(5..7));
    ///
    /// // Contained elements are accessed through their containing element's sublist.
    /// let mut inner_sublist = first_element.sublist();
    /// let inner_element = inner_sublist.next().unwrap();
    /// assert_eq!(inner_element.value, &(2..4));
    ///
    /// // Further nested elements are accessed in further nested iterators.
    /// let mut inner_inner_sublist = inner_element.sublist();
    /// let inner_inner_element = inner_inner_sublist.next().unwrap();
    /// assert_eq!(inner_inner_element.value, &(3..4));
    /// ```
    ///
    /// [`overlapping()`]: Self::overlapping()
    /// [`Iterator`]: core::iter::Iterator
    pub fn sublist<'a>(&'a self) -> Sublist<'a, B, I> {
        Sublist::new(&self.elements)
    }

    /// Returns an [`Overlapping`] [`Iterator`] over all elements within the
    /// `NestedContainmentList`.
    ///
    /// The [`Overlapping`] is a nested [`Iterator`] over all values contained in the
    /// `NestedContainmentList` that overlap with the `query` [`Interval`]. All [`Interval`]s
    /// contained within other [`Interval`]s in the collection that also overlap with the `query`
    /// are accessed as nested [`Overlapping`]s under their outer-most values.
    ///
    /// Iterating using this method is very similar to iterating using the [`sublist()`] method.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5, 2..3, 2..4, 5..7]);
    /// let query = 3..6;
    /// let mut overlapping = nclist.overlapping(&query);
    ///
    /// let first_element = overlapping.next().unwrap();
    /// let second_element = overlapping.next().unwrap();
    ///
    /// // The outermost elements are accessed directly.
    /// assert_eq!(first_element.value, &(1..5));
    /// assert_eq!(second_element.value, &(5..7));
    ///
    /// // Contained elements are accessed through their containing element's sublist.
    /// let mut inner_sublist = first_element.sublist();
    /// let inner_element = inner_sublist.next().unwrap();
    /// assert_eq!(inner_element.value, &(2..4));
    ///
    /// // Note that 2..3 is not found within the nested iterators, since 2..3 does not overlap with 3..6.
    /// ```
    ///
    /// [`sublist()`]: Self::sublist()
    /// [`Iterator`]: core::iter::Iterator
    pub fn overlapping<'a, Q>(&'a self, query: &'a Q) -> Overlapping<'a, B, Q, I>
    where
        Q: Interval<B>,
        I: Borrow<Q>,
    {
        Overlapping::new(&self.elements, query)
    }

    /// Insert a new value into the `NestedContainmentList`.
    ///
    /// This insertion preserves the internal nested structure of the container, and has temporal
    /// complexity of *O(log(n))*.
    ///
    /// If the `NestedContainmentList`'s `capacity` is not large enough, the `NestedContainmentList`
    /// will reallocate.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let mut nclist = NestedContainmentList::new();
    /// nclist.insert(1..2);
    /// ```
    pub fn insert(&mut self, value: I) {
        // Direct insertion.
        let mut sublist_indices: Vec<usize> = Vec::with_capacity(self.elements.len());
        let mut indices = 0..self.elements.len();
        while let Some(index) = indices.next() {
            // If the value is ordered less than or equal to this element, then insert the value
            // before this element.
            match nestable_ordering(&value, &self.elements[index].value) {
                Ordering::Less | Ordering::Equal => {
                    // Find the length of the value's sublist.
                    let mut len = 0;
                    for inner_index in index..self.elements.len() {
                        if nestable_contains(&value, &self.elements[inner_index].value) {
                            len += 1;
                        } else {
                            break;
                        }
                    }
                    self.elements.insert(
                        index,
                        Element {
                            value: value,
                            sublist_len: len,
                            _marker: PhantomData,
                        },
                    );
                    // Lengthen the sublist of every parent element.
                    for sublist_index in sublist_indices {
                        self.elements[sublist_index].sublist_len += 1;
                    }
                    // The element is inserted. We are done.
                    return;
                }
                _ => {}
            }

            let element = &self.elements[index];
            if nestable_contains(&element.value, &value) {
                // Proceed down this element's path.
                sublist_indices.push(index);
            } else {
                // If the value isn't contained in this element's sublist, we can skip it entirely.
                if element.sublist_len > 0 {
                    indices.nth(element.sublist_len - 1);
                }
            }
        }

        // Since the value didn't belong somewhere in the middle, we must insert it at the end.
        self.elements.push(Element {
            value: value,
            sublist_len: 0,
            _marker: PhantomData,
        });
        // Lengthen the sublist of every parent element.
        for sublist_index in sublist_indices {
            self.elements[sublist_index].sublist_len += 1;
        }
    }

    /// Remove the specified value from the `NestedContainmentList`.
    ///
    /// This removal preserves the internal nested structure of the container, and has temporal
    /// complexity *O(log(n))*.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 3..4]);
    /// assert!(nclist.remove(&(2..4)));
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        Q: Interval<B>,
        I: Borrow<Q>,
    {
        // Direct removal.
        let mut sublist_indices: Vec<usize> = Vec::with_capacity(self.elements.len());
        let mut indices = 0..self.elements.len();
        while let Some(index) = indices.next() {
            match nestable_ordering(value, Borrow::borrow(&self.elements[index].value)) {
                // If the value is nestably equal to this element, remove it.
                Ordering::Equal => {
                    self.elements.remove(index);
                    // Shorten the sublist of every parent element.
                    for sublist_index in sublist_indices {
                        self.elements[sublist_index].sublist_len -= 1;
                    }
                    // The element is removed. We are done.
                    return true;
                }
                // If the value is nestably less than this element, we have already passed where it
                // would be.
                Ordering::Less => {
                    break;
                }
                Ordering::Greater => {}
            }

            let element = &self.elements[index];
            if nestable_contains(Borrow::borrow(&element.value), value) {
                // Proceed down this element's path.
                sublist_indices.push(index);
            } else {
                // If the value isn't contained in this element's sublist, we can skip it entirely.
                if element.sublist_len > 0 {
                    indices.nth(element.sublist_len - 1);
                }
            }
        }

        false
    }
}

// If the rustc version is 1.20.0 or higher, we can use sort_unstable_by. It is faster than the
// alternative sort_by.
#[cfg(rustc_1_20)]
#[inline]
fn sort_values<B, I>(values: &mut Vec<I>)
where
    B: Ord,
    I: Interval<B> + Clone,
{
    values.sort_unstable_by(nestable_ordering);
}

// Otherwise, we use the regular sort_by.
#[cfg(not(rustc_1_20))]
#[inline]
fn sort_values<B, I>(values: &mut Vec<I>)
where
    B: Ord,
    I: Interval<B> + Clone,
{
    values.sort_by(nestable_ordering);
}

impl<B, I> NestedContainmentList<B, I>
where
    B: Ord,
    I: Interval<B> + Clone,
{
    /// Construct a `NestedContainmentList` from a slice.
    ///
    /// The elements within the slice are cloned into the new `NestedContainmentList`.
    ///
    /// This construction has temporal complexity of *O(n log(n))*, where *n* is the length of the
    /// slice. If you already have a collection of [`Interval`]s that you wish to use to create a
    /// `NestedContainmentList`, this is likely the most efficient way to do so.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 3..4, 5..7]);
    /// ```
    pub fn from_slice(values: &[I]) -> Self {
        // Sort the elements.
        let mut values = values.to_vec();
        sort_values(&mut values);

        // Depth-first construction.
        let mut elements: Vec<Element<B, I>> = Vec::with_capacity(values.len());
        let mut sublist_indices: Vec<usize> = Vec::with_capacity(values.len());
        for index in 0..values.len() {
            let value = values.remove(0);
            while !sublist_indices.is_empty() {
                let sublist_index = sublist_indices.pop().unwrap();

                if nestable_contains(&elements[sublist_index].value, &value) {
                    // We are within the previous sublist.
                    sublist_indices.push(sublist_index);
                    break;
                } else {
                    // We are no longer within the previous sublist.
                    let len = index - sublist_index - 1;
                    elements[sublist_index].sublist_len = len;
                }
            }

            sublist_indices.push(index);
            elements.push(Element {
                value: value,
                sublist_len: 0,
                _marker: PhantomData,
            });
        }

        // Clean up remaining sublist indices.
        for sublist_index in sublist_indices {
            let len = elements.len() - sublist_index - 1;
            elements[sublist_index].sublist_len = len;
        }

        NestedContainmentList { elements: elements }
    }
}

impl<B, I> Default for NestedContainmentList<B, I>
where
    B: Ord,
    I: Interval<B>,
{
    /// Constructs a new, empty `NestedContainmentList`. Equivalent to [`new()`].
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::ops::Range;
    ///
    /// let nclist = NestedContainmentList::<usize, Range<usize>>::default();
    /// ```
    ///
    /// [`new()`]: Self::new()
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(rust_1_36))]
    extern crate std as core;

    use core::ops::Range;
    use NestedContainmentList;

    #[test]
    fn new() {
        let nclist = NestedContainmentList::<usize, Range<usize>>::new();

        // Check that the sublist is empty.
        assert_none!(nclist.sublist().next());
    }

    #[test]
    fn default() {
        let nclist = NestedContainmentList::<usize, Range<usize>>::default();

        // Check that the sublist is empty.
        assert_none!(nclist.sublist().next());
    }

    #[test]
    fn len() {
        let mut nclist = NestedContainmentList::new();

        assert_eq!(nclist.len(), 0);

        nclist.insert(1..5);

        assert_eq!(nclist.len(), 1);
    }

    #[test]
    fn is_empty() {
        assert!(NestedContainmentList::<usize, Range<usize>>::new().is_empty());
    }

    #[test]
    fn is_not_empty() {
        assert!(!NestedContainmentList::from_slice(&[1..2]).is_empty());
    }

    #[test]
    fn capacity() {
        let nclist = NestedContainmentList::<usize, Range<usize>>::with_capacity(10);

        assert_eq!(nclist.capacity(), 10);
    }

    #[test]
    fn insert_on_empty() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);

        let mut sublist = nclist.sublist();
        assert_eq!(sublist.next().unwrap().value, &(1..5));
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_contained() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);
        nclist.insert(2..4);

        let mut sublist = nclist.sublist();
        let sublist_first_element = sublist.next().unwrap();
        assert_eq!(sublist_first_element.value, &(1..5));
        let mut sublist_first_element_sublist = sublist_first_element.sublist();
        assert_eq!(sublist_first_element_sublist.next().unwrap().value, &(2..4));
        assert_none!(sublist_first_element_sublist.next());
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_containing() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(2..4);
        nclist.insert(1..5);

        let mut sublist = nclist.sublist();
        let first_sublist_element = sublist.next().unwrap();
        assert_eq!(first_sublist_element.value, &(1..5));
        let mut first_sublist_element_sublist = first_sublist_element.sublist();
        assert_eq!(first_sublist_element_sublist.next().unwrap().value, &(2..4));
        assert_none!(first_sublist_element_sublist.next());
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_contained_not_at_end() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);
        nclist.insert(6..10);
        nclist.insert(2..4);

        let mut sublist = nclist.sublist();
        let first_sublist_element = sublist.next().unwrap();
        assert_eq!(first_sublist_element.value, &(1..5));
        let mut first_sublist_element_sublist = first_sublist_element.sublist();
        assert_eq!(first_sublist_element_sublist.next().unwrap().value, &(2..4));
        assert_none!(first_sublist_element_sublist.next());
        assert_eq!(sublist.next().unwrap().value, &(6..10));
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_contained_and_containing() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);
        nclist.insert(3..4);
        nclist.insert(2..4);

        let mut sublist = nclist.sublist();
        let first_sublist_element = sublist.next().unwrap();
        assert_eq!(first_sublist_element.value, &(1..5));
        let mut first_sublist_element_sublist = first_sublist_element.sublist();
        let second_sublist_element = first_sublist_element_sublist.next().unwrap();
        assert_eq!(second_sublist_element.value, &(2..4));
        let mut second_sublist_element_sublist = second_sublist_element.sublist();
        assert_eq!(
            second_sublist_element_sublist.next().unwrap().value,
            &(3..4)
        );
        assert_none!(first_sublist_element_sublist.next());
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_equal() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);
        nclist.insert(1..5);

        let mut sublist = nclist.sublist();
        let first_sublist_element = sublist.next().unwrap();
        assert_eq!(first_sublist_element.value, &(1..5));
        let mut first_sublist_element_sublist = first_sublist_element.sublist();
        assert_eq!(first_sublist_element_sublist.next().unwrap().value, &(1..5));
        assert_none!(first_sublist_element_sublist.next());
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_disjoint() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);
        nclist.insert(6..10);

        let mut sublist = nclist.sublist();
        assert_eq!(sublist.next().unwrap().value, &(1..5));
        assert_eq!(sublist.next().unwrap().value, &(6..10));
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_into_second_sublist() {
        let mut nclist = NestedContainmentList::from_slice(&[1..4, 2..3, 5..9]);

        nclist.insert(6..8);

        let mut sublist = nclist.sublist();
        assert_eq!(sublist.next().unwrap().value, &(1..4));
        let second_element = sublist.next().unwrap();
        assert_eq!(second_element.value, &(5..9));
        assert_eq!(second_element.sublist().next().unwrap().value, &(6..8));
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_from_empty() {
        let mut nclist = NestedContainmentList::<usize, Range<usize>>::new();

        assert!(!nclist.remove(&(1..5)));
    }

    #[test]
    fn remove() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5]);

        assert!(nclist.remove(&(1..5)));
    }

    #[test]
    fn remove_not_found() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 6..7]);

        assert!(!nclist.remove(&(1..4)));
    }

    #[test]
    fn remove_contained() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4]);

        assert!(nclist.remove(&(2..4)));

        let mut sublist = nclist.sublist();
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_containing() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 0..6]);

        assert!(nclist.remove(&(0..6)));

        let mut sublist = nclist.sublist();
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_contained_and_containing() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 3..4]);

        assert!(nclist.remove(&(2..4)));

        let mut sublist = nclist.sublist();
        let first_sublist_element = sublist.next().unwrap();
        assert_eq!(first_sublist_element.value, &(1..5));
        let mut first_sublist_element_sublist = first_sublist_element.sublist();
        assert_eq!(first_sublist_element_sublist.next().unwrap().value, &(3..4));
        assert_none!(first_sublist_element_sublist.next());
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_from_second_sublist() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 6..7]);

        assert!(nclist.remove(&(6..7)));
    }

    #[test]
    fn overlapping() {
        let nclist = NestedContainmentList::from_slice(&[1..5, 3..4, 2..4, 6..7]);

        let query = 4..7;
        let mut overlapping = nclist.overlapping(&query);

        let first_element = overlapping.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        let second_element = overlapping.next().unwrap();
        assert_eq!(second_element.value, &(6..7));
        assert_none!(second_element.sublist().next());
        assert_none!(overlapping.next());
    }

    #[test]
    fn overlapping_skip_first() {
        let nclist = NestedContainmentList::from_slice(&[1..2, 3..4]);

        let query = 3..4;
        let mut overlapping = nclist.overlapping(&query);

        let first_element = overlapping.next().unwrap();
        assert_eq!(first_element.value, &(3..4));
        assert_none!(first_element.sublist().next());
        assert_none!(overlapping.next());
    }

    #[test]
    fn overlapping_contained() {
        let nclist = NestedContainmentList::from_slice(&[1..5]);

        let query = 2..3;
        let mut overlapping = nclist.overlapping(&query);

        let first_element = overlapping.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(overlapping.next());
    }

    #[test]
    fn overlapping_starts_at_topmost_element() {
        let nclist = NestedContainmentList::from_slice(&[1..4, 2..3]);
        let query = 2..4;
        let mut overlapping = nclist.overlapping(&query);

        let overlapping_element = overlapping.next().unwrap();
        assert_eq!(overlapping_element.value, &(1..4));

        let inner_overlapping_element = overlapping_element.sublist().next().unwrap();
        assert_eq!(inner_overlapping_element.value, &(2..3));
    }

    #[test]
    fn overlapping_stops_early() {
        let nclist = NestedContainmentList::from_slice(&[1..4, 2..5]);
        let query = 1..2;
        let mut overlapping = nclist.overlapping(&query);

        assert_eq!(overlapping.next().unwrap().value, &(1..4));
        assert_none!(overlapping.next());
    }

    #[test]
    fn from_slice() {
        let nclist = NestedContainmentList::from_slice(&[1..5, 3..4, 2..4, 6..7]);

        let mut sublist = nclist.sublist();
        let first_sublist_element = sublist.next().unwrap();
        assert_eq!(first_sublist_element.value, &(1..5));
        let mut first_sublist_element_sublist = first_sublist_element.sublist();
        let second_sublist_element = first_sublist_element_sublist.next().unwrap();
        assert_eq!(second_sublist_element.value, &(2..4));
        let mut second_sublist_element_sublist = second_sublist_element.sublist();
        assert_eq!(
            second_sublist_element_sublist.next().unwrap().value,
            &(3..4)
        );
        assert_none!(first_sublist_element_sublist.next());
        assert_eq!(sublist.next().unwrap().value, &(6..7));
        assert_none!(sublist.next());
    }
}

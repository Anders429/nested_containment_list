//! Implementation of a Nested Containment List.
//!
//! A Nested Containment List is a data structure for storing types that implement the
//! [`core::ops::RangeBounds`] trait. Elements stored in a [`NestedContainmentList`] are stored in a
//! nested structure to allow for easy querying using other `RangeBounds` queries.
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
//! let nclist = NestedContainmentList::<Range<usize>, usize>::new();
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
//! A [`NestedContainmentList`] allows for insertion and removal of [`RangeBounds`] types. Both of
//! these methods have a temporal complexity of *O(log(n))*, where *n* is the number of
//! `RangeBounds` stored in the data structure.
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
//! Iterating over a [`NestedContainmentList`] is done in a nested manner. An [`Iterator`] is
//! obtained from the [`overlapping()`] method. It is used to iterate directly over the top-most
//! sublist, returning values which overlap with the query range, with nested intervals contained
//! within the top-most elements being accessed through nested sublists.
//!
//! For example, iterating over all elements can be done as follows:
//!
//! ```
//! use nested_containment_list::NestedContainmentList;
//!
//! let nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 6..7]);
//! let mut sublist = nclist.overlapping(&(..));
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
//! [`Iterator`]: core::iter::Iterator
//! [`Iterator::flatten()`]: core::iter::Iterator::flatten()
//! [`RangeBounds`]: core::ops::RangeBounds

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

mod nestable;

use alloc::vec::Vec;
use core::{
    borrow::Borrow,
    cmp::Ordering,
    iter::{Chain, FromIterator, FusedIterator, Iterator, Once, once},
    marker::PhantomData,
    mem,
    ops::RangeBounds,
};
use nestable::Nestable;

#[derive(Debug)]
struct Element<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    value: R,
    sublist_len: usize,
    _marker: PhantomData<T>,
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
pub struct OverlappingElement<'a, R, S, T>
where
    R: RangeBounds<T> + 'a,
    S: RangeBounds<T> + 'a,
    T: Ord + 'a,
{
    pub value: &'a R,
    sublist_elements: &'a [Element<R, T>],
    query: &'a S,
    _marker: PhantomData<T>,
}

impl<'a, R, S, T> OverlappingElement<'a, R, S, T>
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
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
    pub fn sublist(&self) -> Overlapping<'a, R, S, T> {
        Overlapping::new(self.sublist_elements, self.query)
    }
}

impl<'a, R, S, T> IntoIterator for OverlappingElement<'a, R, S, T>
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
    type Item = Self;
    type IntoIter = Chain<Once<Self::Item>, Overlapping<'a, R, S, T>>;

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
        once(OverlappingElement {
            value: self.value,
            sublist_elements: &[],
            query: self.query,
            _marker: PhantomData,
        })
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
pub struct Overlapping<'a, R, S, T>
where
    R: RangeBounds<T> + 'a,
    S: RangeBounds<T> + 'a,
    T: Ord + 'a,
{
    index: usize,
    elements: &'a [Element<R, T>],
    query: &'a S,
}

impl<'a, R, S, T> Overlapping<'a, R, S, T>
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
    fn new(elements: &'a [Element<R, T>], query: &'a S) -> Self {
        // Find the index of the first overlapping interval in the top-most sublist.
        let mut index = 0;
        while index < elements.len() && !elements[index].value.overlapping(query) {
            index += elements[index].sublist_len + 1;
        }
        Overlapping {
            index,
            elements,
            query,
        }
    }
}

impl<'a, R, S, T> Iterator for Overlapping<'a, R, S, T>
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
    type Item = OverlappingElement<'a, R, S, T>;

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
        if self.index >= self.elements.len() {
            return None;
        }
        let current_index = self.index;
        // Next element.
        let element = &self.elements[self.index];

        if element.value.overlapping(self.query) {
            // Skip over element's sublist.
            self.index += element.sublist_len + 1;
            Some(OverlappingElement {
                value: &element.value,
                sublist_elements: &self.elements[(current_index + 1)..self.index],
                query: self.query,
                _marker: PhantomData,
            })
        } else {
            // End iteration, since there will be no more overlaps.
            self.index = self.elements.len();
            None
        }
    }
}

impl<'a, R, S, T> FusedIterator for Overlapping<'a, R, S, T>
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
}

#[derive(Debug)]
pub struct IterElement<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    pub value: R,
    sublist_elements: Vec<Element<R, T>>,
}

impl<R, T> IterElement<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    pub fn sublist(self) -> Iter<R, T> {
        Iter {
            elements: self.sublist_elements,
        }
    }
}

impl<R, T> IntoIterator for IterElement<R, T>
where
    R: RangeBounds<T>,
    T: Ord
{
    type Item = Self;
    type IntoIter = Chain<Once<Self::Item>, Iter<R, T>>;

    fn into_iter(self) -> Self::IntoIter {
        once(IterElement {
            value: self.value,
            sublist_elements: Vec::new(),
        })
        .chain(Iter {
            elements: self.sublist_elements,
        })
    }
}

pub struct Iter<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    elements: Vec<Element<R, T>>,
}

impl<R, T> Iterator for Iter<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    type Item = IterElement<R, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.elements.is_empty() {
            return None;
        }
        // TODO: Is there a more efficient way to do this without moving all elements left?
        // Perhaps reversing the Vec on creation?
        let element = self.elements.remove(0);
        let remaining_elements = self.elements.split_off(element.sublist_len);

        Some(IterElement {
            value: element.value,
            sublist_elements: mem::replace(&mut self.elements, remaining_elements),
        })
    }
}

impl<R, T> FusedIterator for Iter<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
}

/// Data structure for efficient storage and querying of [`RangeBounds`].
///
/// # Usage
///
/// A `NestedContainmentList` is a collection of [`RangeBounds`], and can be used similar to other
/// collections. It has a [`len()`] and a [`capacity()`], allows for mutation through [`insert()`]
/// and [`remove()`]. A main difference between `NestedContainmentList` and other Rust collections
/// is how its contents are accessed: they may be iterated over through [`overlapping()`]. For
/// further details, see [Data Access](#data-access).
///
/// ## Construction
///
/// A `NestedContainmentList` stores [`RangeBounds`] in a nested structure to allow for fast querying.
/// Construction of a `NestedContainmentList` has temporal complexity *O(n log(n))*, where *n* is
/// the number of [`RangeBounds`] being stored. Both insertion and removal, with [`insert()`] and
/// [`remove()`] respectively, into a `NestedContainmentList` has temporal complexity *O(log(n))*,
/// where *n* is the number of [`RangeBounds`] currently stored.
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
/// When data is stored within a `NestedContainmentList`, it is typically accessed by querying for
/// [`RangeBounds`] overlapping another [`RangeBounds`], using the [`overlapping()`] method.
///
/// Both methods return a nested [`Iterator`] structure, with the difference being that access
/// through [`overlapping()`] only iterates over [`RangeBounds`] that overlap with the query
/// value. For details on the [`Iterator`]s returned by these methods, see the documentation for
/// [`Overlapping`].
///
/// Querying using [`overlapping()`] has temporal complexity *O(n + log(N))*, where *N* is the
/// number of [`RangeBounds`] stored, and *n* is the number of intervals overlapping with the query
/// value.
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
/// let mut sublist = nclist.overlapping(&(..));
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
/// [`Iterator`]: core::iter::Iterator
/// [`RangeBounds`]: core::ops::RangeBounds
#[derive(Debug)]
pub struct NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    elements: Vec<Element<R, T>>,
}

impl<R, T> NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
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
    /// let nclist = NestedContainmentList::<Range<usize>, usize>::new();
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
    /// The `NestedContainmentList` will be able to hold exactly `capacity` [`RangeBounds`] without
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
    /// let nclist = NestedContainmentList::<Range<usize>, usize>::with_capacity(10);
    /// assert_eq!(nclist.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.elements.capacity()
    }

    /// Returns an [`Overlapping`] [`Iterator`] over all elements within the
    /// `NestedContainmentList`.
    ///
    /// The [`Overlapping`] is a nested [`Iterator`] over all values contained in the
    /// `NestedContainmentList` that overlap with the `query` [`RangeBounds`]. All [`RangeBounds`]
    /// contained within other [`RangeBounds`] in the collection that also overlap with the `query`
    /// are accessed as nested [`Overlapping`]s under their outer-most values.
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
    /// [`Iterator`]: core::iter::Iterator
    pub fn overlapping<'a, S>(&'a self, query: &'a S) -> Overlapping<'a, R, S, T>
    where
        S: RangeBounds<T>,
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
    pub fn insert(&mut self, value: R) {
        // Direct insertion.
        let mut sublist_indices: Vec<usize> = Vec::with_capacity(self.elements.len());
        let mut indices = 0..self.elements.len();
        while let Some(index) = indices.next() {
            // If the value is ordered less than or equal to this element, then insert the value
            // before this element.
            match value.ordering(&self.elements[index].value) {
                Ordering::Less | Ordering::Equal => {
                    // Find the length of the value's sublist.
                    let mut len = 0;
                    for inner_index in index..self.elements.len() {
                        if Nestable::contains(&value, &self.elements[inner_index].value) {
                            len += 1;
                        } else {
                            break;
                        }
                    }
                    self.elements.insert(
                        index,
                        Element {
                            value,
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
            if Nestable::contains(&element.value, &value) {
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
            value,
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
        Q: RangeBounds<T>,
        R: Borrow<Q>,
    {
        // Direct removal.
        let mut sublist_indices: Vec<usize> = Vec::with_capacity(self.elements.len());
        let mut indices = 0..self.elements.len();
        while let Some(index) = indices.next() {
            match value.ordering(&self.elements[index].value) {
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
            if Nestable::contains(&element.value, value) {
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

impl<R, T> NestedContainmentList<R, T>
where
    R: RangeBounds<T> + Clone,
    T: Ord,
{
    /// Construct a `NestedContainmentList` from a slice.
    ///
    /// The elements within the slice are cloned into the new `NestedContainmentList`.
    ///
    /// This construction has temporal complexity of *O(n log(n))*, where *n* is the length of the
    /// slice. If you already have a collection of [`RangeBounds`] that you wish to use to create a
    /// `NestedContainmentList`, this is likely the most efficient way to do so.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    ///
    /// let nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 3..4, 5..7]);
    /// ```
    pub fn from_slice(values: &[R]) -> Self {
        // Sort the elements.
        let mut values = values.to_vec();
        values.sort_unstable_by(Nestable::ordering);

        // Depth-first construction.
        let mut elements: Vec<Element<R, T>> = Vec::with_capacity(values.len());
        let mut sublist_indices: Vec<usize> = Vec::with_capacity(values.len());
        for index in 0..values.len() {
            let value = values.remove(0);
            while !sublist_indices.is_empty() {
                let sublist_index = sublist_indices.pop().unwrap();

                if Nestable::contains(&elements[sublist_index].value, &value) {
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
                value,
                sublist_len: 0,
                _marker: PhantomData,
            });
        }

        // Clean up remaining sublist indices.
        for sublist_index in sublist_indices {
            let len = elements.len() - sublist_index - 1;
            elements[sublist_index].sublist_len = len;
        }

        NestedContainmentList { elements }
    }
}

impl<R, T> FromIterator<R> for NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    /// Construct a `NestedContainmentList` from an [`Iterator`].
    ///
    /// This construction has temporal complexity of *O(n log(n))*, where *n* is the length of the
    /// `Iterator`.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..5, 3..4, 2..4, 6..7]);
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = R>,
    {
        // Sort the elements.
        let mut values = iter.into_iter().collect::<Vec<_>>();
        values.sort_unstable_by(Nestable::ordering);

        // Depth-first construction.
        let mut elements: Vec<Element<R, T>> = Vec::with_capacity(values.len());
        let mut sublist_indices: Vec<usize> = Vec::with_capacity(values.len());
        for index in 0..values.len() {
            let value = values.remove(0);
            while !sublist_indices.is_empty() {
                let sublist_index = sublist_indices.pop().unwrap();

                if Nestable::contains(&elements[sublist_index].value, &value) {
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
                value,
                sublist_len: 0,
                _marker: PhantomData,
            });
        }

        // Clean up remaining sublist indices.
        for sublist_index in sublist_indices {
            let len = elements.len() - sublist_index - 1;
            elements[sublist_index].sublist_len = len;
        }

        NestedContainmentList { elements }
    }
}

impl<R, T> IntoIterator for NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    type Item = IterElement<R, T>;
    type IntoIter = Iter<R, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            elements: self.elements,
        }
    }
}

impl<R, T> Default for NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    /// Constructs a new, empty `NestedContainmentList`. Equivalent to [`new()`].
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::ops::Range;
    ///
    /// let nclist = NestedContainmentList::<Range<usize>, usize>::default();
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
    extern crate std as alloc;
    #[cfg(not(rust_1_36))]
    extern crate std as core;

    use alloc::vec;
    use core::{iter::FromIterator, ops::Range};
    use NestedContainmentList;

    #[test]
    fn new() {
        let nclist = NestedContainmentList::<Range<usize>, usize>::new();

        // Check that the sublist is empty.
        assert_none!(nclist.overlapping(&(..)).next());
    }

    #[test]
    fn default() {
        let nclist = NestedContainmentList::<Range<usize>, usize>::default();

        // Check that the sublist is empty.
        assert_none!(nclist.overlapping(&(..)).next());
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
        assert!(NestedContainmentList::<Range<usize>, usize>::new().is_empty());
    }

    #[test]
    fn is_not_empty() {
        assert!(!NestedContainmentList::from_slice(&[1..2]).is_empty());
    }

    #[test]
    fn capacity() {
        let nclist = NestedContainmentList::<Range<usize>, usize>::with_capacity(10);

        assert_eq!(nclist.capacity(), 10);
    }

    #[test]
    fn insert_on_empty() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);

        let mut sublist = nclist.overlapping(&(..));
        assert_eq!(sublist.next().unwrap().value, &(1..5));
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_contained() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);
        nclist.insert(2..4);

        let mut sublist = nclist.overlapping(&(..));
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

        let mut sublist = nclist.overlapping(&(..));
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

        let mut sublist = nclist.overlapping(&(..));
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

        let mut sublist = nclist.overlapping(&(..));
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

        let mut sublist = nclist.overlapping(&(..));
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

        let mut sublist = nclist.overlapping(&(..));
        assert_eq!(sublist.next().unwrap().value, &(1..5));
        assert_eq!(sublist.next().unwrap().value, &(6..10));
        assert_none!(sublist.next());
    }

    #[test]
    fn insert_into_second_sublist() {
        let mut nclist = NestedContainmentList::from_slice(&[1..4, 2..3, 5..9]);

        nclist.insert(6..8);

        let mut sublist = nclist.overlapping(&(..));
        assert_eq!(sublist.next().unwrap().value, &(1..4));
        let second_element = sublist.next().unwrap();
        assert_eq!(second_element.value, &(5..9));
        assert_eq!(second_element.sublist().next().unwrap().value, &(6..8));
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_from_empty() {
        let mut nclist = NestedContainmentList::<Range<usize>, usize>::new();

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

        let mut sublist = nclist.overlapping(&(..));
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_containing() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 0..6]);

        assert!(nclist.remove(&(0..6)));

        let mut sublist = nclist.overlapping(&(..));
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_contained_and_containing() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4, 3..4]);

        assert!(nclist.remove(&(2..4)));

        let mut sublist = nclist.overlapping(&(..));
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

        let mut sublist = nclist.overlapping(&(..));
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

    #[test]
    fn from_iter() {
        let nclist = NestedContainmentList::from_iter(vec![1..5, 3..4, 2..4, 6..7]);

        let mut sublist = nclist.overlapping(&(..));
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

    #[test]
    fn into_iter() {
        let nclist = NestedContainmentList::from_iter(vec![1..5, 3..4, 2..4, 6..7]);

        let mut iter = nclist.into_iter();
        let first_sublist_element = iter.next().unwrap();
        assert_eq!(first_sublist_element.value, 1..5);
        let mut first_sublist_element_sublist = first_sublist_element.sublist();
        let second_sublist_element = first_sublist_element_sublist.next().unwrap();
        assert_eq!(second_sublist_element.value, 2..4);
        let mut second_sublist_element_sublist = second_sublist_element.sublist();
        assert_eq!(second_sublist_element_sublist.next().unwrap().value, 3..4);
        assert_none!(first_sublist_element_sublist.next());
        assert_eq!(iter.next().unwrap().value, 6..7);
        assert_none!(iter.next());
    }
}

//! Implementation of a Nested Containment List.
//!
//! A Nested Containment List is a data structure for storing types that implement the
//! [`core::ops::RangeBounds`] trait. Elements stored in a [`NestedContainmentList`] are stored in a
//! nested structure to allow for easy querying using other `RangeBounds` queries.
//!
//! ## Construction
//!
//! Construction of [`NestedContainmentList`]s can be done using either the [`new()`] or
//! [`from_iter()`] methods. Construction from `from_iter()` has temporal complexity
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
//! use std::iter::FromIterator;
//!
//! let nclist = NestedContainmentList::from_iter(vec![1..5, 2..4, 5..7]);
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
//! use std::iter::FromIterator;
//!
//! let nclist = NestedContainmentList::from_iter(vec![1..5, 2..4, 6..7]);
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
//! [`from_iter()`]: NestedContainmentList::from_iter()
//! [`new()`]: NestedContainmentList::new()
//! [`overlapping()`]: NestedContainmentList::overlapping()
//! [`Iterator`]: core::iter::Iterator
//! [`Iterator::flatten()`]: core::iter::Iterator::flatten()
//! [`RangeBounds`]: core::ops::RangeBounds

#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]
#![allow(clippy::doc_markdown, clippy::redundant_pub_crate)]
#![cfg_attr(rustc_1_36, no_std)]

#[cfg(rustc_1_36)]
extern crate alloc;
#[cfg(not(rustc_1_36))]
extern crate std as alloc;
#[cfg(not(rustc_1_36))]
extern crate std as core;

mod nestable;

use crate::nestable::Nestable;
use alloc::{borrow::ToOwned, collections::VecDeque, vec::Vec};
use core::{
    borrow::Borrow,
    cmp::{min, Ordering},
    hint::unreachable_unchecked,
    iter::{once, Chain, FromIterator, FusedIterator, Iterator, Once},
    marker::PhantomData,
    mem,
    num::NonZeroUsize,
    ops::RangeBounds,
};

/// Internal element, stored within the `NestedContainmentList` and its associated `Iterators`.
///
/// The values in here are more directly used in the external API's `OverlappingElement` and
/// `IterElement` types.
#[derive(Debug)]
struct Element<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    value: R,
    sublist_len: usize,
    // Direct parent's offset, if the element has a parent. This is the absolute distance between
    // this element and its direct parent element.
    parent_offset: Option<NonZeroUsize>,
    _marker: PhantomData<T>,
}

/// An element contained within an [`Overlapping`].
///
/// This element allows access to its contained value `I` and its sub-elements which also overlap
/// with the query `S`.
///
/// An `OverlappingElement` is usually obtained from iterating over an `Overlapping`.
///
/// # Example
/// ```
/// use nested_containment_list::NestedContainmentList;
/// use std::iter::FromIterator;
///
/// let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3]);
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
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..5, 2..3, 3..4]);
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
    #[must_use]
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

    /// Returns an [`Iterator`] over this element's `value`, followed by its `sublist()` elements
    /// that overlap with the query `S`.
    ///
    /// This is useful if you want to iterate over all values including the enclosing value.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3]);
    /// let mut overlapping = nclist.overlapping(&(2..5));
    /// let first_element = overlapping.next().unwrap();
    /// let mut first_element_iter = first_element.into_iter();
    ///
    /// assert_eq!(first_element_iter.next().unwrap().value, &(1..4));
    /// assert_eq!(first_element_iter.next().unwrap().value, &(2..3));
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
    #[must_use]
    fn into_iter(self) -> Self::IntoIter {
        once(Self {
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
/// use std::iter::FromIterator;
///
/// let nclist = NestedContainmentList::from_iter(vec![1..5, 2..3, 2..4, 5..7]);
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
#[derive(Debug)]
pub struct Overlapping<'a, R, S, T>
where
    R: RangeBounds<T> + 'a,
    S: RangeBounds<T> + 'a,
    T: Ord + 'a,
{
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
        Overlapping { elements, query }
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
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..5]);
    /// let query = 2..3;
    /// let mut overlapping = nclist.overlapping(&query);
    ///
    /// assert_eq!(overlapping.next().unwrap().value, &(1..5));
    /// assert!(overlapping.next().is_none());
    /// ```
    ///
    /// [`sublist()`]: OverlappingElement::sublist()
    fn next(&mut self) -> Option<Self::Item> {
        while !self.elements.is_empty() {
            let element = unsafe {
                // SAFETY: Just checked that `self.elements` has at least one value.
                self.elements.get_unchecked(0)
            };
            if element.value.overlapping(self.query) {
                let sublist_elements = unsafe {
                    // SAFETY: `element.sublist_len` is invariantly guaranteed to only advance to a
                    // point within the bounds of `elements`. Therefore, this will never go out of
                    // bounds.
                    self.elements.get_unchecked(1..=element.sublist_len)
                };
                self.elements = unsafe {
                    // SAFETY: `element.sublist_len` will invariantly always be less than
                    // `elements.len()`, since the length of a sublist of an element never includes
                    // itself. Therefore, `element.sublist_len + 1 <= elements.len()`.
                    self.elements.get_unchecked((element.sublist_len + 1)..)
                };
                return Some(OverlappingElement {
                    value: &element.value,
                    sublist_elements,
                    query: self.query,
                    _marker: PhantomData,
                });
            }
            match self.query.ordering(&element.value) {
                // Have not yet chopped off the front elements.
                Ordering::Greater | Ordering::Equal => {
                    // Custom version of a binary search.
                    let mut index = 0;
                    let mut size = self.elements.len();
                    if size != 0 {
                        while size > 1 {
                            let mut half = size / 2;
                            let mut mid = index + half;

                            let mid_element = loop {
                                let mid_element = unsafe {
                                    // SAFETY: The maximum `mid` can be is bound above by
                                    // `size / 2 + size / 4 + size / 8 + ...`
                                    self.elements.get_unchecked(mid)
                                };
                                if let Some(offset) = mid_element.parent_offset {
                                    if offset.get() > (mid - index) {
                                        // The parent element exists outside of the scope of this
                                        // iterator.
                                        break mid_element;
                                    }
                                    mid -= offset.get();
                                } else {
                                    // This is the top-most element, since it has no parent offset.
                                    break mid_element;
                                }
                            };

                            index = match if mid_element.value.overlapping(self.query) {
                                Ordering::Greater
                            } else {
                                mid_element.value.ordering(self.query)
                            } {
                                Ordering::Greater => {
                                    half += mid_element.sublist_len;
                                    index
                                }
                                Ordering::Less | Ordering::Equal => mid,
                            };
                            size -= half;
                        }
                        let index_element = unsafe {
                            // SAFETY: Since `index` is obtained from the above binary search, where
                            // its max possible value is `size / 2 + size / 4 + size / 8 + ...`.
                            // Therefore it will be within the bounds of `self.elements`.
                            self.elements.get_unchecked(index)
                        };
                        match if index_element.value.overlapping(self.query) {
                            Ordering::Greater
                        } else {
                            index_element.value.ordering(self.query)
                        } {
                            Ordering::Less => {
                                index += 1;
                            }
                            Ordering::Greater | Ordering::Equal => {}
                        }
                    }
                    self.elements = unsafe {
                        // SAFETY: Since `index` is obtained from the above binary search, where its
                        // max possible value is `size / 2 + size / 4 + size / 8 + ... + 1`.
                        // Therefore it will be within the bounds of `self.elements`, being at most
                        // `self.elements.len()`.
                        self.elements.get_unchecked(index..)
                    };
                }
                // Have already emitted every overlapping element.
                Ordering::Less => {
                    self.elements = &[];
                }
            }
        }

        None
    }

    /// Consumes the iterator, returning the last element.
    ///
    /// This method directly uses `next_back()` to jump straight to the end of the iterator.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..2, 3..4, 5..6]);
    ///
    /// let mut overlapping = nclist.overlapping(&(1..4));
    /// assert_eq!(overlapping.last().unwrap().value, &(3..4));
    /// ```
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    /// Returns the bounds on the remaining length of the iterator.
    ///
    /// The lower bound will always be `1` unless the iterator has been exhausted, in which case it
    /// will be `0`. The upper bound will always be provided and will be the total count of
    /// remaining elements to be iterated over, including those which are nested and those which may
    /// not actually overlap with the query.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..5, 2..5, 6..7]);
    /// let query = 2..4;
    /// let overlapping = nclist.overlapping(&query);
    ///
    /// assert_eq!(overlapping.size_hint(), (1, Some(3)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        (min(1, self.elements.len()), Some(self.elements.len()))
    }
}

impl<'a, R, S, T> DoubleEndedIterator for Overlapping<'a, R, S, T>
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        // while !self.elements.is_empty() {
        //     let last_element = unsafe {
        //         self.elements.get_unchecked(self.elements.len() - 1)
        //     };
        //     if last_element.overlapping(self.query) || match last_element.ordering(self.query) {
        //         Ordering::Less | Ordering::Equal => true,
        //         Ordering::Greater => false,
        //     } {

        //     }
        // }

        while !self.elements.is_empty() {
            let mut index = self.elements.len() - 1;

            // Find top level parent element.
            let element = loop {
                let parent_element = unsafe {
                    // SAFETY: `index` will always be less than self.elements.len(), since it is set
                    // to one less than it, and it only ever decreases.
                    self.elements.get_unchecked(index)
                };
                if let Some(offset) = parent_element.parent_offset {
                    if offset.get() > index {
                        // The parent element exists outside of the scope of this iterator.
                        break parent_element;
                    }
                    index -= offset.get();
                } else {
                    // This is the top-most element, since it has no parent offset.
                    break parent_element;
                }
            };

            // Check whether the parent element overlaps with query.
            if element.value.overlapping(self.query) {
                let sublist_elements = unsafe {
                    // SAFETY: `index` is guaranteed to be at most `self.elements.len() - 1`, so
                    // this indexing will never be out of bounds.
                    self.elements.get_unchecked((index + 1)..)
                };
                self.elements = unsafe {
                    // SAFETY: `index` is guaranteed to be at most `self.elements.len() - 1`, so
                    // this indexing will never be out of bounds.
                    self.elements.get_unchecked(..index)
                };
                return Some(OverlappingElement {
                    value: &element.value,
                    sublist_elements,
                    query: self.query,
                    _marker: PhantomData,
                });
            }
            // Truncate the elements, since they don't overlap.
            self.elements = unsafe {
                // SAFETY: `index` is guaranteed to be at most `self.elements.len() - 1`, so
                // this indexing will never be out of bounds.
                self.elements.get_unchecked(..index)
            };
        }

        None
    }
}

impl<'a, R, S, T> FusedIterator for Overlapping<'a, R, S, T>
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
}

/// An element obtained from [`Iter`].
///
/// This element allows access to its `value`, as well as providing an `Iterator` over all values
/// nested within `value` through the `sublist()` method.
///
/// # Example
/// ```
/// use nested_containment_list::NestedContainmentList;
/// use std::iter::FromIterator;
///
/// let nclist = NestedContainmentList::from_iter(vec![1..2]);
///
/// let mut iter = nclist.into_iter();
/// assert_eq!(iter.next().unwrap().value, 1..2);
/// ```
#[derive(Debug)]
pub struct IterElement<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    pub value: R,
    sublist_elements: VecDeque<Element<R, T>>,
}

impl<R, T> IterElement<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    /// Returns an [`Iter`] [`Iterator`] over this element's sublist.
    ///
    /// Note that this method consumes the `IterElement`.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3]);
    ///
    /// let mut iter = nclist.into_iter();
    /// let mut sublist = iter.next().unwrap().sublist();
    /// assert_eq!(sublist.next().unwrap().value, 2..3);
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
    pub fn sublist(self) -> Iter<R, T> {
        Iter {
            elements: self.sublist_elements,
        }
    }
}

impl<R, T> IntoIterator for IterElement<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    type Item = Self;
    type IntoIter = Chain<Once<Self::Item>, Iter<R, T>>;

    /// Returns an [`Iterator`] over this element's `value`, followed by its `sublist()`.
    ///
    /// This is useful if you want to iterate over all values including the enclosing value.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3]);
    /// let mut iter = nclist.into_iter();
    /// let first_element = iter.next().unwrap();
    /// let mut first_element_iter = first_element.into_iter();
    ///
    /// assert_eq!(first_element_iter.next().unwrap().value, 1..4);
    /// assert_eq!(first_element_iter.next().unwrap().value, 2..3);
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
    fn into_iter(self) -> Self::IntoIter {
        once(Self {
            value: self.value,
            sublist_elements: VecDeque::new(),
        })
        .chain(Iter {
            elements: self.sublist_elements,
        })
    }
}

/// An [`Iterator`] over all elements in a [`NestedContainmentList`].
///
/// This `Iterator` proceeds in a nested fashion, meaning it only yields the outer-most nested
/// elements. To access the inner elements, call [`sublist()`] on the outer elements.
///
/// # Example
///
/// ```
/// use nested_containment_list::NestedContainmentList;
/// use std::iter::FromIterator;
///
/// let nclist = NestedContainmentList::from_iter(vec![1..2]);
///
/// let mut iter = nclist.into_iter();
/// assert_eq!(iter.next().unwrap().value, 1..2);
/// ```
///
/// [`Iterator`]: core::iter::Iterator
/// [`sublist()`]: IterElement::sublist()
#[derive(Debug)]
pub struct Iter<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    elements: VecDeque<Element<R, T>>,
}

impl<R, T> Iterator for Iter<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    type Item = IterElement<R, T>;

    /// Yield the next outer-most element.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..2]);
    ///
    /// let mut iter = nclist.into_iter();
    /// assert_eq!(iter.next().unwrap().value, 1..2);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        if self.elements.is_empty() {
            return None;
        }

        let element = self.elements.pop_front().unwrap();
        let remaining_elements = self.elements.split_off(element.sublist_len);

        Some(IterElement {
            value: element.value,
            sublist_elements: mem::replace(&mut self.elements, remaining_elements),
        })
    }

    /// Consumes the iterator, returning the last element.
    ///
    /// This method directly uses `next_back()` to jump straight to the end of the iterator.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..2, 3..4]);
    ///
    /// let mut iter = nclist.into_iter();
    /// assert_eq!(iter.last().unwrap().value, 3..4);
    /// ```
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    /// Returns the bounds on the remaining length of the iterator.
    ///
    /// The lower bound will always be `1` unless the iterator has been exhausted, in which case it
    /// will be `0`. The upper bound will always be provided and will be the total count of
    /// remaining elements to be iterated over, including those which are nested.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..5, 2..5, 6..7]);
    /// let iter = nclist.into_iter();
    ///
    /// assert_eq!(iter.size_hint(), (1, Some(3)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        (min(1, self.elements.len()), Some(self.elements.len()))
    }
}

impl<R, T> DoubleEndedIterator for Iter<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.elements.is_empty() {
            return None;
        }

        let mut sublist_elements = VecDeque::new();
        let element = loop {
            let parent_element = self.elements.pop_back().unwrap();
            if let Some(offset) = parent_element.parent_offset {
                if offset.get() > self.elements.len() {
                    // The parent element exists outside of the scope of this iterator.
                    break parent_element;
                }
                sublist_elements.push_front(parent_element);
                self.elements
                    .split_off(self.elements.len() - offset.get() + 1)
                    .into_iter()
                    .for_each(|element| sublist_elements.push_front(element));
            } else {
                // This is the top-most element, since it has no parent offset.
                break parent_element;
            }
        };

        Some(IterElement {
            value: element.value,
            sublist_elements,
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
/// use std::iter::FromIterator;
///
/// let mut nclist = NestedContainmentList::from_iter(vec![1..5, 2..4, 5..7]);
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
/// use std::iter::FromIterator;
///
/// let mut nclist = NestedContainmentList::from_iter(vec![1..5, 2..4, 5..7]);
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
    #[must_use]
    pub fn new() -> Self {
        Self {
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
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
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
    #[must_use]
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
    #[must_use]
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
    #[must_use]
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
    /// use std::iter::FromIterator;
    ///
    /// let nclist = NestedContainmentList::from_iter(vec![1..5, 2..3, 2..4, 5..7]);
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
    #[must_use]
    pub fn overlapping<'a, S>(&'a self, query: &'a S) -> Overlapping<'a, R, S, T>
    where
        S: RangeBounds<T>,
    {
        Overlapping::new(&self.elements, query)
    }

    fn insert_at(&mut self, index: usize, value: R) {
        // Find the length of the value's sublist.
        let mut len = 0;
        let mut inner_indices = index..self.elements.len();
        while let Some(inner_index) = inner_indices.next() {
            let inner_element = unsafe {
                // SAFETY: `inner_index` is guaranteed to be less than `self.elements.len()`, due to
                // being obtained from the range `index..self.elements.len()`.
                self.elements.get_unchecked_mut(inner_index)
            };
            if Nestable::contains(&value, &inner_element.value) {
                len += inner_element.sublist_len + 1;
                inner_element.parent_offset = Some(unsafe {
                    // SAFETY: `inner_index` will never be less than `index`, and adding one to the
                    // value will guarantee it is not zero.
                    NonZeroUsize::new_unchecked(inner_index - index + 1)
                });
                if inner_element.sublist_len > 0 {
                    inner_indices.nth(inner_element.sublist_len - 1);
                }
            } else {
                break;
            }
        }

        // Handle parent elements.
        let mut direct_parent_index = None;
        if index > 0 {
            let mut parent_index = index - 1;
            loop {
                let parent_element = unsafe { self.elements.get_unchecked_mut(parent_index) };
                let current_parent_offset = parent_element.parent_offset;
                if Nestable::contains(&parent_element.value, &value) {
                    // Store the value's direct parent.
                    if direct_parent_index.is_none() {
                        direct_parent_index = Some(parent_index);
                    }
                    // Lengthen the parent element's sublist, since value is being added to it.
                    let current_parent_sublist_len = parent_element.sublist_len;
                    parent_element.sublist_len += 1;
                    // Lengthen the parent offset of every direct child element after the inserted
                    // element.
                    let mut child_index = index;
                    while child_index <= parent_index + current_parent_sublist_len {
                        let child_element = unsafe {
                            // SAFETY: `child_index` will invariantly be within the bounds of
                            // `self.elements`, since it is within the parent element's sublist.
                            self.elements.get_unchecked_mut(child_index)
                        };
                        child_element.parent_offset = Some(unsafe {
                            // SAFETY: `child_element` is guaranteed to have a `parent_offset`, and
                            // therefore adding one to its value will also be non-zero.
                            NonZeroUsize::new_unchecked(
                                child_element.parent_offset.unwrap().get() + 1,
                            )
                        });
                        child_index += child_element.sublist_len + 1;
                    }
                }
                // Advance to next parent element.
                if let Some(offset) = current_parent_offset {
                    parent_index -= offset.get();
                } else {
                    break;
                }
            }
        }

        // Insert the element.
        self.elements.insert(
            index,
            Element {
                value,
                sublist_len: len,
                parent_offset: direct_parent_index.map(|parent_index| unsafe {
                    // SAFETY: `index` is always guaranteed to be strictly greater than
                    // `parent_index`, as `parent_index` is at most `index - 1`.
                    NonZeroUsize::new_unchecked(index - parent_index)
                }),
                _marker: PhantomData,
            },
        );
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
        // Binary search insertion.
        let index = match self
            .elements
            .binary_search_by(|element| element.value.ordering(&value))
        {
            Ok(index) | Err(index) => index,
        };

        self.insert_at(index, value);
    }

    /// Remove the specified value from the `NestedContainmentList`.
    ///
    /// This removal preserves the internal nested structure of the container, and has temporal
    /// complexity *O(log(n))*.
    ///
    /// # Example
    /// ```
    /// use nested_containment_list::NestedContainmentList;
    /// use std::iter::FromIterator;
    ///
    /// let mut nclist = NestedContainmentList::from_iter(vec![1..5, 2..4, 3..4]);
    /// assert!(nclist.remove(&(2..4)));
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        Q: RangeBounds<T>,
        R: Borrow<Q>,
    {
        // Binary search removal.
        match self
            .elements
            .binary_search_by(|element| element.value.ordering(Borrow::borrow(value)))
        {
            Ok(index) => {
                // Correct all child elements' parent_offset values.
                let removed_element = unsafe {
                    // SAFETY: Since `index` was obtained from the binary search, we can be sure it
                    // is within the bounds of `self.elements`.
                    self.elements.get_unchecked(index)
                };
                let removed_element_sublist_len = removed_element.sublist_len;
                let removed_element_parent_offset = removed_element.parent_offset;
                let mut child_index = index + 1;
                while child_index <= index + removed_element_sublist_len {
                    let child_element = unsafe {
                        // SAFETY: `child_index` is guaranteed to be less than
                        // `self.elements.len()`, as it is less than `index +
                        // removed_element_sublist_len` which is invariantly guaranteed to be within
                        // the bounds of `self.elements`.
                        self.elements.get_unchecked_mut(child_index)
                    };
                    child_element.parent_offset =
                        removed_element_parent_offset.map(|offset| unsafe {
                            // SAFETY: Both `offset` and `child_element.parent_offset` are
                            // guaranteed to be non-zero, so subtracting one from their sum is also
                            // guaranteed to be non-zero.
                            NonZeroUsize::new_unchecked(
                                offset.get() + child_element.parent_offset.unwrap().get() - 1,
                            )
                        });
                    child_index += child_element.sublist_len + 1;
                }

                // Shorten the sublist of every parent element.
                if let Some(offset) = removed_element_parent_offset {
                    let mut parent_index = index - offset.get();
                    loop {
                        let parent_element = unsafe {
                            // SAFETY: `parent_index` is invariantly guaranteed to be within the
                            // bounds of `self.elements`.
                            self.elements.get_unchecked_mut(parent_index)
                        };
                        parent_element.sublist_len -= 1;
                        if let Some(parent_offset) = parent_element.parent_offset {
                            parent_index -= parent_offset.get();
                        } else {
                            break;
                        }
                    }
                }

                // Remove the element.
                self.elements.remove(index);

                true
            }
            Err(_) => false,
        }
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
                let sublist_index = sublist_indices.pop().unwrap_or_else(|| {
                    if cfg!(debug_assertions) {
                        unreachable!()
                    } else {
                        unsafe { unreachable_unchecked() }
                    }
                });

                let mut sublist_element = unsafe {
                    // SAFETY: `sublist_index` is always guaranteed to be less than the current
                    // `index`, and since we push a new element with every `index`, `sublist_index`
                    // is guaranteed to be within the bounds of `elements`.
                    elements.get_unchecked_mut(sublist_index)
                };
                if Nestable::contains(&sublist_element.value, &value) {
                    // We are within the previous sublist.
                    sublist_indices.push(sublist_index);
                    break;
                }
                // We are no longer within the previous sublist.
                let len = index - sublist_index - 1;
                sublist_element.sublist_len = len;
            }

            elements.push(Element {
                value,
                sublist_len: 0,
                parent_offset: sublist_indices.last().map(|sublist_index| unsafe {
                    // SAFETY: `index` is always guaranteed to be strictly greater than
                    // `sublist_index`, as `sublist_index` is obtained from `sublist_indices`, which
                    // only consists of values from `0..values.len()`, which is ascending, and
                    // `index` hasn't yet been pushed to `sublist_indices`.
                    NonZeroUsize::new_unchecked(index - sublist_index)
                }),
                _marker: PhantomData,
            });
            sublist_indices.push(index);
        }

        // Clean up remaining sublist indices.
        for sublist_index in sublist_indices {
            let len = elements.len() - sublist_index - 1;
            unsafe {
                // SAFETY: Since we have iterated through every `index`, then `elements` is the same
                // length as `values`. Since each `sublist_index` is an index less than
                // `values.len()`, each `sublist_index` will always be within the bounds of
                // `elements`.
                elements.get_unchecked_mut(sublist_index)
            }
            .sublist_len = len;
        }

        Self { elements }
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
            elements: VecDeque::from(self.elements),
        }
    }
}

impl<R, T> Extend<R> for NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = R>,
    {
        // Sort the new values.
        let mut values: Vec<_> = iter.into_iter().collect();
        values.sort_unstable_by(Nestable::ordering);

        let mut index = 0;
        for value in values {
            let prev_index = index;
            // Each subsequent value must belong after the previously inserted value.
            index = match self.elements[index..]
                .binary_search_by(|element| element.value.ordering(&value))
            {
                Ok(index) | Err(index) => index,
            };
            self.insert_at(prev_index + index, value);
            // The just-inserted value doesn't need to be included in the next iteration's search.
            index += 1;
        }
    }
}

impl<R, T> From<Vec<R>> for NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    #[inline]
    fn from(v: Vec<R>) -> Self {
        Self::from_iter(v)
    }
}

impl<R, T> From<&'_ [R]> for NestedContainmentList<R, T>
where
    R: RangeBounds<T> + Clone,
    T: Ord,
{
    #[inline]
    fn from(s: &[R]) -> Self {
        Self::from_iter(s.to_owned())
    }
}

#[cfg(rustc_1_41)]
/// Due to orphaning rules, this implementation is only available in `rustc 1.41.0` and above. On
/// earlier `rustc` versions, a direct implementation of [`Into`] is provided instead, so that the
/// following example will still work:
///
/// ```
/// use nested_containment_list::NestedContainmentList;
///
/// let nclist = NestedContainmentList::from(vec![2..3, 1..4, 3..5]);
/// let vec: Vec<_> = nclist.into();
/// ```
///
/// See
/// [Implementing `Into` for conversions to external types in old versions of Rust](https://doc.rust-lang.org/nightly/core/convert/trait.Into.html#implementing-into-for-conversions-to-external-types-in-old-versions-of-rust)
/// for more information.
///
/// [`Into`]: core::convert::Into
impl<R, T> From<NestedContainmentList<R, T>> for Vec<R>
where
    R: RangeBounds<T>,
    T: Ord,
{
    #[inline]
    fn from(nclist: NestedContainmentList<R, T>) -> Self {
        nclist
            .elements
            .into_iter()
            .map(|element| element.value)
            .collect()
    }
}

#[cfg(not(rustc_1_41))]
impl<R, T> Into<Vec<R>> for NestedContainmentList<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    #[inline]
    fn into(self) -> Vec<R> {
        self.elements
            .into_iter()
            .map(|element| element.value)
            .collect()
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
    use crate::NestedContainmentList;
    use alloc::{vec, vec::Vec};
    use claim::assert_none;
    use core::{iter::FromIterator, ops::Range};

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
        assert!(!NestedContainmentList::from_iter(vec![1..2]).is_empty());
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
        let mut nclist = NestedContainmentList::from_iter(vec![1..4, 2..3, 5..9]);

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
        let mut nclist = NestedContainmentList::from_iter(vec![1..5]);

        assert!(nclist.remove(&(1..5)));
    }

    #[test]
    fn remove_not_found() {
        let mut nclist = NestedContainmentList::from_iter(vec![1..5, 6..7]);

        assert!(!nclist.remove(&(1..4)));
    }

    #[test]
    fn remove_contained() {
        let mut nclist = NestedContainmentList::from_iter(vec![1..5, 2..4]);

        assert!(nclist.remove(&(2..4)));

        let mut sublist = nclist.overlapping(&(..));
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_containing() {
        let mut nclist = NestedContainmentList::from_iter(vec![1..5, 0..6]);

        assert!(nclist.remove(&(0..6)));

        let mut sublist = nclist.overlapping(&(..));
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(sublist.next());
    }

    #[test]
    fn remove_contained_and_containing() {
        let mut nclist = NestedContainmentList::from_iter(vec![1..5, 2..4, 3..4]);

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
        let mut nclist = NestedContainmentList::from_iter(vec![1..5, 2..4, 6..7]);

        assert!(nclist.remove(&(6..7)));
    }

    #[test]
    fn overlapping() {
        let nclist = NestedContainmentList::from_iter(vec![1..5, 3..4, 2..4, 6..7]);

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
        let nclist = NestedContainmentList::from_iter(vec![1..2, 3..4]);

        let query = 3..4;
        let mut overlapping = nclist.overlapping(&query);

        let first_element = overlapping.next().unwrap();
        assert_eq!(first_element.value, &(3..4));
        assert_none!(first_element.sublist().next());
        assert_none!(overlapping.next());
    }

    #[test]
    fn overlapping_contained() {
        let nclist = NestedContainmentList::from_iter(vec![1..5]);

        let query = 2..3;
        let mut overlapping = nclist.overlapping(&query);

        let first_element = overlapping.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_none!(first_element.sublist().next());
        assert_none!(overlapping.next());
    }

    #[test]
    fn overlapping_starts_at_topmost_element() {
        let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3]);
        let query = 2..4;
        let mut overlapping = nclist.overlapping(&query);

        let overlapping_element = overlapping.next().unwrap();
        assert_eq!(overlapping_element.value, &(1..4));

        let inner_overlapping_element = overlapping_element.sublist().next().unwrap();
        assert_eq!(inner_overlapping_element.value, &(2..3));
    }

    #[test]
    fn overlapping_stops_early() {
        let nclist = NestedContainmentList::from_iter(vec![1..4, 2..5]);
        let query = 1..2;
        let mut overlapping = nclist.overlapping(&query);

        assert_eq!(overlapping.next().unwrap().value, &(1..4));
        assert_none!(overlapping.next());
    }

    #[test]
    fn overlapping_with_inner_not_overlapping() {
        let nclist = NestedContainmentList::from(vec![1..5, 1..2, 2..3, 4..5, 0..0]);
        let mut overlapping = nclist.overlapping(&(2..3));

        let element = overlapping.next().unwrap();
        assert_eq!(element.value, &(1..5));
        assert_eq!(element.sublist().next().unwrap().value, &(2..3));
    }

    #[test]
    fn overlapping_last() {
        let nclist = NestedContainmentList::from_iter(vec![1..2, 2..5, 3..4, 6..7]);

        let last = nclist.overlapping(&(1..4)).last().unwrap();

        assert_eq!(last.value, &(2..5));
        assert_eq!(last.sublist().next().unwrap().value, &(3..4));
    }

    #[test]
    fn overlapping_size_hint() {
        let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3, 4..7]);
        let query = 1..3;
        let overlapping = nclist.overlapping(&query);

        assert_eq!(overlapping.size_hint(), (1, Some(3)));
    }

    #[test]
    fn overlapping_size_hint_empty() {
        let nclist = NestedContainmentList::<Range<usize>, usize>::new();
        let query = 1..3;
        let overlapping = nclist.overlapping(&query);

        assert_eq!(overlapping.size_hint(), (0, Some(0)));
    }

    #[test]
    fn overlapping_size_hint_after_iterating() {
        let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3, 4..7]);
        let query = 1..5;
        let mut overlapping = nclist.overlapping(&query);
        overlapping.next();

        assert_eq!(overlapping.size_hint(), (1, Some(1)));
    }

    #[test]
    fn overlapping_element_into_iter() {
        let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3]);
        let mut overlapping = nclist.overlapping(&(2..5));
        let first_element = overlapping.next().unwrap();
        let mut first_element_iter = first_element.into_iter();

        assert_eq!(first_element_iter.next().unwrap().value, &(1..4));
        assert_eq!(first_element_iter.next().unwrap().value, &(2..3));
    }

    #[test]
    fn overlapping_next_back() {
        let nclist = NestedContainmentList::from_iter(vec![0..1, 1..2, 2..5, 2..4, 6..7]);
        let mut overlapping = nclist.overlapping(&(1..4));

        let second_element = overlapping.next_back().unwrap();
        assert_eq!(second_element.value, &(2..5));
        let mut second_element_sublist = second_element.sublist();
        assert_eq!(second_element_sublist.next_back().unwrap().value, &(2..4));
        assert_none!(second_element_sublist.next_back());
        let first_element = overlapping.next_back().unwrap();
        assert_eq!(first_element.value, &(1..2));
        assert_none!(first_element.sublist().next_back());
        assert_none!(overlapping.next_back());
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

    #[test]
    fn iter_last() {
        let nclist = NestedContainmentList::from_iter(vec![1..2, 2..5, 3..4]);

        let last = nclist.into_iter().last().unwrap();

        assert_eq!(last.value, 2..5);
        assert_eq!(last.sublist().next().unwrap().value, 3..4);
    }

    #[test]
    fn iter_size_hint() {
        let nclist = NestedContainmentList::from_iter(vec![1..5, 2..5, 6..7]);
        let iter = nclist.into_iter();

        assert_eq!(iter.size_hint(), (1, Some(3)));
    }

    #[test]
    fn iter_size_hint_empty() {
        let nclist = NestedContainmentList::<Range<usize>, usize>::new();
        let iter = nclist.into_iter();

        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn iter_size_hint_after_iterating() {
        let nclist = NestedContainmentList::from_iter(vec![1..5, 2..5, 6..7]);
        let mut iter = nclist.into_iter();
        iter.next();

        assert_eq!(iter.size_hint(), (1, Some(1)));
    }

    #[test]
    fn iter_next_back() {
        let nclist = NestedContainmentList::from_iter(vec![1..5, 3..4, 2..4, 6..7]);
        let mut iter = nclist.into_iter();

        let second_element = iter.next_back().unwrap();
        assert_eq!(second_element.value, 6..7);
        assert_none!(second_element.sublist().next_back());
        let first_element = iter.next_back().unwrap();
        assert_eq!(first_element.value, 1..5);
        let mut first_element_sublist = first_element.sublist();
        let second_sublist_element = first_element_sublist.next_back().unwrap();
        assert_eq!(second_sublist_element.value, 2..4);
        let mut second_sublist_element_sublist = second_sublist_element.sublist();
        assert_eq!(
            second_sublist_element_sublist.next_back().unwrap().value,
            3..4
        );
        assert_none!(second_sublist_element_sublist.next_back());
        assert_none!(first_element_sublist.next_back());
        assert_none!(iter.next_back());
    }

    #[test]
    fn iter_element_into_iter() {
        let nclist = NestedContainmentList::from_iter(vec![1..4, 2..3]);
        let mut iter = nclist.into_iter();
        let first_element = iter.next().unwrap();
        let mut first_element_iter = first_element.into_iter();

        assert_eq!(first_element_iter.next().unwrap().value, 1..4);
        assert_eq!(first_element_iter.next().unwrap().value, 2..3);
    }

    #[test]
    fn extend() {
        let mut nclist = NestedContainmentList::from(vec![2..3, 1..4, 7..8]);

        nclist.extend(vec![0..5, 6..7, 7..9, 10..11]);

        assert_eq!(
            Into::<Vec<_>>::into(nclist),
            vec![0..5, 1..4, 2..3, 6..7, 7..9, 7..8, 10..11]
        );
    }

    #[test]
    fn from_vec() {
        let nclist = NestedContainmentList::from(vec![2..3, 1..4, 5..6]);

        assert_eq!(Into::<Vec<_>>::into(nclist), vec![1..4, 2..3, 5..6]);
    }

    #[test]
    fn from_slice() {
        let slice = &[2..3, 1..4, 5..6][..];
        let nclist = NestedContainmentList::from(slice);
        let mut iter = nclist.into_iter();

        let first_element = iter.next().unwrap();
        assert_eq!(first_element.value, 1..4);
        assert_eq!(first_element.sublist().next().unwrap().value, 2..3);
        let second_element = iter.next().unwrap();
        assert_eq!(second_element.value, 5..6);
    }

    #[test]
    fn into_vec() {
        let vec: Vec<_> = NestedContainmentList::from_iter(vec![2..3, 1..4, 5..6]).into();

        let nclist: NestedContainmentList<_, _> = vec.into();
        let mut iter = nclist.into_iter();

        let first_element = iter.next().unwrap();
        assert_eq!(first_element.value, 1..4);
        assert_eq!(first_element.sublist().next().unwrap().value, 2..3);
        let second_element = iter.next().unwrap();
        assert_eq!(second_element.value, 5..6);
    }
}

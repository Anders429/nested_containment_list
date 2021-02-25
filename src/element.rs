//! Internal elements and their associated methods.
//!
//! The `Element` struct defined here is not publicly exposed. Instead, separate
//! `OverlappingElement` and `IterElement` structs are exposed in the public API.

use core::{marker::PhantomData, num::NonZeroUsize, ops::RangeBounds};

/// Internal element, stored within the `NestedContainmentList` and its associated `Iterators`.
///
/// This contains all of the raw information about values stored in the containers (including the
/// values themselves).
#[derive(Debug)]
pub(crate) struct Element<R, T>
where
    R: RangeBounds<T>,
    T: Ord,
{
    pub(crate) value: R,
    pub(crate) sublist_len: usize,
    // Direct parent's offset, if the element has a parent. This is the absolute distance between
    // this element and its direct parent element.
    pub(crate) parent_offset: Option<NonZeroUsize>,
    pub(crate) _marker: PhantomData<T>,
}

pub(crate) trait ParentElements {
    type Item;

    unsafe fn top_most_parent_element_with_index(&self, index: usize) -> (&Self::Item, usize);
    unsafe fn top_most_parent_element(&self, index: usize) -> &Self::Item;
}

impl<R, T> ParentElements for [Element<R, T>]
where
    R: RangeBounds<T>,
    T: Ord,
{
    type Item = Element<R, T>;

    /// Find the element at `index`'s top-most parent element within `self`, alongside its index.
    ///
    /// # Safety
    /// The caller must guarantee that `index` is within the bounds of `self`.
    unsafe fn top_most_parent_element_with_index(
        &self,
        mut index: usize,
    ) -> (&Element<R, T>, usize) {
        loop {
            // Note that `index` must be within the bounds of `self`.
            let element = self.get_unchecked(index);
            if let Some(offset) = element.parent_offset {
                if offset.get() > index {
                    // The parent element exists outside of the scope of this
                    // iterator.
                    return (element, index);
                }
                index -= offset.get();
            } else {
                // This is the top-most element, since it has no parent offset.
                return (element, index);
            }
        }
    }

    /// Find the element at `index`'s top-most parent element within `self`.
    ///
    /// # Safety
    /// The caller must guarantee that `index` is within the bounds of `self`.
    unsafe fn top_most_parent_element(&self, index: usize) -> &Element<R, T> {
        self.top_most_parent_element_with_index(index).0
    }
}

#[cfg(test)]
mod tests {
    use crate::element::{Element, ParentElements};
    use core::{marker::PhantomData, num::NonZeroUsize, ptr};

    #[test]
    fn finds_top_most_parent_element() {
        let elements = &[
            Element {
                value: 1..4,
                sublist_len: 2,
                parent_offset: None,
                _marker: PhantomData,
            },
            Element {
                value: 2..4,
                sublist_len: 1,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
            Element {
                value: 2..3,
                sublist_len: 0,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
        ];

        assert!(ptr::eq(
            unsafe { elements.top_most_parent_element(2) },
            &elements[0]
        ));
    }

    #[test]
    fn finds_top_most_parent_element_no_parent() {
        let elements = &[Element {
            value: 1..4,
            sublist_len: 2,
            parent_offset: None,
            _marker: PhantomData,
        }];

        assert!(ptr::eq(
            unsafe { elements.top_most_parent_element(0) },
            &elements[0]
        ));
    }

    #[test]
    fn finds_top_most_parent_element_offset_out_of_scope() {
        let elements = &[
            Element {
                value: 1..4,
                sublist_len: 2,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
            Element {
                value: 2..4,
                sublist_len: 1,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
            Element {
                value: 2..3,
                sublist_len: 0,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
        ];

        assert!(ptr::eq(
            unsafe { elements.top_most_parent_element(2) },
            &elements[0]
        ));
    }

    #[test]
    fn finds_top_most_parent_element_with_index() {
        let elements = &[
            Element {
                value: 1..4,
                sublist_len: 2,
                parent_offset: None,
                _marker: PhantomData,
            },
            Element {
                value: 2..4,
                sublist_len: 1,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
            Element {
                value: 2..3,
                sublist_len: 0,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
        ];

        let result = unsafe { elements.top_most_parent_element_with_index(2) };

        assert!(ptr::eq(result.0, &elements[0]));
        assert_eq!(result.1, 0);
    }

    #[test]
    fn finds_top_most_parent_element_with_index_no_parent() {
        let elements = &[Element {
            value: 1..4,
            sublist_len: 2,
            parent_offset: None,
            _marker: PhantomData,
        }];

        let result = unsafe { elements.top_most_parent_element_with_index(0) };

        assert!(ptr::eq(result.0, &elements[0]));
        assert_eq!(result.1, 0);
    }

    #[test]
    fn finds_top_most_parent_element_with_index_offset_out_of_scope() {
        let elements = &[
            Element {
                value: 1..4,
                sublist_len: 2,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
            Element {
                value: 2..4,
                sublist_len: 1,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
            Element {
                value: 2..3,
                sublist_len: 0,
                parent_offset: NonZeroUsize::new(1),
                _marker: PhantomData,
            },
        ];

        let result = unsafe { elements.top_most_parent_element_with_index(2) };

        assert!(ptr::eq(result.0, &elements[0]));
        assert_eq!(result.1, 0);
    }
}

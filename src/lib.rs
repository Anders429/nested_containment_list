use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::iter::Chain;
use std::iter::Iterator;
use std::marker::PhantomData;
use std::option;

mod impls;

pub trait Nestable<B>
where
    B: Ord,
{
    fn left_bound(&self) -> B;
    fn right_bound(&self) -> B;
}

fn nestable_contains<B, N>(a: &N, b: &N) -> bool
where
    B: Ord,
    N: Nestable<B>,
{
    Nestable::left_bound(a) <= Nestable::left_bound(b)
        && Nestable::left_bound(b) <= Nestable::right_bound(b)
        && Nestable::right_bound(b) <= Nestable::right_bound(a)
}

fn nestable_ordering<B, N>(a: &N, b: &N) -> Ordering
where
    B: Ord,
    N: Nestable<B>,
{
    if Nestable::left_bound(a) < Nestable::left_bound(b)
        || Nestable::left_bound(a) == Nestable::left_bound(b)
            && Nestable::right_bound(a) > Nestable::right_bound(b)
    {
        Ordering::Less
    } else if Nestable::left_bound(a) > Nestable::left_bound(b)
        || Nestable::right_bound(a) < Nestable::right_bound(b)
    {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

fn nestable_overlap<B, N>(a: &N, b: &N) -> bool
where
    B: Ord,
    N: Nestable<B>,
{
    Nestable::left_bound(a) <= Nestable::right_bound(b)
        && Nestable::right_bound(a) >= Nestable::right_bound(b)
        || Nestable::left_bound(b) <= Nestable::right_bound(a)
            && Nestable::right_bound(b) >= Nestable::right_bound(a)
}

#[derive(Debug, Eq, PartialEq)]
struct Element<B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    value: N,
    sublist_len: usize,
    _marker: PhantomData<B>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct SublistElement<'a, B, N>
where
    B: Ord + 'a,
    N: Nestable<B> + 'a,
{
    pub value: &'a N,
    sublist_elements: &'a [Element<B, N>],
    _marker: PhantomData<B>,
}

impl<'a, B, N> SublistElement<'a, B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    pub fn sublist(&self) -> Sublist<'a, B, N> {
        Sublist::new(self.sublist_elements)
    }
}

impl<'a, B, N> IntoIterator for SublistElement<'a, B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    type Item = Self;
    type IntoIter = Chain<option::IntoIter<Self::Item>, Sublist<'a, B, N>>;

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

#[derive(Debug)]
pub struct Sublist<'a, B, N>
where
    B: Ord + 'a,
    N: Nestable<B> + 'a,
{
    index: usize,
    elements: &'a [Element<B, N>],
}

impl<'a, B, N> Sublist<'a, B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    fn new(elements: &'a [Element<B, N>]) -> Self {
        Sublist {
            index: 0,
            elements: elements,
        }
    }
}

impl<'a, B, N> Iterator for Sublist<'a, B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    type Item = SublistElement<'a, B, N>;

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

#[derive(Debug, Eq, PartialEq)]
pub struct OverlappingElement<'a, B, Q, N>
where
    B: Ord + 'a,
    Q: Nestable<B> + 'a,
    N: Nestable<B> + Borrow<Q> + 'a,
{
    pub value: &'a N,
    sublist_elements: &'a [Element<B, N>],
    query: &'a Q,
    _marker: PhantomData<B>,
}

impl<'a, B, Q, N> OverlappingElement<'a, B, Q, N>
where
    B: Ord,
    Q: Nestable<B>,
    N: Nestable<B> + Borrow<Q>,
{
    pub fn sublist(&self) -> Overlapping<'a, B, Q, N> {
        Overlapping::new(self.sublist_elements, self.query)
    }
}

impl<'a, B, Q, N> IntoIterator for OverlappingElement<'a, B, Q, N>
where
    B: Ord,
    Q: Nestable<B>,
    N: Nestable<B> + Borrow<Q>,
{
    type Item = Self;
    type IntoIter = Chain<option::IntoIter<Self::Item>, Overlapping<'a, B, Q, N>>;

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

pub struct Overlapping<'a, B, Q, N>
where
    B: Ord + 'a,
    Q: Nestable<B> + 'a,
    N: Nestable<B> + Borrow<Q> + 'a,
{
    sublist: Sublist<'a, B, N>,
    query: &'a Q,
}

impl<'a, B, Q, N> Overlapping<'a, B, Q, N>
where
    B: Ord,
    Q: Nestable<B>,
    N: Nestable<B> + Borrow<Q>,
{
    fn new(elements: &'a [Element<B, N>], query: &'a Q) -> Self {
        let start_index = match elements.binary_search_by(|element| {
            Ord::cmp(
                &Nestable::right_bound(query),
                &Nestable::right_bound(Borrow::borrow(&element.value)),
            )
        }) {
            Ok(index) => index,
            Err(index) => index,
        };
        Overlapping {
            sublist: Sublist {
                index: start_index,
                elements: elements,
            },
            query: query,
        }
    }
}

impl<'a, B, Q, N> Iterator for Overlapping<'a, B, Q, N>
where
    B: Ord,
    Q: Nestable<B>,
    N: Nestable<B> + Borrow<Q>,
{
    type Item = OverlappingElement<'a, B, Q, N>;

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

#[derive(Debug)]
pub struct NestedContainmentList<B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    elements: Vec<Element<B, N>>,
}

impl<B, N> NestedContainmentList<B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    pub fn new() -> Self {
        NestedContainmentList {
            elements: Vec::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        NestedContainmentList {
            elements: Vec::with_capacity(capacity),
        }
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn capacity(&self) -> usize {
        self.elements.capacity()
    }

    pub fn sublist<'a>(&'a self) -> Sublist<'a, B, N> {
        Sublist::new(&self.elements)
    }

    pub fn overlapping<'a, Q>(&'a self, query: &'a Q) -> Overlapping<'a, B, Q, N>
    where
        Q: Nestable<B>,
        N: Borrow<Q>,
    {
        Overlapping::new(&self.elements, query)
    }

    pub fn insert(&mut self, value: N) {
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

    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        Q: Nestable<B>,
        N: Borrow<Q>,
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
                _ => {}
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
fn sort_values<B, N>(values: &mut Vec<N>)
where
    B: Ord,
    N: Nestable<B> + Clone,
{
    values.sort_unstable_by(nestable_ordering);
}

// Otherwise, we use the regular sort_by.
#[cfg(not(rustc_1_20))]
#[inline]
fn sort_values<B, N>(values: &mut Vec<N>)
where
    B: Ord,
    N: Nestable<B> + Clone,
{
    values.sort_by(nestable_ordering);
}

impl<B, N> NestedContainmentList<B, N>
where
    B: Ord,
    N: Nestable<B> + Clone,
{
    pub fn from_slice(values: &[N]) -> Self {
        // Sort the elements.
        let mut values = values.to_vec();
        sort_values(&mut values);

        // Depth-first construction.
        let mut elements: Vec<Element<B, N>> = Vec::with_capacity(values.len());
        let mut sublist_indices: VecDeque<usize> = VecDeque::with_capacity(values.len());
        for index in 0..values.len() {
            let value = values.remove(0);
            while !sublist_indices.is_empty() {
                let sublist_index = sublist_indices.pop_back().unwrap();

                if nestable_contains(&elements[sublist_index].value, &value) {
                    // We are within the previous sublist.
                    sublist_indices.push_back(sublist_index);
                    break;
                } else {
                    // We are no longer within the previous sublist.
                    let len = index - sublist_index - 1;
                    elements[sublist_index].sublist_len = len;
                }
            }

            sublist_indices.push_back(index);
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

impl<B, N> Default for NestedContainmentList<B, N>
where
    B: Ord,
    N: Nestable<B>,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;
    use NestedContainmentList;

    #[test]
    fn new() {
        let nclist = NestedContainmentList::<usize, Range<usize>>::new();

        // Check that the sublist is empty.
        assert_eq!(nclist.sublist().next(), None);
    }

    #[test]
    fn default() {
        let nclist = NestedContainmentList::<usize, Range<usize>>::default();

        // Check that the sublist is empty.
        assert_eq!(nclist.sublist().next(), None);
    }

    #[test]
    fn insert_on_empty() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);

        let mut sublist = nclist.sublist();
        assert_eq!(sublist.next().unwrap().value, &(1..5));
        assert_eq!(sublist.next(), None);
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
        assert_eq!(sublist_first_element_sublist.next(), None);
        assert_eq!(sublist.next(), None);
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
        assert_eq!(first_sublist_element_sublist.next(), None);
        assert_eq!(sublist.next(), None);
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
        assert_eq!(first_sublist_element_sublist.next(), None);
        assert_eq!(sublist.next().unwrap().value, &(6..10));
        assert_eq!(sublist.next(), None);
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
        assert_eq!(first_sublist_element_sublist.next(), None);
        assert_eq!(sublist.next(), None);
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
        assert_eq!(first_sublist_element_sublist.next(), None);
        assert_eq!(sublist.next(), None);
    }

    #[test]
    fn insert_disjoint() {
        let mut nclist = NestedContainmentList::new();

        nclist.insert(1..5);
        nclist.insert(6..10);

        let mut sublist = nclist.sublist();
        assert_eq!(sublist.next().unwrap().value, &(1..5));
        assert_eq!(sublist.next().unwrap().value, &(6..10));
        assert_eq!(sublist.next(), None);
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
        let mut nclist = NestedContainmentList::from_slice(&[1..5]);

        assert!(!nclist.remove(&(1..4)));
    }

    #[test]
    fn remove_contained() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 2..4]);

        assert!(nclist.remove(&(2..4)));

        let mut sublist = nclist.sublist();
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_eq!(first_element.sublist().next(), None);
        assert_eq!(sublist.next(), None);
    }

    #[test]
    fn remove_containing() {
        let mut nclist = NestedContainmentList::from_slice(&[1..5, 0..6]);

        assert!(nclist.remove(&(0..6)));

        let mut sublist = nclist.sublist();
        let first_element = sublist.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_eq!(first_element.sublist().next(), None);
        assert_eq!(sublist.next(), None);
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
        assert_eq!(first_sublist_element_sublist.next(), None);
        assert_eq!(sublist.next(), None);
    }

    #[test]
    fn overlapping() {
        let nclist = NestedContainmentList::from_slice(&[1..5, 3..4, 2..4, 6..7]);

        let query = 5..7;
        let mut overlapping = nclist.overlapping(&query);

        let first_element = overlapping.next().unwrap();
        assert_eq!(first_element.value, &(1..5));
        assert_eq!(first_element.sublist().next(), None);
        let second_element = overlapping.next().unwrap();
        assert_eq!(second_element.value, &(6..7));
        assert_eq!(second_element.sublist().next(), None);
        assert_eq!(overlapping.next(), None);
    }

    #[test]
    fn overlapping_skip_first() {
        let nclist = NestedContainmentList::from_slice(&[1..2, 3..4]);

        let query = 3..4;
        let mut overlapping = nclist.overlapping(&query);

        let first_element = overlapping.next().unwrap();
        assert_eq!(first_element.value, &(3..4));
        assert_eq!(first_element.sublist().next(), None);
        assert_eq!(overlapping.next(), None);
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
        assert_eq!(first_sublist_element_sublist.next(), None);
        assert_eq!(sublist.next().unwrap().value, &(6..7));
        assert_eq!(sublist.next(), None);
    }
}

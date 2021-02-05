use core::{
    cmp::Ordering,
    ops::{Bound, RangeBounds},
};

pub(crate) trait Nestable<R, T>
where
    R: RangeBounds<T>,
{
    fn contains<S>(&self, inner: &S) -> bool
    where
        S: RangeBounds<T>;
    fn ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>;
    fn end_bound_ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>;
}

impl<R, T> Nestable<R, T> for R
where
    R: RangeBounds<T>,
    T: PartialOrd<T>,
{
    fn contains<S>(&self, inner: &S) -> bool
    where
        S: RangeBounds<T>,
    {
        (match self.start_bound() {
            Bound::Included(outer_start) => match inner.start_bound() {
                Bound::Included(inner_start) | Bound::Excluded(inner_start) => {
                    outer_start <= inner_start
                }
                Bound::Unbounded => false,
            },
            Bound::Excluded(outer_start) => match inner.start_bound() {
                Bound::Included(inner_start) => outer_start < inner_start,
                Bound::Excluded(inner_start) => outer_start <= inner_start,
                Bound::Unbounded => false,
            },
            Bound::Unbounded => true,
        }) && (match self.end_bound() {
            Bound::Included(outer_end) => match inner.end_bound() {
                Bound::Included(inner_end) | Bound::Excluded(inner_end) => outer_end >= inner_end,
                Bound::Unbounded => false,
            },
            Bound::Excluded(outer_end) => match inner.end_bound() {
                Bound::Included(inner_end) => outer_end > inner_end,
                Bound::Excluded(inner_end) => outer_end >= inner_end,
                Bound::Unbounded => false,
            },
            Bound::Unbounded => true,
        })
    }

    fn ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>,
    {
        match self.start_bound() {
            Bound::Included(self_start) => match other.start_bound() {
                Bound::Included(other_start) => {
                    if self_start < other_start {
                        Ordering::Less
                    } else if self_start == other_start {
                        self.end_bound_ordering(other)
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Excluded(other_start) => {
                    if self_start <= other_start {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Unbounded => Ordering::Greater,
            },
            Bound::Excluded(self_start) => match other.start_bound() {
                Bound::Included(other_start) => {
                    if self_start < other_start {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Excluded(other_start) => {
                    if self_start < other_start {
                        Ordering::Less
                    } else if self_start == other_start {
                        self.end_bound_ordering(other)
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Unbounded => Ordering::Greater,
            },
            Bound::Unbounded => match other.start_bound() {
                Bound::Unbounded => Ordering::Equal,
                _ => Ordering::Less,
            },
        }
    }

    #[inline]
    fn end_bound_ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>,
    {
        match self.end_bound() {
            Bound::Included(self_end) => match other.end_bound() {
                Bound::Included(other_end) => {
                    if self_end > other_end {
                        Ordering::Less
                    } else if self_end == other_end {
                        Ordering::Equal
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Excluded(other_end) => {
                    if self_end >= other_end {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Unbounded => Ordering::Less,
            },
            Bound::Excluded(self_end) => match other.end_bound() {
                Bound::Included(other_end) => {
                    if self_end > other_end {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Excluded(other_end) => {
                    if self_end > other_end {
                        Ordering::Less
                    } else if self_end == other_end {
                        Ordering::Equal
                    } else {
                        Ordering::Greater
                    }
                }
                Bound::Unbounded => Ordering::Less,
            },
            Bound::Unbounded => match other.end_bound() {
                Bound::Unbounded => Ordering::Equal,
                _ => Ordering::Greater,
            },
        }
    }
}

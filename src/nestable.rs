use core::{
    cmp::Ordering::{self, Equal, Greater, Less},
    ops::{
        Bound::{Excluded, Included, Unbounded},
        RangeBounds,
    },
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
            Included(outer_start) => match inner.start_bound() {
                Included(inner_start) | Excluded(inner_start) => outer_start <= inner_start,
                Unbounded => false,
            },
            Excluded(outer_start) => match inner.start_bound() {
                Included(inner_start) => outer_start < inner_start,
                Excluded(inner_start) => outer_start <= inner_start,
                Unbounded => false,
            },
            Unbounded => true,
        }) && (match self.end_bound() {
            Included(outer_end) => match inner.end_bound() {
                Included(inner_end) | Excluded(inner_end) => outer_end >= inner_end,
                Unbounded => false,
            },
            Excluded(outer_end) => match inner.end_bound() {
                Included(inner_end) => outer_end > inner_end,
                Excluded(inner_end) => outer_end >= inner_end,
                Unbounded => false,
            },
            Unbounded => true,
        })
    }

    fn ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>,
    {
        match self.start_bound() {
            Included(self_start) => match other.start_bound() {
                Included(other_start) => {
                    if self_start < other_start {
                        Less
                    } else if self_start == other_start {
                        self.end_bound_ordering(other)
                    } else {
                        Greater
                    }
                }
                Excluded(other_start) => {
                    if self_start <= other_start {
                        Less
                    } else {
                        Greater
                    }
                }
                Unbounded => Greater,
            },
            Excluded(self_start) => match other.start_bound() {
                Included(other_start) => {
                    if self_start < other_start {
                        Less
                    } else {
                        Greater
                    }
                }
                Excluded(other_start) => {
                    if self_start < other_start {
                        Less
                    } else if self_start == other_start {
                        self.end_bound_ordering(other)
                    } else {
                        Greater
                    }
                }
                Unbounded => Greater,
            },
            Unbounded => match other.start_bound() {
                Unbounded => Equal,
                _ => Less,
            },
        }
    }

    #[inline]
    fn end_bound_ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>,
    {
        match self.end_bound() {
            Included(self_end) => match other.end_bound() {
                Included(other_end) => {
                    if self_end > other_end {
                        Less
                    } else if self_end == other_end {
                        Equal
                    } else {
                        Greater
                    }
                }
                Excluded(other_end) => {
                    if self_end >= other_end {
                        Less
                    } else {
                        Greater
                    }
                }
                Unbounded => Less,
            },
            Excluded(self_end) => match other.end_bound() {
                Included(other_end) => {
                    if self_end > other_end {
                        Less
                    } else {
                        Greater
                    }
                }
                Excluded(other_end) => {
                    if self_end > other_end {
                        Less
                    } else if self_end == other_end {
                        Equal
                    } else {
                        Greater
                    }
                }
                Unbounded => Less,
            },
            Unbounded => match other.end_bound() {
                Unbounded => Equal,
                _ => Greater,
            },
        }
    }
}

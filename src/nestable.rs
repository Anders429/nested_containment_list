use core::{
    cmp::Ordering::{self, Equal, Greater, Less},
    ops::{
        Bound::{Excluded, Included, Unbounded},
        RangeBounds,
    },
};

#[inline]
fn end_bound_ordering<R, S, T>(this: &R, other: &S) -> Ordering
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: PartialOrd<T>,
{
    match this.end_bound() {
        Included(this_end) => match other.end_bound() {
            Included(other_end) => {
                if this_end > other_end {
                    Less
                } else if this_end == other_end {
                    Equal
                } else {
                    Greater
                }
            }
            Excluded(other_end) => {
                if this_end >= other_end {
                    Less
                } else {
                    Greater
                }
            }
            Unbounded => Less,
        },
        Excluded(this_end) => match other.end_bound() {
            Included(other_end) => {
                if this_end > other_end {
                    Less
                } else {
                    Greater
                }
            }
            Excluded(other_end) => {
                if this_end > other_end {
                    Less
                } else if this_end == other_end {
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
                        end_bound_ordering(self, other)
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
                        end_bound_ordering(self, other)
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
}

#[cfg(test)]
mod tests {
    use core::ops::RangeFull;
    use nestable::Nestable;

    #[test]
    fn range_full_contains() {
        assert!(Nestable::<RangeFull, usize>::contains(&(..), &(..)));
        assert!((..).contains(&(1..)));
        assert!((..).contains(&(..1)));
        assert!((..).contains(&(..=1)));
        assert!((..).contains(&(0..1)));
        assert!((..).contains(&(0..=1)));
    }

    #[test]
    fn range_from_contains() {
        assert!(!Nestable::contains(&(1..), &(..)));
        assert!(Nestable::contains(&(1..), &(2..)));
        assert!(!Nestable::contains(&(1..), &(0..)));
        assert!(!Nestable::contains(&(1..), &(..2)));
        assert!(!Nestable::contains(&(1..), &(..=2)));
        assert!(Nestable::contains(&(1..), &(2..3)));
        assert!(!Nestable::contains(&(1..), &(0..3)));
        assert!(Nestable::contains(&(1..), &(2..=3)));
        assert!(!Nestable::contains(&(1..), &(0..=3)));
    }

    #[test]
    fn range_to_contains() {
        assert!(!Nestable::contains(&(..2), &(..)));
        assert!(!Nestable::contains(&(..2), &(1..)));
        assert!(Nestable::contains(&(..2), &(..1)));
        assert!(!Nestable::contains(&(..2), &(..3)));
        assert!(Nestable::contains(&(..2), &(..=1)));
        assert!(!Nestable::contains(&(..2), &(..=2)));
        assert!(!Nestable::contains(&(..2), &(..=3)));
        assert!(Nestable::contains(&(..2), &(0..1)));
        assert!(Nestable::contains(&(..2), &(0..2)));
        assert!(!Nestable::contains(&(..2), &(0..3)));
        assert!(!Nestable::contains(&(..2), &(2..3)));
        assert!(Nestable::contains(&(..2), &(2..2)));
        assert!(Nestable::contains(&(..2), &(0..=1)));
        assert!(!Nestable::contains(&(..2), &(0..=2)));
        assert!(!Nestable::contains(&(..2), &(0..=3)));
        assert!(!Nestable::contains(&(..2), &(2..=3)));
        assert!(!Nestable::contains(&(..2), &(2..=2)));
    }

    #[test]
    fn range_to_inclusive_contains() {
        assert!(!Nestable::contains(&(..=2), &(..)));
        assert!(!Nestable::contains(&(..=2), &(1..)));
        assert!(Nestable::contains(&(..=2), &(..1)));
        assert!(Nestable::contains(&(..=2), &(..2)));
        assert!(!Nestable::contains(&(..=2), &(..3)));
        assert!(Nestable::contains(&(..=2), &(..=1)));
        assert!(Nestable::contains(&(..=2), &(..=2)));
        assert!(!Nestable::contains(&(..=2), &(..=3)));
        assert!(Nestable::contains(&(..=2), &(0..1)));
        assert!(Nestable::contains(&(..=2), &(0..2)));
        assert!(!Nestable::contains(&(..=2), &(0..3)));
        assert!(Nestable::contains(&(..=2), &(2..2)));
        assert!(Nestable::contains(&(..=2), &(0..=1)));
        assert!(Nestable::contains(&(..=2), &(0..=2)));
        assert!(!Nestable::contains(&(..=2), &(0..=3)));
        assert!(Nestable::contains(&(..=2), &(2..=2)));
    }

    #[test]
    fn range_contains() {
        assert!(!Nestable::contains(&(1..4), &(..)));
        assert!(!Nestable::contains(&(1..4), &(2..)));
        assert!(!Nestable::contains(&(1..4), &(..3)));
        assert!(!Nestable::contains(&(1..4), &(..=3)));
        assert!(Nestable::contains(&(1..4), &(2..3)));
        assert!(!Nestable::contains(&(1..4), &(2..5)));
        assert!(!Nestable::contains(&(1..4), &(0..3)));
        assert!(!Nestable::contains(&(1..4), &(5..6)));
        assert!(Nestable::contains(&(1..4), &(2..4)));
        assert!(Nestable::contains(&(1..4), &(1..3)));
        assert!(Nestable::contains(&(1..4), &(2..=3)));
        assert!(!Nestable::contains(&(1..4), &(2..=5)));
        assert!(!Nestable::contains(&(1..4), &(0..=3)));
        assert!(!Nestable::contains(&(1..4), &(5..=6)));
        assert!(!Nestable::contains(&(1..4), &(2..=4)));
        assert!(Nestable::contains(&(1..4), &(1..=3)));
    }

    #[test]
    fn range_inclusive_contains() {
        assert!(!Nestable::contains(&(1..=4), &(..)));
        assert!(!Nestable::contains(&(1..=4), &(2..)));
        assert!(!Nestable::contains(&(1..=4), &(..3)));
        assert!(!Nestable::contains(&(1..=4), &(..=3)));
        assert!(Nestable::contains(&(1..=4), &(2..3)));
        assert!(!Nestable::contains(&(1..=4), &(2..5)));
        assert!(!Nestable::contains(&(1..=4), &(0..3)));
        assert!(!Nestable::contains(&(1..=4), &(5..6)));
        assert!(Nestable::contains(&(1..=4), &(2..4)));
        assert!(Nestable::contains(&(1..=4), &(1..3)));
        assert!(Nestable::contains(&(1..=4), &(2..=3)));
        assert!(!Nestable::contains(&(1..=4), &(2..=5)));
        assert!(!Nestable::contains(&(1..=4), &(0..=3)));
        assert!(!Nestable::contains(&(1..=4), &(5..=6)));
        assert!(Nestable::contains(&(1..=4), &(2..=4)));
        assert!(Nestable::contains(&(1..=4), &(1..=3)));
    }
}

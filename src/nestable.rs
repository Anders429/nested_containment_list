/// Defines a `Nestable` trait for types that are usable within a `NestedContainmentList`.
///
/// A type that is `Nestable` has two methods provided: `contains()` and `ordering()`. All types
/// that implement `RangeBounds<T>` where `T` is `PartialOrd<T>` implicitly implement `Nestable`.
///
/// A `Nestable` value is "contained" (via `contains()`) inside another `Nestable` value if its
/// bounds can be exactly contained inside the other value. This takes into account all variants of
/// bounds.
///
/// An ordering is also defined on `Nestable` types, using `ordering()`. This is defined by first
/// comparing on the `start_bound()`, and then, if the values are equal, comparing on `end_bound()`.
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
            Unbounded => Greater,
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
            Unbounded => Greater,
        },
        Unbounded => match other.end_bound() {
            Unbounded => Equal,
            _ => Less,
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
                Unbounded => end_bound_ordering(self, other),
                _ => Less,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use claim::assert_matches;
    use core::{
        cmp::Ordering::{Equal, Greater, Less},
        ops::RangeFull,
    };
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

    #[test]
    fn range_full_ordering() {
        assert_matches!(Nestable::<RangeFull, usize>::ordering(&(..), &(..)), Equal);
        assert_matches!((..).ordering(&(1..)), Less);
        assert_matches!((..).ordering(&(..1)), Less);
        assert_matches!((..).ordering(&(..=1)), Less);
        assert_matches!((..).ordering(&(1..2)), Less);
        assert_matches!((..).ordering(&(1..=2)), Less);
    }

    #[test]
    fn range_from_ordering() {
        assert_matches!((1..).ordering(&(..)), Greater);
        assert_matches!((1..).ordering(&(0..)), Greater);
        assert_matches!((1..).ordering(&(1..)), Equal);
        assert_matches!((1..).ordering(&(2..)), Less);
        assert_matches!((1..).ordering(&(..2)), Greater);
        assert_matches!((1..).ordering(&(..=2)), Greater);
        assert_matches!((1..).ordering(&(0..2)), Greater);
        assert_matches!((1..).ordering(&(1..2)), Less);
        assert_matches!((1..).ordering(&(2..3)), Less);
        assert_matches!((1..).ordering(&(0..=2)), Greater);
        assert_matches!((1..).ordering(&(1..=2)), Less);
        assert_matches!((1..).ordering(&(2..=3)), Less);
    }

    #[test]
    fn range_to_ordering() {
        assert_matches!((..2).ordering(&(..)), Greater);
        assert_matches!((..2).ordering(&(1..)), Less);
        assert_matches!((..2).ordering(&(..1)), Less);
        assert_matches!((..2).ordering(&(..2)), Equal);
        assert_matches!((..2).ordering(&(..3)), Greater);
        assert_matches!((..2).ordering(&(..=1)), Less);
        assert_matches!((..2).ordering(&(..=2)), Greater);
        assert_matches!((..2).ordering(&(..=3)), Greater);
        assert_matches!((..2).ordering(&(0..1)), Less);
        assert_matches!((..2).ordering(&(0..=1)), Less);
    }

    #[test]
    fn range_to_inclusive_ordering() {
        assert_matches!((..=2).ordering(&(..)), Greater);
        assert_matches!((..=2).ordering(&(1..)), Less);
        assert_matches!((..=2).ordering(&(..1)), Less);
        assert_matches!((..=2).ordering(&(..2)), Less);
        assert_matches!((..=2).ordering(&(..3)), Greater);
        assert_matches!((..=2).ordering(&(..=1)), Less);
        assert_matches!((..=2).ordering(&(..=2)), Equal);
        assert_matches!((..=2).ordering(&(..=3)), Greater);
        assert_matches!((..=2).ordering(&(0..1)), Less);
        assert_matches!((..=2).ordering(&(0..=1)), Less);
    }

    #[test]
    fn range_ordering() {
        assert_matches!((1..4).ordering(&(..)), Greater);
        assert_matches!((1..4).ordering(&(0..)), Greater);
        assert_matches!((1..4).ordering(&(1..)), Greater);
        assert_matches!((1..4).ordering(&(2..)), Less);
        assert_matches!((1..4).ordering(&(..2)), Greater);
        assert_matches!((1..4).ordering(&(..=2)), Greater);
        assert_matches!((1..4).ordering(&(0..2)), Greater);
        assert_matches!((1..4).ordering(&(0..5)), Greater);
        assert_matches!((1..4).ordering(&(1..5)), Greater);
        assert_matches!((1..4).ordering(&(1..4)), Equal);
        assert_matches!((1..4).ordering(&(1..3)), Less);
        assert_matches!((1..4).ordering(&(2..5)), Less);
        assert_matches!((1..4).ordering(&(0..=2)), Greater);
        assert_matches!((1..4).ordering(&(0..=5)), Greater);
        assert_matches!((1..4).ordering(&(1..=5)), Greater);
        assert_matches!((1..4).ordering(&(1..=4)), Greater);
        assert_matches!((1..4).ordering(&(1..=3)), Less);
        assert_matches!((1..4).ordering(&(2..=5)), Less);
    }

    #[test]
    fn range_inclusive_ordering() {
        assert_matches!((1..=4).ordering(&(..)), Greater);
        assert_matches!((1..=4).ordering(&(0..)), Greater);
        assert_matches!((1..=4).ordering(&(1..)), Greater);
        assert_matches!((1..=4).ordering(&(2..)), Less);
        assert_matches!((1..=4).ordering(&(..2)), Greater);
        assert_matches!((1..=4).ordering(&(..=2)), Greater);
        assert_matches!((1..=4).ordering(&(0..2)), Greater);
        assert_matches!((1..=4).ordering(&(0..5)), Greater);
        assert_matches!((1..=4).ordering(&(1..5)), Greater);
        assert_matches!((1..=4).ordering(&(1..4)), Less);
        assert_matches!((1..=4).ordering(&(1..3)), Less);
        assert_matches!((1..=4).ordering(&(2..5)), Less);
        assert_matches!((1..=4).ordering(&(0..=2)), Greater);
        assert_matches!((1..=4).ordering(&(0..=5)), Greater);
        assert_matches!((1..=4).ordering(&(1..=5)), Greater);
        assert_matches!((1..=4).ordering(&(1..=4)), Equal);
        assert_matches!((1..=4).ordering(&(1..=3)), Less);
        assert_matches!((1..=4).ordering(&(2..=5)), Less);
    }
}

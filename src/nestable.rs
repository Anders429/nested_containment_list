/// Defines a `Nestable` trait for types that are usable within a `NestedContainmentList`.
///
/// A type that is `Nestable` has two methods provided: `contains()` and `ordering()`. All types
/// that implement `RangeBounds<T>` where `T` is `Ord` implicitly implement `Nestable`.
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

/// Internal function for ordering on `end_bound()`s.
///
/// The ordering is done in reverse. See documentation for `Nestable::ordering()` for more.
#[inline]
fn end_bound_ordering<R, S, T>(this: &R, other: &S) -> Ordering
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
    match (this.end_bound(), other.end_bound()) {
        (Included(this_end), Included(other_end)) | (Excluded(this_end), Excluded(other_end)) => {
            other_end.cmp(this_end)
        }
        (Included(this_end), Excluded(other_end)) => other_end.cmp(this_end).then(Less),
        (Excluded(this_end), Included(other_end)) => other_end.cmp(this_end).then(Greater),
        (Unbounded, Unbounded) => Equal,
        (Unbounded, _) => Less,
        (_, Unbounded) => Greater,
    }
}

/// Internal function for finding overlap one way.
///
/// This performs the comparison upon `other.end_bound()`, finding whether it lies in the range
/// `this`.
///
/// This calculation is preferred over `RangeBounds::contains()`, as it takes into account the
/// `Bound` variants.
///
/// Note that this is a "naive" implementation, as it only accounts for half the cases. If `other`
/// is unbounded above, for example, this will fail. The full check should be done both ways.
#[inline]
fn overlap_naive<R, S, T>(this: &R, other: &S) -> bool
where
    R: RangeBounds<T>,
    S: RangeBounds<T>,
    T: Ord,
{
    match (this.start_bound(), this.end_bound(), other.end_bound()) {
        (Unbounded, Unbounded, _) | (_, Unbounded, Unbounded) => true,
        (_, _, Unbounded) => false,
        (Unbounded, Included(this_end), Included(other_end))
        | (Unbounded, Excluded(this_end), Excluded(other_end))
        | (Unbounded, Included(this_end), Excluded(other_end)) => this_end >= other_end,
        (Unbounded, Excluded(this_end), Included(other_end)) => this_end > other_end,
        (Included(this_start), Unbounded, Included(other_end)) => this_start <= other_end,
        (Included(this_start), Unbounded, Excluded(other_end))
        | (Excluded(this_start), Unbounded, Included(other_end))
        | (Excluded(this_start), Unbounded, Excluded(other_end)) => this_start < other_end,
        (Included(this_start), Included(this_end), Included(other_end)) => {
            this_start <= other_end && this_end >= other_end
        }
        (Included(this_start), Included(this_end), Excluded(other_end))
        | (Excluded(this_start), Included(this_end), Included(other_end))
        | (Excluded(this_start), Excluded(this_end), Excluded(other_end))
        | (Included(this_start), Excluded(this_end), Excluded(other_end))
        | (Excluded(this_start), Included(this_end), Excluded(other_end)) => {
            this_start < other_end && this_end >= other_end
        }
        (Included(this_start), Excluded(this_end), Included(other_end)) => {
            this_start <= other_end && this_end > other_end
        }

        (Excluded(this_start), Excluded(this_end), Included(other_end)) => {
            this_start < other_end && this_end > other_end
        }
    }
}

/// A trait for types which are nestable.
///
/// This trait is automatically implemented on all types which implement `RangeBounds<T>` over a
/// totally orderable `T`.
pub(crate) trait Nestable<R, T>
where
    R: RangeBounds<T>,
{
    /// `R` is said to "contain" `S` if `R::start_bound()` is less than or equal to
    /// `S::start_bound()` and `R::end_bound()` is greater than or equal to `S::end_bound()`.
    fn contains<S>(&self, inner: &S) -> bool
    where
        S: RangeBounds<T>;

    /// Ordering is calculated by comparing `start_bound()`. In the event of equality, ordering is
    /// then calculated by comparing `end_bound()` in reverse.
    ///
    /// This ordering guarantees that ranges will be immediately followed by each of their contained
    /// ranges.
    fn ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>;

    /// `R` overlaps `S` if any part of the range `R` appears within the range `S`. This method
    /// returns true if the two ranges overlap.
    fn overlapping<S>(&self, other: &S) -> bool
    where
        S: RangeBounds<T>;
}

/// Implementation on all types that implement `RangeBounds<T>` over a totally orderable `T`.
impl<R, T> Nestable<R, T> for R
where
    R: RangeBounds<T>,
    T: Ord,
{
    fn contains<S>(&self, inner: &S) -> bool
    where
        S: RangeBounds<T>,
    {
        (match (self.start_bound(), inner.start_bound()) {
            (Included(outer_start), Included(inner_start))
            | (Included(outer_start), Excluded(inner_start))
            | (Excluded(outer_start), Excluded(inner_start)) => outer_start <= inner_start,
            (Excluded(outer_start), Included(inner_start)) => outer_start < inner_start,
            (Unbounded, _) => true,
            (_, Unbounded) => false,
        }) && match (self.end_bound(), inner.end_bound()) {
            (Included(outer_start), Included(inner_start))
            | (Included(outer_start), Excluded(inner_start))
            | (Excluded(outer_start), Excluded(inner_start)) => outer_start >= inner_start,
            (Excluded(outer_start), Included(inner_start)) => outer_start > inner_start,
            (Unbounded, _) => true,
            (_, Unbounded) => false,
        }
    }

    fn ordering<S>(&self, other: &S) -> Ordering
    where
        S: RangeBounds<T>,
    {
        match (self.start_bound(), other.start_bound()) {
            (Included(self_start), Included(other_start))
            | (Excluded(self_start), Excluded(other_start)) => self_start
                .cmp(other_start)
                .then_with(|| end_bound_ordering(self, other)),
            (Included(self_start), Excluded(other_start)) => self_start.cmp(other_start).then(Less),
            (Excluded(self_start), Included(other_start)) => {
                self_start.cmp(other_start).then(Greater)
            }
            (Unbounded, Unbounded) => end_bound_ordering(self, other),
            (Unbounded, _) => Less,
            (_, Unbounded) => Greater,
        }
    }

    fn overlapping<S>(&self, other: &S) -> bool
    where
        S: RangeBounds<T>,
    {
        overlap_naive(self, other) || overlap_naive(other, self)
    }
}

#[cfg(test)]
mod tests {
    use crate::nestable::Nestable;
    use claim::assert_matches;
    use core::{
        cmp::Ordering::{Equal, Greater, Less},
        ops::RangeFull,
    };
    use more_ranges::{
        RangeFromExclusive, RangeFromExclusiveToExclusive, RangeFromExclusiveToInclusive,
    };

    #[test]
    fn range_full_contains() {
        assert!(Nestable::<RangeFull, usize>::contains(&(..), &(..)));
        assert!((..).contains(&(1..)));
        assert!((..).contains(&(..1)));
        assert!((..).contains(&(..=1)));
        assert!((..).contains(&(0..1)));
        assert!((..).contains(&(0..=1)));
        assert!((..).contains(&RangeFromExclusive { start: 1 }));
        assert!((..).contains(&RangeFromExclusiveToExclusive { start: 1, end: 4 }));
        assert!((..).contains(&RangeFromExclusiveToInclusive { start: 1, end: 4 }));
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
        assert!(!Nestable::contains(
            &(1..),
            &RangeFromExclusive { start: 0 }
        ));
        assert!(Nestable::contains(&(1..), &RangeFromExclusive { start: 1 }));
        assert!(Nestable::contains(&(1..), &RangeFromExclusive { start: 2 }));
        assert!(!Nestable::contains(
            &(1..),
            &RangeFromExclusiveToExclusive { start: 0, end: 1 }
        ));
        assert!(!Nestable::contains(
            &(1..),
            &RangeFromExclusiveToExclusive { start: 0, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..),
            &RangeFromExclusiveToExclusive { start: 1, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..),
            &RangeFromExclusiveToExclusive { start: 2, end: 4 }
        ));
        assert!(!Nestable::contains(
            &(1..),
            &RangeFromExclusiveToInclusive { start: 0, end: 1 }
        ));
        assert!(!Nestable::contains(
            &(1..),
            &RangeFromExclusiveToInclusive { start: 0, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..),
            &RangeFromExclusiveToInclusive { start: 1, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..),
            &RangeFromExclusiveToInclusive { start: 2, end: 4 }
        ));
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
        assert!(!Nestable::contains(
            &(..2),
            &RangeFromExclusive { start: 1 }
        ));
        assert!(Nestable::contains(
            &(..2),
            &RangeFromExclusiveToExclusive { start: 0, end: 1 }
        ));
        assert!(Nestable::contains(
            &(..2),
            &RangeFromExclusiveToExclusive { start: 0, end: 2 }
        ));
        assert!(!Nestable::contains(
            &(..2),
            &RangeFromExclusiveToExclusive { start: 0, end: 3 }
        ));
        assert!(Nestable::contains(
            &(..2),
            &RangeFromExclusiveToInclusive { start: 0, end: 1 }
        ));
        assert!(!Nestable::contains(
            &(..2),
            &RangeFromExclusiveToInclusive { start: 0, end: 2 }
        ));
        assert!(!Nestable::contains(
            &(..2),
            &RangeFromExclusiveToInclusive { start: 0, end: 3 }
        ));
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
        assert!(!Nestable::contains(
            &(..=2),
            &RangeFromExclusive { start: 1 }
        ));
        assert!(Nestable::contains(
            &(..=2),
            &RangeFromExclusiveToExclusive { start: 0, end: 1 }
        ));
        assert!(Nestable::contains(
            &(..=2),
            &RangeFromExclusiveToExclusive { start: 0, end: 2 }
        ));
        assert!(!Nestable::contains(
            &(..=2),
            &RangeFromExclusiveToExclusive { start: 0, end: 3 }
        ));
        assert!(Nestable::contains(
            &(..=2),
            &RangeFromExclusiveToInclusive { start: 0, end: 1 }
        ));
        assert!(Nestable::contains(
            &(..=2),
            &RangeFromExclusiveToInclusive { start: 0, end: 2 }
        ));
        assert!(!Nestable::contains(
            &(..=2),
            &RangeFromExclusiveToInclusive { start: 0, end: 3 }
        ));
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
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusive { start: 1 }
        ));
        assert!(Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToExclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToExclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToExclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToExclusive { start: 5, end: 6 }
        ));
        assert!(Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToExclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToExclusive { start: 1, end: 3 }
        ));
        assert!(Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToInclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToInclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToInclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToInclusive { start: 5, end: 6 }
        ));
        assert!(!Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToInclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..4),
            &RangeFromExclusiveToInclusive { start: 1, end: 3 }
        ));
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
        assert!(!Nestable::contains(
            &(1..=4),
            &RangeFromExclusive { start: 1 }
        ));
        assert!(Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToExclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToExclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToExclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToExclusive { start: 5, end: 6 }
        ));
        assert!(Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToExclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToExclusive { start: 1, end: 3 }
        ));
        assert!(Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToInclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToInclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToInclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToInclusive { start: 5, end: 6 }
        ));
        assert!(Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToInclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &(1..=4),
            &RangeFromExclusiveToInclusive { start: 1, end: 3 }
        ));
    }

    #[test]
    fn range_from_exclusive_contains() {
        assert!(!Nestable::contains(&RangeFromExclusive { start: 1 }, &(..)));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(0..)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(1..)
        ));
        assert!(Nestable::contains(&RangeFromExclusive { start: 1 }, &(2..)));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(..2)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(..=2)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(0..4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(1..4)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(2..4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(0..=4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(1..=4)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &(2..=4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &RangeFromExclusiveToExclusive { start: 0, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &RangeFromExclusiveToExclusive { start: 1, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &RangeFromExclusiveToExclusive { start: 2, end: 4 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &RangeFromExclusiveToInclusive { start: 0, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &RangeFromExclusiveToInclusive { start: 1, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusive { start: 1 },
            &RangeFromExclusiveToInclusive { start: 2, end: 4 }
        ));
    }

    #[test]
    fn range_from_exclusive_to_exclusive_contains() {
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(..)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(2..)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(..3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(..=3)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(2..3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(2..5)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(0..3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(5..6)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(2..4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(1..3)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(2..=3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(2..=5)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(0..=3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(5..=6)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(2..=4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &(1..=3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusive { start: 2 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 5, end: 6 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 1, end: 3 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 5, end: 6 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToExclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 1, end: 3 }
        ));
    }

    #[test]
    fn range_from_exclusive_to_inclusive_contains() {
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(..)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(2..)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(..3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(..=3)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(2..3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(2..5)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(0..3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(5..6)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(2..4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(1..3)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(2..=3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(2..=5)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(0..=3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(5..=6)
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(2..=4)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &(1..=3)
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusive { start: 2 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 5, end: 6 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToExclusive { start: 1, end: 3 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 2, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 2, end: 5 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 0, end: 3 }
        ));
        assert!(!Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 5, end: 6 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 2, end: 4 }
        ));
        assert!(Nestable::contains(
            &RangeFromExclusiveToInclusive { start: 1, end: 4 },
            &RangeFromExclusiveToInclusive { start: 1, end: 3 }
        ));
    }

    #[test]
    fn range_full_ordering() {
        assert_matches!(Nestable::<RangeFull, usize>::ordering(&(..), &(..)), Equal);
        assert_matches!((..).ordering(&(1..)), Less);
        assert_matches!((..).ordering(&(..1)), Less);
        assert_matches!((..).ordering(&(..=1)), Less);
        assert_matches!((..).ordering(&(1..2)), Less);
        assert_matches!((..).ordering(&(1..=2)), Less);
        assert_matches!((..).ordering(&RangeFromExclusive { start: 1 }), Less);
        assert_matches!(
            (..).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 2 }),
            Less
        );
        assert_matches!(
            (..).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 2 }),
            Less
        );
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
        assert_matches!((1..).ordering(&RangeFromExclusive { start: 0 }), Greater);
        assert_matches!((1..).ordering(&RangeFromExclusive { start: 1 }), Less);
        assert_matches!((1..).ordering(&RangeFromExclusive { start: 2 }), Less);
        assert_matches!(
            (1..).ordering(&RangeFromExclusiveToExclusive { start: 0, end: 3 }),
            Greater
        );
        assert_matches!(
            (1..).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            (1..).ordering(&RangeFromExclusiveToExclusive { start: 2, end: 3 }),
            Less
        );
        assert_matches!(
            (1..).ordering(&RangeFromExclusiveToInclusive { start: 0, end: 3 }),
            Greater
        );
        assert_matches!(
            (1..).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            (1..).ordering(&RangeFromExclusiveToInclusive { start: 2, end: 3 }),
            Less
        );
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
        assert_matches!((..2).ordering(&RangeFromExclusive { start: 1 }), Less);
        assert_matches!(
            (..2).ordering(&RangeFromExclusiveToExclusive { start: 0, end: 1 }),
            Less
        );
        assert_matches!(
            (..2).ordering(&RangeFromExclusiveToInclusive { start: 0, end: 1 }),
            Less
        );
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
        assert_matches!((..=2).ordering(&RangeFromExclusive { start: 1 }), Less);
        assert_matches!(
            (..=2).ordering(&RangeFromExclusiveToExclusive { start: 0, end: 1 }),
            Less
        );
        assert_matches!(
            (..=2).ordering(&RangeFromExclusiveToInclusive { start: 0, end: 1 }),
            Less
        );
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
        assert_matches!((1..4).ordering(&RangeFromExclusive { start: 0 }), Greater);
        assert_matches!((1..4).ordering(&RangeFromExclusive { start: 1 }), Less);
        assert_matches!((1..4).ordering(&RangeFromExclusive { start: 2 }), Less);
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToExclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToExclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 5 }),
            Less
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 4 }),
            Less
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToExclusive { start: 2, end: 5 }),
            Less
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToInclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToInclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 5 }),
            Less
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 4 }),
            Less
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            (1..4).ordering(&RangeFromExclusiveToInclusive { start: 2, end: 5 }),
            Less
        );
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
        assert_matches!((1..=4).ordering(&RangeFromExclusive { start: 0 }), Greater);
        assert_matches!((1..=4).ordering(&RangeFromExclusive { start: 1 }), Less);
        assert_matches!((1..=4).ordering(&RangeFromExclusive { start: 2 }), Less);
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToExclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToExclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 5 }),
            Less
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 4 }),
            Less
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToExclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToExclusive { start: 2, end: 5 }),
            Less
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToInclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToInclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 5 }),
            Less
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 4 }),
            Less
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToInclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            (1..=4).ordering(&RangeFromExclusiveToInclusive { start: 2, end: 5 }),
            Less
        );
    }

    #[test]
    fn range_from_exclusive_ordering() {
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(..)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(0..)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(1..)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(2..)), Less);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(..2)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(..=2)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(0..2)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(1..2)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(2..3)), Less);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(0..=2)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(1..=2)), Greater);
        assert_matches!(RangeFromExclusive { start: 1 }.ordering(&(2..=3)), Less);
        assert_matches!(
            RangeFromExclusive { start: 1 }.ordering(&RangeFromExclusive { start: 0 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }.ordering(&RangeFromExclusive { start: 1 }),
            Equal
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }.ordering(&RangeFromExclusive { start: 2 }),
            Less
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }
                .ordering(&RangeFromExclusiveToExclusive { start: 0, end: 3 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }
                .ordering(&RangeFromExclusiveToExclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }
                .ordering(&RangeFromExclusiveToExclusive { start: 2, end: 3 }),
            Less
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }
                .ordering(&RangeFromExclusiveToInclusive { start: 0, end: 3 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }
                .ordering(&RangeFromExclusiveToInclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            RangeFromExclusive { start: 1 }
                .ordering(&RangeFromExclusiveToInclusive { start: 2, end: 3 }),
            Less
        );
    }

    #[test]
    fn range_from_exclusive_to_exclusive_ordering() {
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(..)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(0..)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(1..)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(2..)),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(..2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(..=2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(0..2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(0..5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(1..5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(1..4)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(1..3)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(2..5)),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(0..=2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(0..=5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(1..=5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(1..=4)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(1..=3)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }.ordering(&(2..=5)),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusive { start: 0 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusive { start: 1 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusive { start: 2 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 1, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 1, end: 4 }),
            Equal
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 2, end: 5 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 1, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 1, end: 4 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToExclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 2, end: 5 }),
            Less
        );
    }

    #[test]
    fn range_from_exclusive_to_inclusive_ordering() {
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(..)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(0..)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(1..)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(2..)),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(..2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(..=2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(0..2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(0..5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(1..5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(1..4)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(1..3)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(2..5)),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(0..=2)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(0..=5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(1..=5)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(1..=4)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(1..=3)),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }.ordering(&(2..=5)),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusive { start: 0 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusive { start: 1 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusive { start: 2 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 1, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 1, end: 4 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToExclusive { start: 2, end: 5 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 0, end: 2 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 0, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 1, end: 5 }),
            Greater
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 1, end: 4 }),
            Equal
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 1, end: 3 }),
            Less
        );
        assert_matches!(
            RangeFromExclusiveToInclusive { start: 1, end: 4 }
                .ordering(&RangeFromExclusiveToInclusive { start: 2, end: 5 }),
            Less
        );
    }

    #[test]
    fn range_full_overlapping() {
        assert!(Nestable::<RangeFull, usize>::overlapping(&(..), &(..)));
        assert!((..).overlapping(&(1..)));
        assert!((..).overlapping(&(..2)));
        assert!((..).overlapping(&(..=2)));
        assert!((..).overlapping(&(1..2)));
        assert!((..).overlapping(&(1..=2)));
        assert!((..).overlapping(&RangeFromExclusive { start: 1 }));
        assert!((..).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 2 }));
        assert!((..).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 2 }));
    }

    #[test]
    fn range_from_overlapping() {
        assert!((1..).overlapping(&(..)));
        assert!((1..).overlapping(&(0..)));
        assert!((1..).overlapping(&(1..)));
        assert!((1..).overlapping(&(2..)));
        assert!(!(1..).overlapping(&(..0)));
        assert!(!(1..).overlapping(&(..1)));
        assert!((1..).overlapping(&(..2)));
        assert!(!(1..).overlapping(&(..=0)));
        assert!((1..).overlapping(&(..=1)));
        assert!((1..).overlapping(&(..=2)));
        assert!(!(1..).overlapping(&(0..0)));
        assert!(!(1..).overlapping(&(0..1)));
        assert!((1..).overlapping(&(0..2)));
        assert!((1..).overlapping(&(1..2)));
        assert!(!(1..).overlapping(&(0..=0)));
        assert!((1..).overlapping(&(0..=1)));
        assert!((1..).overlapping(&(0..=2)));
        assert!((1..).overlapping(&(1..=2)));
        assert!((1..).overlapping(&RangeFromExclusive { start: 0 }));
        assert!((1..).overlapping(&RangeFromExclusive { start: 1 }));
        assert!((1..).overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!(1..).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 0 }));
        assert!(!(1..).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!((1..).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 2 }));
        assert!((1..).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 2 }));
        assert!(!(1..).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 0 }));
        assert!((1..).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!((1..).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 2 }));
        assert!((1..).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 2 }));
    }

    #[test]
    fn range_to_overlapping() {
        assert!((..2).overlapping(&(..)));
        assert!((..2).overlapping(&(1..)));
        assert!(!(..2).overlapping(&(2..)));
        assert!(!(..2).overlapping(&(3..)));
        assert!((..2).overlapping(&(..1)));
        assert!((..2).overlapping(&(..2)));
        assert!((..2).overlapping(&(..3)));
        assert!((..2).overlapping(&(..=1)));
        assert!((..2).overlapping(&(..=2)));
        assert!((..2).overlapping(&(..=3)));
        assert!((..2).overlapping(&(0..1)));
        assert!((..2).overlapping(&(1..2)));
        assert!((..2).overlapping(&(1..3)));
        assert!(!(..2).overlapping(&(2..3)));
        assert!(!(..2).overlapping(&(3..4)));
        assert!((..2).overlapping(&(0..=1)));
        assert!((..2).overlapping(&(1..=2)));
        assert!((..2).overlapping(&(1..=3)));
        assert!(!(..2).overlapping(&(2..=3)));
        assert!(!(..2).overlapping(&(3..=4)));
        assert!((..2).overlapping(&RangeFromExclusive { start: 1 }));
        assert!(!(..2).overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!(..2).overlapping(&RangeFromExclusive { start: 3 }));
        assert!((..2).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!((..2).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 2 }));
        assert!((..2).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 3 }));
        assert!(!(..2).overlapping(&RangeFromExclusiveToExclusive { start: 2, end: 3 }));
        assert!(!(..2).overlapping(&RangeFromExclusiveToExclusive { start: 3, end: 4 }));
        assert!((..2).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!((..2).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 2 }));
        assert!((..2).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 3 }));
        assert!(!(..2).overlapping(&RangeFromExclusiveToInclusive { start: 2, end: 3 }));
        assert!(!(..2).overlapping(&RangeFromExclusiveToInclusive { start: 3, end: 4 }));
    }

    #[test]
    fn range_to_inclusive_overlapping() {
        assert!((..=2).overlapping(&(..)));
        assert!((..=2).overlapping(&(1..)));
        assert!((..=2).overlapping(&(2..)));
        assert!(!(..=2).overlapping(&(3..)));
        assert!((..=2).overlapping(&(..1)));
        assert!((..=2).overlapping(&(..2)));
        assert!((..=2).overlapping(&(..3)));
        assert!((..=2).overlapping(&(..=1)));
        assert!((..=2).overlapping(&(..=2)));
        assert!((..=2).overlapping(&(..=3)));
        assert!((..=2).overlapping(&(0..1)));
        assert!((..=2).overlapping(&(1..2)));
        assert!((..=2).overlapping(&(1..3)));
        assert!((..=2).overlapping(&(2..3)));
        assert!(!(..=2).overlapping(&(3..4)));
        assert!((..=2).overlapping(&(0..=1)));
        assert!((..=2).overlapping(&(1..=2)));
        assert!((..=2).overlapping(&(1..=3)));
        assert!((..=2).overlapping(&(2..=3)));
        assert!(!(..=2).overlapping(&(3..=4)));
        assert!((..=2).overlapping(&RangeFromExclusive { start: 1 }));
        assert!(!(..=2).overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!(..=2).overlapping(&RangeFromExclusive { start: 3 }));
        assert!((..=2).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!((..=2).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 2 }));
        assert!((..=2).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 3 }));
        assert!(!(..=2).overlapping(&RangeFromExclusiveToExclusive { start: 2, end: 3 }));
        assert!(!(..=2).overlapping(&RangeFromExclusiveToExclusive { start: 3, end: 4 }));
        assert!((..=2).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!((..=2).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 2 }));
        assert!((..=2).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 3 }));
        assert!(!(..=2).overlapping(&RangeFromExclusiveToInclusive { start: 2, end: 3 }));
        assert!(!(..=2).overlapping(&RangeFromExclusiveToInclusive { start: 3, end: 4 }));
    }

    #[test]
    fn range_overlapping() {
        assert!((1..4).overlapping(&(..)));
        assert!((1..4).overlapping(&(0..)));
        assert!((1..4).overlapping(&(2..)));
        assert!(!(1..4).overlapping(&(4..)));
        assert!(!(1..4).overlapping(&(5..)));
        assert!(!(1..4).overlapping(&(..0)));
        assert!(!(1..4).overlapping(&(..1)));
        assert!((1..4).overlapping(&(..2)));
        assert!((1..4).overlapping(&(..5)));
        assert!(!(1..4).overlapping(&(..=0)));
        assert!((1..4).overlapping(&(..=1)));
        assert!((1..4).overlapping(&(..=2)));
        assert!((1..4).overlapping(&(..=5)));
        assert!(!(1..4).overlapping(&(0..0)));
        assert!(!(1..4).overlapping(&(0..1)));
        assert!((1..4).overlapping(&(0..2)));
        assert!((1..4).overlapping(&(2..3)));
        assert!((1..4).overlapping(&(1..4)));
        assert!((1..4).overlapping(&(3..5)));
        assert!(!(1..4).overlapping(&(4..6)));
        assert!(!(1..4).overlapping(&(5..6)));
        assert!(!(1..4).overlapping(&(0..=0)));
        assert!((1..4).overlapping(&(0..=1)));
        assert!((1..4).overlapping(&(0..=2)));
        assert!((1..4).overlapping(&(2..=3)));
        assert!((1..4).overlapping(&(1..=4)));
        assert!((1..4).overlapping(&(3..=5)));
        assert!(!(1..4).overlapping(&(4..=6)));
        assert!(!(1..4).overlapping(&(5..=6)));
        assert!((1..4).overlapping(&RangeFromExclusive { start: 0 }));
        assert!((1..4).overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!(1..4).overlapping(&RangeFromExclusive { start: 4 }));
        assert!(!(1..4).overlapping(&RangeFromExclusive { start: 5 }));
        assert!(!(1..4).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 0 }));
        assert!(!(1..4).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 2 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToExclusive { start: 2, end: 3 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 4 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToExclusive { start: 3, end: 5 }));
        assert!(!(1..4).overlapping(&RangeFromExclusiveToExclusive { start: 4, end: 6 }));
        assert!(!(1..4).overlapping(&RangeFromExclusiveToExclusive { start: 5, end: 6 }));
        assert!(!(1..4).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 0 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 2 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToInclusive { start: 2, end: 3 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 4 }));
        assert!((1..4).overlapping(&RangeFromExclusiveToInclusive { start: 3, end: 5 }));
        assert!(!(1..4).overlapping(&RangeFromExclusiveToInclusive { start: 4, end: 6 }));
        assert!(!(1..4).overlapping(&RangeFromExclusiveToInclusive { start: 5, end: 6 }));
    }

    #[test]
    fn range_inclusive_overlapping() {
        assert!((1..=4).overlapping(&(..)));
        assert!((1..=4).overlapping(&(0..)));
        assert!((1..=4).overlapping(&(2..)));
        assert!((1..=4).overlapping(&(4..)));
        assert!(!(1..=4).overlapping(&(5..)));
        assert!(!(1..=4).overlapping(&(..0)));
        assert!(!(1..=4).overlapping(&(..1)));
        assert!((1..=4).overlapping(&(..2)));
        assert!((1..=4).overlapping(&(..5)));
        assert!(!(1..=4).overlapping(&(..=0)));
        assert!((1..=4).overlapping(&(..=1)));
        assert!((1..=4).overlapping(&(..=2)));
        assert!((1..=4).overlapping(&(..=5)));
        assert!(!(1..=4).overlapping(&(0..0)));
        assert!(!(1..=4).overlapping(&(0..1)));
        assert!((1..=4).overlapping(&(0..2)));
        assert!((1..=4).overlapping(&(2..3)));
        assert!((1..=4).overlapping(&(1..4)));
        assert!((1..=4).overlapping(&(3..5)));
        assert!((1..=4).overlapping(&(4..6)));
        assert!(!(1..=4).overlapping(&(5..6)));
        assert!(!(1..=4).overlapping(&(0..=0)));
        assert!((1..=4).overlapping(&(0..=1)));
        assert!((1..=4).overlapping(&(0..=2)));
        assert!((1..=4).overlapping(&(2..=3)));
        assert!((1..=4).overlapping(&(1..=4)));
        assert!((1..=4).overlapping(&(3..=5)));
        assert!((1..=4).overlapping(&(4..=6)));
        assert!(!(1..=4).overlapping(&(5..=6)));
        assert!((1..=4).overlapping(&RangeFromExclusive { start: 0 }));
        assert!((1..=4).overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusive { start: 4 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusive { start: 5 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 0 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 2 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 2, end: 3 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 4 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 3, end: 5 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 4, end: 6 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusiveToExclusive { start: 5, end: 6 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 0 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 2 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 2, end: 3 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 4 }));
        assert!((1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 3, end: 5 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 4, end: 6 }));
        assert!(!(1..=4).overlapping(&RangeFromExclusiveToInclusive { start: 5, end: 6 }));
    }

    #[test]
    fn range_from_exclusive_overlapping() {
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(..)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(0..)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(1..)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(2..)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(..0)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(..1)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(..2)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(..=0)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(..=1)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(..=2)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(0..0)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(0..1)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(0..2)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(1..2)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(0..=0)));
        assert!(!RangeFromExclusive { start: 1 }.overlapping(&(0..=1)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(0..=2)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&(1..=2)));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&RangeFromExclusive { start: 0 }));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&RangeFromExclusive { start: 1 }));
        assert!(RangeFromExclusive { start: 1 }.overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 0 }));
        assert!(!RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!(RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 2 }));
        assert!(RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 2 }));
        assert!(!RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 0 }));
        assert!(!RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!(RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 2 }));
        assert!(RangeFromExclusive { start: 1 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 2 }));
    }

    #[test]
    fn range_from_exclusive_to_exclusive_overlapping() {
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(0..)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(2..)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(4..)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(5..)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..0)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..1)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..2)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..5)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..=0)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..=1)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..=2)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(..=5)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(0..0)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(0..1)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(0..2)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(2..3)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(1..4)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(3..5)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(4..6)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(5..6)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(0..=0)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(0..=1)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(0..=2)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(2..=3)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(1..=4)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(3..=5)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(4..=6)));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }.overlapping(&(5..=6)));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 0 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 4 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 5 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 0 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 2 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 2, end: 3 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 4 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 3, end: 5 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 4, end: 6 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 5, end: 6 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 0 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 2 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 2, end: 3 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 4 }));
        assert!(RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 3, end: 5 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 4, end: 6 }));
        assert!(!RangeFromExclusiveToExclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 5, end: 6 }));
    }

    #[test]
    fn range_from_exclusive_to_inclusive_overlapping() {
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(0..)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(2..)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(4..)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(5..)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..0)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..1)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..2)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..5)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..=0)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..=1)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..=2)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(..=5)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(0..0)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(0..1)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(0..2)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(2..3)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(1..4)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(3..5)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(4..6)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(5..6)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(0..=0)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(0..=1)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(0..=2)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(2..=3)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(1..=4)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(3..=5)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(4..=6)));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }.overlapping(&(5..=6)));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 0 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 2 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 4 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusive { start: 5 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 0 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 1 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 0, end: 2 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 2, end: 3 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 1, end: 4 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 3, end: 5 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 4, end: 6 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToExclusive { start: 5, end: 6 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 0 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 1 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 0, end: 2 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 2, end: 3 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 1, end: 4 }));
        assert!(RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 3, end: 5 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 4, end: 6 }));
        assert!(!RangeFromExclusiveToInclusive { start: 1, end: 4 }
            .overlapping(&RangeFromExclusiveToInclusive { start: 5, end: 6 }));
    }
}

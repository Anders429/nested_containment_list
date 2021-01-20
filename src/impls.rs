#[cfg(not(rustc_1_36))]
extern crate std as core;

use core::ops::Range;
use Interval;

/// A `Range`'s `Interval` is defined to be `[start, end)`, where `start` is the
/// `Range`'s `start` field, and `end` is the `Range`'s `end` field.
impl<B> Interval<B> for Range<B>
where
    B: Copy + Ord,
{
    /// The `start` field.
    fn start(&self) -> B {
        self.start
    }

    /// The `end` field.
    fn end(&self) -> B {
        self.end
    }
}

#[cfg(test)]
mod tests {
    use Interval;

    #[test]
    fn range() {
        let range = 1..2;

        assert_eq!(range.start(), 1);
        assert_eq!(range.end(), 2);
    }
}

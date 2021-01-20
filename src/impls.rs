use std::cmp::max;
use std::cmp::min;
use std::ops::Range;
use Interval;

impl<B> Interval<B> for Range<B>
where
    B: Copy + Ord,
{
    fn left_bound(&self) -> B {
        min(self.start, self.end)
    }

    fn right_bound(&self) -> B {
        max(self.start, self.end)
    }
}

#[cfg(test)]
mod tests {
    use Interval;

    #[test]
    fn range_ascending() {
        let range = 1..2;

        assert_eq!(range.left_bound(), 1);
        assert_eq!(range.right_bound(), 2);
    }

    #[test]
    fn range_descending() {
        let range = 2..1;

        assert_eq!(range.left_bound(), 1);
        assert_eq!(range.right_bound(), 2);
    }
}

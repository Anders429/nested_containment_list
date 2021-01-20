#[cfg(not(rustc_1_36))]
extern crate std as core;

use core::ops::Range;
use Interval;

impl<B> Interval<B> for Range<B>
where
    B: Copy + Ord,
{
    fn start(&self) -> B {
        self.start
    }

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

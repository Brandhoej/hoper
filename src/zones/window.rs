use std::fmt::Display;

use super::delay::Delay;

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub struct Window {
    lower: Delay,
    upper: Delay,
}

impl Window {
    pub fn new(lower: Delay, upper: Delay) -> Self {
        if lower > upper {
            panic!();
        }

        Self { lower, upper }
    }

    pub fn intersections(windows: Vec<Self>) -> Option<Self> {
        // TODO: windows borrowed elements?
        let mut windows = windows.into_iter();
        let first = windows.next()?;

        windows.fold(Some(first), |accumulator, window| {
            accumulator.and_then(|a| a.intersection(&window))
        })
    }

    pub const fn lower(&self) -> Delay {
        self.lower
    }

    pub const fn upper(&self) -> Delay {
        self.upper
    }

    pub fn intersection(&self, other: &Self) -> Option<Self> {
        let (lower, upper) = (self.lower.max(other.lower), self.upper.min(other.upper));
        (lower <= upper).then(|| Window::new(lower, upper))
    }

    pub fn intersects(&self, other: &Self) -> bool {
        self.intersection(other).is_some()
    }
}

impl Display for Window {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lower, self.upper)
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use crate::zones::{delay::Delay, window::Window};

    #[test]
    fn intersection() {
        assert_eq!(
            "[0, 1]",
            Window::new(Delay::exact(0), Delay::exact(2))
                .intersection(&Window::new(Delay::exact(0), Delay::exact(1)))
                .unwrap()
                .to_string()
        )
    }
}

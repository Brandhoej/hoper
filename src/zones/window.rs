use std::fmt::{Display, Formatter};

use super::delay::Delay;

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub struct Window {
    lower: Delay,
    upper: Delay,
}

impl Window {
    pub fn new(lower: Delay, upper: Delay) -> Result<Window, ()> {
        if lower.is_infinite() && !upper.is_infinite() {
            return Err(())
        }

        if let (Some(a), Some(b)) = (lower.limit(), upper.limit()) {
            if a > b {
                return Err(());
            }
        }

        if lower.limit() == upper.limit() && (lower.is_tightened() || upper.is_tightened()) {
            return Err(());
        }

        let window = Self { lower, upper };
        Ok(window)
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

    pub fn is_zero(&self) -> bool {
        self.lower.limit() == Some(0) && self.upper.limit() == Some(0)
    }

    pub fn intersection(&self, other: &Self) -> Option<Self> {
        let (lower, upper) = (self.lower.max(other.lower), self.upper.min(other.upper));
        match Window::new(lower, upper) {
            Ok(window) => Some(window),
            Err(_) => None,
        }
    }

    pub fn intersects(&self, other: &Self) -> bool {
        self.intersection(other).is_some()
    }
}

impl Display for Window {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.lower, self.upper)
    }
}

#[cfg(test)]
mod tests {
    use crate::zones::{delay::Delay, window::Window};

    #[test]
    fn intersection() {
        assert_eq!(
            "0..1",
            Window::new(Delay::exact(0), Delay::exact(2))
                .unwrap()
                .intersection(&Window::new(Delay::exact(0), Delay::exact(1)).unwrap())
                .unwrap()
                .to_string()
        );
        assert!(Window::new(Delay::exact(0), Delay::exact(2))
            .unwrap()
            .intersection(&Window::new(Delay::tighten(2), Delay::infinite()).unwrap())
            .is_none());
    }

    #[test]
    fn display() {
        assert_eq!(
            "0..2",
            Window::new(Delay::exact(0), Delay::exact(2))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "2↓..∞↑",
            Window::new(Delay::tighten(2), Delay::infinite())
                .unwrap()
                .to_string()
        );
    }
}

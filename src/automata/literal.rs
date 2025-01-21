use crate::zones::constraint::{Clock, REFERENCE};

#[derive(Clone)]
pub enum Literal {
    Boolean(bool),
    Clock(Clock),
    I16(i16),
}

impl Literal {
    #[inline]
    pub const fn new_boolean(value: bool) -> Self {
        Self::Boolean(value)
    }

    #[inline]
    pub const fn new_true() -> Self {
        Self::new_boolean(true)
    }

    #[inline]
    pub const fn new_false() -> Self {
        Self::new_boolean(false)
    }

    #[inline]
    pub const fn new_clock(clock: Clock) -> Self {
        Self::Clock(clock)
    }

    #[inline]
    pub const fn new_reference_clock() -> Self {
        Self::new_clock(REFERENCE)
    }

    #[inline]
    pub const fn new_i16(value: i16) -> Self {
        Self::I16(value)
    }

    #[inline]
    pub const fn boolean(&self) -> Option<bool> {
        if let Self::Boolean(value) = self {
            return Some(*value);
        }
        None
    }

    #[inline]
    pub const fn clock(&self) -> Option<Clock> {
        if let Self::Clock(clock) = self {
            return Some(*clock);
        }
        None
    }

    #[inline]
    pub const fn i16(&self) -> Option<i16> {
        if let Self::I16(value) = self {
            return Some(*value);
        }
        None
    }
}

impl From<bool> for Literal {
    fn from(value: bool) -> Self {
        Self::new_boolean(value)
    }
}

use super::expressions::Unary;

#[derive(Clone)]
pub enum Literal {
    Boolean(bool),
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
    pub const fn boolean(&self) -> Option<bool> {
        if let Self::Boolean(value) = self {
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

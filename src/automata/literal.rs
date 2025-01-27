use std::fmt::Display;

use symbol_table::Symbol;

#[derive(Clone, Debug)]
pub enum Literal {
    Boolean(bool),
    I16(i16),
    Identifier(Symbol),
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
    pub const fn new_identifier(clock: Symbol) -> Self {
        Self::Identifier(clock)
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
    pub const fn identifier(&self) -> Option<Symbol> {
        if let Self::Identifier(ident) = self {
            return Some(*ident);
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

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Boolean(boolean) => write!(f, "{}", *boolean),
            Literal::I16(number) => write!(f, "{}", *number),
            Literal::Identifier(ident) => write!(f, "{:?}", *ident),
        }
    }
}

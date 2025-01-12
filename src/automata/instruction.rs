pub struct Instruction(u8);

/// Halts the program execution immediately.
pub const HALT: Instruction = Instruction(0x00);
/// No operation. Advances the program counter without performing any action.
pub const NOP: Instruction = Instruction(0x01);

/* Logical instructions */
pub const AND: Instruction = Instruction(0x10);
pub const OR: Instruction = Instruction(0x11);
pub const NOT: Instruction = Instruction(0x12);
pub const XOR: Instruction = Instruction(0x13);

/* Stack instructions */
pub const PUSH_HW: Instruction = Instruction(0xF0);
pub const POP_HW: Instruction = Instruction(0xF1);
pub const PUSH_W: Instruction = Instruction(0xF2);
pub const POP_W: Instruction = Instruction(0xF3);
pub const PUSH_D: Instruction = Instruction(0xF4);
pub const POP_D: Instruction = Instruction(0xF5);
pub const PUSH_Q: Instruction = Instruction(0xF6);
pub const POP_Q: Instruction = Instruction(0xF7);

/* Clock instructions */
/// Tests the diagonal clock constraint: `rA - rB < I`. m
pub const DCLK_LE: Instruction = Instruction(0xE0);
/// Tests the diagonal clock constraint: `rA - rB < I`.
pub const DCLK_LT: Instruction = Instruction(0xE1);
/// Tests the diagonal clock constraint: `rA - rB = I`.
pub const DCLK_EQ: Instruction = Instruction(0xE2);
/// Tests the diagonal clock constraint: `rA - rB > I`.
pub const DCLK_GT: Instruction = Instruction(0xE3);
/// Tests the diagonal clock constraint: `rA - rB ≥ I`.
pub const DCLK_GE: Instruction = Instruction(0xE4);
/// Tests the clock's upper bound: `rB ≤ I`.
pub const CLK_LE: Instruction = Instruction(0xE5);
/// Tests the clock's upper bound: `rB < I`.
pub const CLK_LT: Instruction = Instruction(0xE6);
/// Tests the clock's valuation equality: `rA = I`.
pub const CLK_EQ: Instruction = Instruction(0xE7);
/// Tests the clock's lower bound: `rA > I`.
pub const CLK_GT: Instruction = Instruction(0xE8);
/// Tests the clock's lower bound: `rA ≥ I`.
pub const CLK_GE: Instruction = Instruction(0xE9);
/// Removes all constraints on a given clock: `{u[x=d] | u ∈ D, d ∈ ℝ+}`.
pub const CLK_FREE: Instruction = Instruction(0xEA);
/// Sets the clock to be assigned to its limit: `{u[x=m] | u ∈ D}`.
pub const CLK_RESET: Instruction = Instruction(0xEB);
/// Sets the lhs to be equal to the rhs: `{u[x=u(y)] | u ∈ D, x ∈ D}`.
pub const CLK_CPY: Instruction = Instruction(0xEC);
/// Compound addition assignment of the clock "clock = clock + limit".
pub const CLK_SHIFT: Instruction = Instruction(0xED);

impl From<Instruction> for u8 {
    fn from(value: Instruction) -> Self {
        value.0
    }
}

macro_rules! define_immediate {
    ($struct_name:ident, $unsigned_type:ty, $signed_type:ty) => {
        pub struct $struct_name($unsigned_type);

        impl From<$struct_name> for $unsigned_type {
            fn from(value: $struct_name) -> Self {
                value.0
            }
        }

        impl From<$unsigned_type> for $struct_name {
            fn from(value: $unsigned_type) -> Self {
                Self(value)
            }
        }

        impl From<$struct_name> for $signed_type {
            fn from(value: $struct_name) -> Self {
                value.0 as $signed_type
            }
        }

        impl From<$signed_type> for $struct_name {
            fn from(value: $signed_type) -> Self {
                Self(value as $unsigned_type)
            }
        }
    };
}

define_immediate!(HalfWord, u8, i8);
define_immediate!(Word, u16, i16);
define_immediate!(DoubleWord, u32, i32);
define_immediate!(QuadWord, u64, i64);

impl From<[u8; 1]> for HalfWord {
    fn from(value: [u8; 1]) -> Self {
        Self(value[0])
    }
}

impl From<HalfWord> for [u8; 1] {
    fn from(value: HalfWord) -> Self {
        [value.0]
    }
}

impl From<[u8; 2]> for Word {
    fn from(value: [u8; 2]) -> Self {
        Self(((value[1] as u16) << 8) | (value[0] as u16))
    }
}

impl From<Word> for [u8; 2] {
    fn from(value: Word) -> Self {
        [(value.0 & 0xFF) as u8, ((value.0 >> 8) & 0xFF) as u8]
    }
}

impl From<[u8; 4]> for DoubleWord {
    fn from(value: [u8; 4]) -> Self {
        Self(
            ((value[3] as u32) << 24)
                | ((value[2] as u32) << 16)
                | ((value[1] as u32) << 8)
                | (value[0] as u32),
        )
    }
}

impl From<DoubleWord> for [u8; 4] {
    fn from(value: DoubleWord) -> Self {
        [
            (value.0 & 0xFF) as u8,
            ((value.0 >> 8) & 0xFF) as u8,
            ((value.0 >> 16) & 0xFF) as u8,
            ((value.0 >> 24) & 0xFF) as u8,
        ]
    }
}

impl From<[u8; 8]> for QuadWord {
    fn from(value: [u8; 8]) -> Self {
        Self(
            ((value[7] as u64) << 56)
                | ((value[6] as u64) << 48)
                | ((value[5] as u64) << 40)
                | ((value[4] as u64) << 32)
                | ((value[3] as u64) << 24)
                | ((value[2] as u64) << 16)
                | ((value[1] as u64) << 8)
                | (value[0] as u64),
        )
    }
}

impl From<QuadWord> for [u8; 8] {
    fn from(value: QuadWord) -> Self {
        [
            (value.0 & 0xFF) as u8,
            ((value.0 >> 8) & 0xFF) as u8,
            ((value.0 >> 16) & 0xFF) as u8,
            ((value.0 >> 24) & 0xFF) as u8,
            ((value.0 >> 32) & 0xFF) as u8,
            ((value.0 >> 40) & 0xFF) as u8,
            ((value.0 >> 48) & 0xFF) as u8,
            ((value.0 >> 56) & 0xFF) as u8,
        ]
    }
}

#[cfg(test)]
mod tests {
    use crate::automata::instruction::{DoubleWord, HalfWord, QuadWord, Word};

    #[test]
    fn quadword_conversions() {
        assert_eq!(-1i64, QuadWord::from(-1i64).into());
        assert_eq!(1i64, QuadWord::from(1i64).into());
        assert_eq!(i64::MIN, QuadWord::from(i64::MIN).into());
        assert_eq!(i64::MAX, QuadWord::from(i64::MAX).into());

        assert_eq!(1u64, QuadWord::from(1u64).into());
        assert_eq!(u64::MIN, QuadWord::from(u64::MIN).into());
        assert_eq!(u64::MAX, QuadWord::from(u64::MAX).into());
    }

    #[test]
    fn doubleword_conversions() {
        assert_eq!(-1i32, DoubleWord::from(-1i32).into());
        assert_eq!(1i32, DoubleWord::from(1i32).into());
        assert_eq!(i32::MIN, DoubleWord::from(i32::MIN).into());
        assert_eq!(i32::MAX, DoubleWord::from(i32::MAX).into());

        assert_eq!(1u32, DoubleWord::from(1u32).into());
        assert_eq!(u32::MIN, DoubleWord::from(u32::MIN).into());
        assert_eq!(u32::MAX, DoubleWord::from(u32::MAX).into());
    }

    #[test]
    fn word_conversions() {
        assert_eq!(-1i16, Word::from(-1i16).into());
        assert_eq!(1i16, Word::from(1i16).into());
        assert_eq!(i16::MIN, Word::from(i16::MIN).into());
        assert_eq!(i16::MAX, Word::from(i16::MAX).into());

        assert_eq!(1u16, Word::from(1u16).into());
        assert_eq!(u16::MIN, Word::from(u16::MIN).into());
        assert_eq!(u16::MAX, Word::from(u16::MAX).into());
    }

    #[test]
    fn half_word_conversions() {
        assert_eq!(-1i8, HalfWord::from(-1i8).into());
        assert_eq!(1i8, HalfWord::from(1i8).into());
        assert_eq!(i8::MIN, HalfWord::from(i8::MIN).into());
        assert_eq!(i8::MAX, HalfWord::from(i8::MAX).into());

        assert_eq!(1u8, HalfWord::from(1u8).into());
        assert_eq!(u8::MIN, HalfWord::from(u8::MIN).into());
        assert_eq!(u8::MAX, HalfWord::from(u8::MAX).into());
    }
}

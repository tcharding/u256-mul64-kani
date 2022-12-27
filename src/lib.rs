use std::fmt;
use std::ops::{Add, Div, Rem, Not, Shl, Shr};

/// Big-endian 256 bit integer type.
// (high, low): u.0 contains the high bits, u.1 contains the low bits.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct U256(u128, u128);

const MASK: u64 = u64::MAX; // 0xFFFF_FFFF_FFFF_FFFF

impl U256 {
    const ZERO: U256 = U256(0, 0);
    const ONE: U256 = U256(0, 1);

    /// Returns the low 128 bits.
    fn low_u128(&self) -> u128 { self.1 }

    /// Calculates `self` + `rhs`
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is returned.
    #[must_use = "this returns the result of the operation, without modifying the original"]
    fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let mut ret = U256::ZERO;
        let mut ret_overflow = false;

        let (high, overflow) = self.0.overflowing_add(rhs.0);
        ret.0 = high;
        ret_overflow |= overflow;

        let (low, overflow) = self.1.overflowing_add(rhs.1);
        ret.1 = low;
        if overflow {
            let (high, overflow) = ret.0.overflowing_add(1);
            ret.0 = high;
            ret_overflow |= overflow;
        }

        (ret, ret_overflow)
    }

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the
    /// type.
    #[must_use = "this returns the result of the operation, without modifying the original"]
    fn wrapping_add(self, rhs: Self) -> Self {
        let (ret, _overflow) = self.overflowing_add(rhs);
        ret
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the boundary of
    /// the type.
    #[must_use = "this returns the result of the operation, without modifying the original"]
    fn wrapping_sub(self, rhs: Self) -> Self {
        let (ret, _overflow) = self.overflowing_sub(rhs);
        ret
    }

    /// Calculates `self` - `rhs`
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is returned.
    #[must_use = "this returns the result of the operation, without modifying the original"]
    fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let ret = self.wrapping_add(!rhs).wrapping_add(Self::ONE);
        let overflow = rhs > self;
        (ret, overflow)
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where `mask` removes any
    /// high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-left; the RHS of a wrapping shift-left is
    /// restricted to the range of the type, rather than the bits shifted out of the LHS being
    /// returned to the other end. We do not currently support `rotate_left`.
    #[must_use = "this returns the result of the operation, without modifying the original"]
    fn wrapping_shl(self, rhs: u32) -> Self {
        let shift = rhs & 0x000000ff;

        let mut ret = U256::ZERO;
        let word_shift = shift >= 128;
        let bit_shift = shift % 128;

        if word_shift {
            ret.0 = self.1 << bit_shift
        } else {
            ret.0 = self.0 << bit_shift;
            if bit_shift > 0 {
                ret.0 += self.1.wrapping_shr(128 - bit_shift);
            }
            ret.1 = self.1 << bit_shift;
        }
        ret
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where `mask` removes any
    /// high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-right; the RHS of a wrapping shift-right is
    /// restricted to the range of the type, rather than the bits shifted out of the LHS being
    /// returned to the other end. We do not currently support `rotate_right`.
    #[must_use = "this returns the result of the operation, without modifying the original"]
    fn wrapping_shr(self, rhs: u32) -> Self {
        let shift = rhs & 0x000000ff;

        let mut ret = U256::ZERO;
        let word_shift = shift >= 128;
        let bit_shift = shift % 128;

        if word_shift {
            ret.1 = self.0 >> bit_shift
        } else {
            ret.0 = self.0 >> bit_shift;
            ret.1 = self.1 >> bit_shift;
            if bit_shift > 0 {
                ret.1 += self.0.wrapping_shl(128 - bit_shift);
            }
        }
        ret
    }

    /// Wrapping multiplication by `u64`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is returned.
    pub fn mul_u64(self, rhs: u64) -> (U256, bool) {
        if self.is_zero() || rhs == 0 {
            return (U256::ZERO, false);
        }

        let mut ret_overflow = false;

        let (d, c) = split(self.0);
        let (b, a) = split(self.1);
        let parts = vec![a, b, c, d]; // self as a little-endian array of u64s

        let mut ret = U256::ZERO;
        let mut shift = 0;
        let mut prev_carry = 0_u64;
        let mut prev_high = 0_u64;

        for p in parts {
            let r = (p as u128) * (rhs as u128); // Cannot overlflow 128 bits.
            let (h, l) = split(r);
            let (carry, high, low) = add(h, l, prev_carry, prev_high); // h << 64 + l + high << 64 + low

            ret = ret + U256::from(low) << shift;
            shift += 64;
            prev_carry = carry;
            prev_high = high;
        }

        if prev_carry > 0 || prev_high > 0 {
            ret_overflow = true;
        }

        (ret, ret_overflow)
    }

    /// Calculates quotient and remainder.
    ///
    /// # Returns
    ///
    /// (quotient, remainder)
    ///
    /// # Panics
    ///
    /// If `rhs` is zero.
    fn div_rem(self, rhs: Self) -> (Self, Self) {
        let mut sub_copy = self;
        let mut shift_copy = rhs;
        let mut ret = [0u128; 2];

        let my_bits = self.bits();
        let your_bits = rhs.bits();

        // Check for division by 0
        assert!(your_bits != 0, "attempted to divide {} by zero", self);

        // Early return in case we are dividing by a larger number than us
        if my_bits < your_bits {
            return (U256::ZERO, sub_copy);
        }

        // Bitwise long division
        let mut shift = my_bits - your_bits;
        shift_copy = shift_copy << shift;
        loop {
            if sub_copy >= shift_copy {
                ret[1 - (shift / 128) as usize] |= 1 << (shift % 128);
                sub_copy = sub_copy.wrapping_sub(shift_copy);
            }
            shift_copy = shift_copy >> 1;
            if shift == 0 {
                break;
            }
            shift -= 1;
        }

        (U256(ret[0], ret[1]), sub_copy)
    }

    /// Returns the least number of bits needed to represent the number.
    fn bits(&self) -> u32 {
        if self.0 > 0 {
            256 - self.0.leading_zeros()
        } else {
            128 - self.1.leading_zeros()
        }
    }

    /// Format `self` to `f` as a decimal when value is known to be non-zero.
    fn fmt_decimal(&self, f: &mut fmt::Formatter) -> fmt::Result {
        const DIGITS: usize = 78; // U256::MAX has 78 base 10 digits.
        const TEN: U256 = U256(0, 10);

        let mut buf = [0_u8; DIGITS];
        let mut i = DIGITS - 1; // We loop backwards.
        let mut cur = *self;

        loop {
            let digit = (cur % TEN).low_u128() as u8; // Cast after rem 10 is lossless.
            buf[i] = digit + b'0';
            cur = cur / TEN;
            if cur.is_zero() {
                break;
            }
            i -= 1;
        }
        let s = core::str::from_utf8(&buf[i..]).expect("digits 0-9 are valid UTF8");
        f.pad_integral(true, "", s)
    }

    pub fn is_zero(&self) -> bool { self.0 == 0 && self.1 == 0 }
}

fn split(x: u128) -> (u64, u64) {
    let high = (x >> 64) as u64;
    let low = (x & MASK as u128) as u64;
    (high, low)
}

// Calculates xhigh << 64 + xlow + yhigh << 64 + yhigh returning the result as (carry, high, low).
fn add(xhigh: u64, xlow: u64, yhigh: u64, ylow: u64) -> (u64, u64, u64) {
    let rlow = xlow as u128 + ylow as u128;
    let low = (rlow & MASK as u128) as u64;
    let carry_low = rlow >> 64;

    let rhigh = xhigh as u128 + yhigh as u128;
    let r = rhigh + carry_low;

    let carry = (r >> 64) as u64;
    let high = (r & MASK as u128) as u64;

    (carry, high, low)
}

impl<T: Into<u128>> From<T> for U256 {
    fn from(x: T) -> Self { U256(0, x.into()) }
}

impl fmt::Display for U256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_zero() {
            f.pad_integral(true, "", "0")
        } else {
            self.fmt_decimal(f)
        }
    }
}

impl Add for U256 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (res, overflow) = self.overflowing_add(rhs);
        debug_assert!(!overflow, "Addition of U256 values overflowed");
        res
    }
}

impl Div for U256 {
    type Output = Self;
    fn div(self, rhs: Self) -> Self { self.div_rem(rhs).0 }
}

impl Rem for U256 {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self { self.div_rem(rhs).1 }
}

impl Not for U256 {
    type Output = Self;

    fn not(self) -> Self { U256(!self.0, !self.1) }
}

impl Shl<u32> for U256 {
    type Output = Self;
    fn shl(self, shift: u32) -> U256 { self.wrapping_shl(shift) }
}

impl Shr<u32> for U256 {
    type Output = Self;
    fn shr(self, shift: u32) -> U256 { self.wrapping_shr(shift) }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Proves we only need three u64s to return the result of `add`.
    #[test]
    fn add_max_max_max_max() {
        let (carry, high, low) = add(u64::MAX, u64::MAX, u64::MAX, u64::MAX);
        assert_eq!(carry, 1);
        assert_eq!(high, u64::MAX);
        assert_eq!(low, u64::MAX - 1);
    }
}

#[cfg(kani)]
mod verification {
    use super::*;

    #[cfg(kani)]
    #[kani::proof]
    fn check_mul_u64() {
        let x: u128 = kani::any();
        let y: u64 = kani::any();

        let x = U256::from(x);

        x.mul_u64(y);
    }

    #[cfg(kani)]
    #[kani::proof]
    fn check_add() {
        let x: u128 = kani::any();
        let y: u128 = kani::any();

        let (xhigh, xlow) = split(x);
        let (yhigh, ylow) = split(y);

        let (carry, high, low) = add(xhigh, xlow, yhigh, ylow);

        let (want, overflow) = x.overflowing_add(y);
        if !overflow {
            assert_eq!(carry, 0);

            let got = ((high as u128) << 64) + low as u128;
            assert_eq!(got, want)
        }
    }

    #[cfg(kani)]
    #[kani::proof]
    fn check_mul_div() {
        let x: u128 = kani::any();
        let y: u64 = kani::any();

        let x = U256::from(x);
        let (res, overflow) = x.mul_u64(y);

        if !overflow {
            assert_eq!(res / U256::from(y), x)
        }
    }
}

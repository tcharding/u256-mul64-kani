use std::ops::{Add, Shl};

/// Big-endian 256 bit integer type.
// (high, low): u.0 contains the high bits, u.1 contains the low bits.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct U256(u128, u128);

const MASK: u64 = u64::MAX; // 0xFFFF_FFFF_FFFF_FFFF

impl U256 {
    const ZERO: U256 = U256(0, 0);

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

impl Add for U256 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (res, overflow) = self.overflowing_add(rhs);
        debug_assert!(!overflow, "Addition of U256 values overflowed");
        res
    }
}

impl Shl<u32> for U256 {
    type Output = Self;
    fn shl(self, shift: u32) -> U256 { self.wrapping_shl(shift) }
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
}

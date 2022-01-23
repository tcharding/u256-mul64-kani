/// Big-endian 256 bit integer type.
// (high, low): u.0 contains the high bits, u.1 contains the low bits.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct U256(u128, u128);

impl U256 {
    const ZERO: U256 = U256(0, 0);

    /// Wrapping multiplication by `u64`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is returned.
    pub fn mul_u64(self, rhs: u64) -> (U256, bool) {
        // Multiply 64 bit parts of `mul` by `rhs`.
        fn mul_parts(mul: u128, rhs: u64) -> (u128, u128) {
            let upper = (rhs as u128) * (mul >> 64);
            let lower = (rhs as u128) * (mul & 0xFFFF_FFFF_FFFF_FFFF);
            (upper, lower)
        }

        if self.is_zero() || rhs == 0 {
            return (U256::ZERO, false);
        }

        let mut ret = U256::ZERO;
        let mut ret_overflow = false;

        let (upper, lower) = mul_parts(self.0, rhs);
        ret.0 = lower + (upper << 64);
        ret_overflow |= upper >> 64 > 0;

        let (upper, lower) = mul_parts(self.1, rhs);
        ret.1 = lower + (upper << 64);
        ret.0 += upper >> 64;

        (ret, ret_overflow)
    }

    pub fn is_zero(&self) -> bool { self.0 == 0 && self.1 == 0 }
}

impl<T: Into<u128>> From<T> for U256 {
    fn from(x: T) -> Self { U256(0, x.into()) }
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
}

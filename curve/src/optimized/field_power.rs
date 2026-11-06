//! Field exponentiation with direct initialization from the first set bit.
use crate::{field::Fp, Field};

fn exponent_bit(exponent: [u64; 6], index: u32) -> bool {
    ((exponent[(index / 64) as usize] >> (index % 64)) & 1) == 1
}

fn pow_loop(a: Fp, exponent: [u64; 6], bits: u32, started: bool, acc: Fp) -> Fp {
    if bits == 0 {
        return acc;
    }
    let bit = bits - 1;
    let set = exponent_bit(exponent, bit);
    if !started {
        if set {
            return pow_loop(a, exponent, bit, true, a);
        }
        return pow_loop(a, exponent, bit, false, acc);
    }
    let squared = acc.square();
    let next = if set { squared.times(a) } else { squared };
    pow_loop(a, exponent, bit, true, next)
}

/// Same full six-word exponent contract as `field::pow`.
/// For nonzero exponents, saves the original first square of one and multiply by a.
pub fn pow(a: Fp, exponent: [u64; 6]) -> Fp {
    pow_loop(a, exponent, 384, false, Fp::constant(1))
}

//! LSB-first exponentiation: square the running base, not the accumulator.
use crate::{field::Fp, Field};

fn exponent_bit(exponent: [u64; 6], index: u32) -> bool {
    ((exponent[(index / 64) as usize] >> (index % 64)) & 1) == 1
}

fn pow_loop(power: Fp, exponent: [u64; 6], index: u32, acc: Fp) -> Fp {
    if index == 384 {
        return acc;
    }
    let next = if exponent_bit(exponent, index) {
        acc.times(power)
    } else {
        acc
    };
    pow_loop(power.square(), exponent, index + 1, next)
}

/// Process all 384 bits from low to high, including leading zeros.
/// This is an equivalence example, not a claim of improved performance.
pub fn pow(a: Fp, exponent: [u64; 6]) -> Fp {
    pow_loop(a, exponent, 0, Fp::constant(1))
}

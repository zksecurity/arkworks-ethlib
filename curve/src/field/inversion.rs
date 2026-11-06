//! ark-ff 0.5.0 binary extended-GCD inversion, specialized to six BLS12-381 limbs.
use super::{add_raw, halve, less, subtract, Fp, MODULUS};
use crate::{montgomery, Field};

pub fn is_one(a: [u64; 6]) -> bool {
    a[0] == 1 && a[1] == 0 && a[2] == 0 && a[3] == 0 && a[4] == 0 && a[5] == 0
}

/// The modulus has a spare bit, so adding it before division cannot overflow.
pub fn half_coefficient(b: Fp) -> Fp {
    if b.limbs[0] & 1 == 0 {
        Fp {
            limbs: halve(b.limbs),
        }
    } else {
        Fp {
            limbs: halve(add_raw(b.limbs, MODULUS)),
        }
    }
}

/// MontConfig::inverse, retaining the two normalization loops and subtraction order.
pub fn inverse(a: Fp) -> Option<Fp> {
    if a.is_zero() {
        return None;
    }
    let mut u = a.limbs;
    let mut v = MODULUS;
    let mut b = Fp {
        limbs: montgomery::R2,
    };
    let mut c = Fp { limbs: [0; 6] };
    while !is_one(u) && !is_one(v) {
        while u[0] & 1 == 0 {
            u = halve(u);
            b = half_coefficient(b);
        }
        while v[0] & 1 == 0 {
            v = halve(v);
            c = half_coefficient(c);
        }
        if less(v, u) {
            u = subtract(u, v);
            b = b.minus(c);
        } else {
            v = subtract(v, u);
            c = c.minus(b);
        }
    }
    if is_one(u) {
        Some(b)
    } else {
        Some(c)
    }
}

//! BLS12-381 G1 endomorphism from ark-bls12-381 0.5.0 `curves/g1.rs`.
//!
//! The source GLV path is separate from the live integer multiplication API.
use crate::{field::Fp, AffinePoint, Field, Point};

pub mod arithmetic;

pub use crate::field::G1_BETA as BETA;

#[derive(Clone, Copy)]
pub struct SignedScalar {
    pub positive: bool,
    pub magnitude: [u64; 4],
}

/// Canonical integer view of the source Fr input conversion.
pub fn reduce_scalar(k: [u64; 4]) -> [u64; 4] {
    let (_, r) = arithmetic::div_rem([k[0], k[1], k[2], k[3], 0, 0], arithmetic::ORDER);
    [r[0], r[1], r[2], r[3]]
}

/// One position of ark-ff's four-word big-endian bit iterator.
pub fn scalar_bit(k: [u64; 4], index: u32) -> bool {
    ((k[(index / 64) as usize] >> (index % 64)) & 1) == 1
}

fn loop_bits(
    k1: [u64; 4],
    k2: [u64; 4],
    b1: Point<Fp>,
    b2: Point<Fp>,
    b1b2: Point<Fp>,
    bits: u32,
    skip_zeros: bool,
    res: Point<Fp>,
) -> Point<Fp> {
    if bits == 0 {
        return res;
    }
    let bit = bits - 1;
    let a = scalar_bit(k1, bit);
    let b = scalar_bit(k2, bit);
    if skip_zeros && !a && !b {
        return loop_bits(k1, k2, b1, b2, b1b2, bit, false, res);
    }
    let res = crate::double(res);
    let res = if a {
        if b {
            crate::add(res, b1b2)
        } else {
            crate::add(res, b1)
        }
    } else if b {
        crate::add(res, b2)
    } else {
        res
    };
    loop_bits(k1, k2, b1, b2, b1b2, bit, skip_zeros, res)
}

/// Source GLV loop after decomposition, including its exact skip-flag update.
pub fn mul_decomposed(p: Point<Fp>, k1: SignedScalar, k2: SignedScalar) -> Point<Fp> {
    let mut b1 = p;
    let mut b2 = endomorphism(p);
    if !k1.positive {
        b1 = crate::negate(b1);
    }
    if !k2.positive {
        b2 = crate::negate(b2);
    }
    let b1b2 = crate::add(b1, b2);
    loop_bits(
        k1.magnitude,
        k2.magnitude,
        b1,
        b2,
        b1b2,
        256,
        true,
        crate::identity(),
    )
}

/// Source scalar reduction, decomposition and projective GLV path.
pub fn mul_projective(p: Point<Fp>, k: [u64; 4]) -> Point<Fp> {
    let k = reduce_scalar(k);
    let (k1, k2) = scalar_decomposition(k).unwrap();
    mul_decomposed(p, k1, k2)
}

/// Source signed decomposition, specialized to a canonical scalar input.
/// The proved second quotient is zero, so its zero products are omitted.
/// Noncanonical inputs are rejected before entering the bounded integer backend.
pub fn scalar_decomposition(k: [u64; 4]) -> Option<(SignedScalar, SignedScalar)> {
    use crate::field::less;
    let words = [k[0], k[1], k[2], k[3], 0, 0];
    if !less(words, arithmetic::ORDER) {
        return None;
    }
    let numerator = arithmetic::multiply_128(k, [0xffffffff, 0xac45a4010001a402]);
    let beta1 = arithmetic::rounded_quotient(numerator);
    let b1 = arithmetic::multiply_128(
        [beta1[0], beta1[1], beta1[2], beta1[3]],
        [0x100000000, 0xac45a4010001a402],
    );
    Some((
        signed_difference(words, b1),
        SignedScalar {
            positive: false,
            magnitude: [beta1[0], beta1[1], beta1[2], beta1[3]],
        },
    ))
}

/// Signed difference for values below 2^256; zero has a false positive flag.
pub fn signed_difference(a: [u64; 6], b: [u64; 6]) -> SignedScalar {
    use crate::field::{less, subtract};
    let positive = less(b, a);
    let magnitude = if less(a, b) {
        subtract(b, a)
    } else {
        subtract(a, b)
    };
    SignedScalar {
        positive,
        magnitude: [magnitude[0], magnitude[1], magnitude[2], magnitude[3]],
    }
}

/// Preserve every coordinate except x, including nonstandard infinity encodings.
pub fn endomorphism(p: Point<Fp>) -> Point<Fp> {
    let mut res = p;
    res.x = res.x.times(BETA);
    res
}

/// The affine variant retains the upstream infinity flag and stored coordinates.
pub fn endomorphism_affine(p: AffinePoint<Fp>) -> AffinePoint<Fp> {
    let mut res = p;
    res.x = res.x.times(BETA);
    res
}

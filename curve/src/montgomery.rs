//! ark-ff 0.5.0's portable no-carry CIOS multiplication and Montgomery conversion,
//! specialized to six limbs for the BLS12-381 field backend.
//! Upstream's unroll macro already expands both six-iteration loops; we spell out
//! that expansion and return carry values rather than mutating borrowed scalars.
use crate::field::{less, subtract, MODULUS};

pub const INV: u64 = 0x89f3fffcfffcfffd;
pub const R: [u64; 6] = [
    0x760900000002fffd,
    0xebf4000bc40c0002,
    0x5f48985753c758ba,
    0x77ce585370525745,
    0x5c071a97a256ec6d,
    0x15f65ec3fa80e493,
];
pub const R2: [u64; 6] = [
    0xf4df1f341c341746,
    0x0a76e6a609d104f1,
    0x8de5476c4c95b6d5,
    0x67eb88a9939d83c0,
    0x9a793e85b519952d,
    0x11988fe592cae3aa,
];

/// A single upstream outer-loop boundary, before conditional subtraction.
#[derive(Clone, Copy)]
pub struct Round {
    pub limbs: [u64; 6],
    pub factor: u64,
    pub discarded: u64,
    pub product_carry: u64,
    pub reduction_carry: u64,
}

/// ark_ff::biginteger::arithmetic::mac_with_carry (also mac when carry=0).
pub fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let tmp = a as u128 + b as u128 * c as u128 + carry as u128;
    (tmp as u64, (tmp >> 64) as u64)
}

pub fn round(a: [u64; 6], digit: u64, r: [u64; 6]) -> Round {
    let (t0, c1) = mac(r[0], a[0], digit, 0);
    let k = t0.wrapping_mul(INV);
    let (discarded, c2) = mac(t0, k, MODULUS[0], 0);
    let (t1, c1) = mac(r[1], a[1], digit, c1);
    let (o0, c2) = mac(t1, k, MODULUS[1], c2);
    let (t2, c1) = mac(r[2], a[2], digit, c1);
    let (o1, c2) = mac(t2, k, MODULUS[2], c2);
    let (t3, c1) = mac(r[3], a[3], digit, c1);
    let (o2, c2) = mac(t3, k, MODULUS[3], c2);
    let (t4, c1) = mac(r[4], a[4], digit, c1);
    let (o3, c2) = mac(t4, k, MODULUS[4], c2);
    let (t5, c1) = mac(r[5], a[5], digit, c1);
    let (o4, c2) = mac(t5, k, MODULUS[5], c2);
    Round {
        limbs: [o0, o1, o2, o3, o4, c1 + c2],
        factor: k,
        discarded,
        product_carry: c1,
        reduction_carry: c2,
    }
}

pub fn reduce(r: [u64; 6]) -> [u64; 6] {
    if !less(r, MODULUS) {
        subtract(r, MODULUS)
    } else {
        r
    }
}

/// Actual arithmetic path; inputs are canonical Montgomery residues less than p.
pub fn multiply(a: [u64; 6], b: [u64; 6]) -> [u64; 6] {
    let r0 = round(a, b[0], [0; 6]);
    let r1 = round(a, b[1], r0.limbs);
    let r2 = round(a, b[2], r1.limbs);
    let r3 = round(a, b[3], r2.limbs);
    let r4 = round(a, b[4], r3.limbs);
    let r5 = round(a, b[5], r4.limbs);
    reduce(r5.limbs)
}

/// Observe the same arithmetic routine at each of the six round boundaries.
pub fn trace(a: [u64; 6], b: [u64; 6]) -> [Round; 6] {
    let r0 = round(a, b[0], [0; 6]);
    let r1 = round(a, b[1], r0.limbs);
    let r2 = round(a, b[2], r1.limbs);
    let r3 = round(a, b[3], r2.limbs);
    let r4 = round(a, b[4], r3.limbs);
    let r5 = round(a, b[5], r4.limbs);
    [r0, r1, r2, r3, r4, r5]
}

/// One actual cyclic-index `MontConfig::into_bigint` loop boundary.
#[derive(Clone, Copy)]
pub struct ConversionRound {
    pub limbs: [u64; 6],
    pub factor: u64,
    pub discarded: u64,
    pub carry: u64,
}

/// ark-ff's conversion loop, with N=6 and the inner loop explicitly unrolled.
/// `index` is in 0..6; limb positions retain upstream's cyclic layout.
pub fn conversion_round(mut r: [u64; 6], index: usize) -> ConversionRound {
    let k = r[index].wrapping_mul(INV);
    let (discarded, carry) = mac(r[index], k, MODULUS[0], 0);
    let j = (index + 1) % 6;
    let (word, carry) = mac(r[j], k, MODULUS[1], carry);
    r[j] = word;
    let j = (index + 2) % 6;
    let (word, carry) = mac(r[j], k, MODULUS[2], carry);
    r[j] = word;
    let j = (index + 3) % 6;
    let (word, carry) = mac(r[j], k, MODULUS[3], carry);
    r[j] = word;
    let j = (index + 4) % 6;
    let (word, carry) = mac(r[j], k, MODULUS[4], carry);
    r[j] = word;
    let j = (index + 5) % 6;
    let (word, carry) = mac(r[j], k, MODULUS[5], carry);
    r[j] = word;
    r[index] = carry;
    ConversionRound {
        limbs: r,
        factor: k,
        discarded,
        carry,
    }
}

/// ark-ff `MontConfig::into_bigint`, retaining all six cyclic reduction steps.
pub fn into_canonical(a: [u64; 6]) -> [u64; 6] {
    let r0 = conversion_round(a, 0);
    let r1 = conversion_round(r0.limbs, 1);
    let r2 = conversion_round(r1.limbs, 2);
    let r3 = conversion_round(r2.limbs, 3);
    let r4 = conversion_round(r3.limbs, 4);
    conversion_round(r4.limbs, 5).limbs
}

pub fn trace_into_canonical(a: [u64; 6]) -> [ConversionRound; 6] {
    let r0 = conversion_round(a, 0);
    let r1 = conversion_round(r0.limbs, 1);
    let r2 = conversion_round(r1.limbs, 2);
    let r3 = conversion_round(r2.limbs, 3);
    let r4 = conversion_round(r3.limbs, 4);
    let r5 = conversion_round(r4.limbs, 5);
    [r0, r1, r2, r3, r4, r5]
}

/// ark-ff `MontConfig::from_bigint`: zero shortcut, canonical check, then R² product.
pub fn from_canonical(a: [u64; 6]) -> Option<[u64; 6]> {
    if a[0] == 0 && a[1] == 0 && a[2] == 0 && a[3] == 0 && a[4] == 0 && a[5] == 0 {
        Some(a)
    } else if !less(a, MODULUS) {
        None
    } else {
        Some(multiply(a, R2))
    }
}

/// ark-ff-macros 0.5.0 portable `square_in_place_impl`, with N=6.
/// Phases retain the macro's arithmetic order; the field square is wired after its proof.
pub fn square_cross(a: [u64; 6]) -> [u64; 12] {
    let mut r = [0; 12];
    let carry = 0;
    let (word, carry) = mac(r[1], a[0], a[1], carry);
    r[1] = word;
    let (word, carry) = mac(r[2], a[0], a[2], carry);
    r[2] = word;
    let (word, carry) = mac(r[3], a[0], a[3], carry);
    r[3] = word;
    let (word, carry) = mac(r[4], a[0], a[4], carry);
    r[4] = word;
    let (word, carry) = mac(r[5], a[0], a[5], carry);
    r[5] = word;
    r[6] = carry;
    let carry = 0;
    let (word, carry) = mac(r[3], a[1], a[2], carry);
    r[3] = word;
    let (word, carry) = mac(r[4], a[1], a[3], carry);
    r[4] = word;
    let (word, carry) = mac(r[5], a[1], a[4], carry);
    r[5] = word;
    let (word, carry) = mac(r[6], a[1], a[5], carry);
    r[6] = word;
    r[7] = carry;
    let carry = 0;
    let (word, carry) = mac(r[5], a[2], a[3], carry);
    r[5] = word;
    let (word, carry) = mac(r[6], a[2], a[4], carry);
    r[6] = word;
    let (word, carry) = mac(r[7], a[2], a[5], carry);
    r[7] = word;
    r[8] = carry;
    let carry = 0;
    let (word, carry) = mac(r[7], a[3], a[4], carry);
    r[7] = word;
    let (word, carry) = mac(r[8], a[3], a[5], carry);
    r[8] = word;
    r[9] = carry;
    let carry = 0;
    let (word, carry) = mac(r[9], a[4], a[5], carry);
    r[9] = word;
    r[10] = carry;
    r
}

pub fn square_double(mut r: [u64; 12]) -> [u64; 12] {
    r[11] = r[10] >> 63;
    r[10] = (r[10] << 1) | (r[9] >> 63);
    r[9] = (r[9] << 1) | (r[8] >> 63);
    r[8] = (r[8] << 1) | (r[7] >> 63);
    r[7] = (r[7] << 1) | (r[6] >> 63);
    r[6] = (r[6] << 1) | (r[5] >> 63);
    r[5] = (r[5] << 1) | (r[4] >> 63);
    r[4] = (r[4] << 1) | (r[3] >> 63);
    r[3] = (r[3] << 1) | (r[2] >> 63);
    r[2] = (r[2] << 1) | (r[1] >> 63);
    r[1] <<= 1;
    r
}

#[derive(Clone, Copy)]
pub struct SquareDiagonal {
    pub limbs: [u64; 12],
    pub carry: u64,
}

pub fn square_diagonal(a: [u64; 6], mut r: [u64; 12]) -> SquareDiagonal {
    let carry = 0;
    let (word, carry) = mac(r[0], a[0], a[0], carry);
    r[0] = word;
    let (word, carry) = crate::field::adc(r[1], 0, carry);
    r[1] = word;
    let (word, carry) = mac(r[2], a[1], a[1], carry);
    r[2] = word;
    let (word, carry) = crate::field::adc(r[3], 0, carry);
    r[3] = word;
    let (word, carry) = mac(r[4], a[2], a[2], carry);
    r[4] = word;
    let (word, carry) = crate::field::adc(r[5], 0, carry);
    r[5] = word;
    let (word, carry) = mac(r[6], a[3], a[3], carry);
    r[6] = word;
    let (word, carry) = crate::field::adc(r[7], 0, carry);
    r[7] = word;
    let (word, carry) = mac(r[8], a[4], a[4], carry);
    r[8] = word;
    let (word, carry) = crate::field::adc(r[9], 0, carry);
    r[9] = word;
    let (word, carry) = mac(r[10], a[5], a[5], carry);
    r[10] = word;
    let (word, carry) = crate::field::adc(r[11], 0, carry);
    r[11] = word;
    SquareDiagonal { limbs: r, carry }
}

#[derive(Clone, Copy)]
pub struct SquareReductionRound {
    pub limbs: [u64; 12],
    pub factor: u64,
    pub discarded: u64,
    pub carry: u64,
    pub mac_carry: u64,
}

pub fn square_reduction_round(mut r: [u64; 12], index: usize, carry2: u64) -> SquareReductionRound {
    let k = r[index].wrapping_mul(INV);
    let (discarded, carry) = mac(r[index], k, MODULUS[0], 0);
    let j = index + 1;
    let (word, carry) = mac(r[j], k, MODULUS[1], carry);
    r[j] = word;
    let j = index + 2;
    let (word, carry) = mac(r[j], k, MODULUS[2], carry);
    r[j] = word;
    let j = index + 3;
    let (word, carry) = mac(r[j], k, MODULUS[3], carry);
    r[j] = word;
    let j = index + 4;
    let (word, carry) = mac(r[j], k, MODULUS[4], carry);
    r[j] = word;
    let j = index + 5;
    let (word, carry) = mac(r[j], k, MODULUS[5], carry);
    r[j] = word;
    let j = index + 6;
    let mac_carry = carry;
    let (word, carry) = crate::field::adc(r[j], carry, carry2);
    r[j] = word;
    SquareReductionRound {
        limbs: r,
        factor: k,
        discarded,
        carry,
        mac_carry,
    }
}

pub fn square(a: [u64; 6]) -> [u64; 6] {
    let r = square_diagonal(a, square_double(square_cross(a))).limbs;
    let r0 = square_reduction_round(r, 0, 0);
    let r1 = square_reduction_round(r0.limbs, 1, r0.carry);
    let r2 = square_reduction_round(r1.limbs, 2, r1.carry);
    let r3 = square_reduction_round(r2.limbs, 3, r2.carry);
    let r4 = square_reduction_round(r3.limbs, 4, r3.carry);
    let r5 = square_reduction_round(r4.limbs, 5, r4.carry);
    reduce([
        r5.limbs[6],
        r5.limbs[7],
        r5.limbs[8],
        r5.limbs[9],
        r5.limbs[10],
        r5.limbs[11],
    ])
}

/// One pair accumulation from ark-ff's specialized M=2 sum-of-products path.
#[derive(Clone, Copy)]
pub struct ProductAccumulation {
    pub limbs: [u64; 6],
    pub carry_a: u64,
    pub carry_b: u64,
}

pub fn accumulate_product(
    a: [u64; 6],
    digit: u64,
    r: [u64; 6],
    carry_a: u64,
    carry_b: u64,
) -> ProductAccumulation {
    let (o0, carry) = mac(r[0], digit, a[0], 0);
    let (o1, carry) = mac(r[1], digit, a[1], carry);
    let (o2, carry) = mac(r[2], digit, a[2], carry);
    let (o3, carry) = mac(r[3], digit, a[3], carry);
    let (o4, carry) = mac(r[4], digit, a[4], carry);
    let (o5, carry) = mac(r[5], digit, a[5], carry);
    let (carry_a, carry_b) = crate::field::adc(carry_a, carry_b, carry);
    ProductAccumulation {
        limbs: [o0, o1, o2, o3, o4, o5],
        carry_a,
        carry_b,
    }
}

#[derive(Clone, Copy)]
pub struct SumProductRound {
    pub first: ProductAccumulation,
    pub second: ProductAccumulation,
    pub limbs: [u64; 6],
    pub factor: u64,
    pub discarded: u64,
    pub reduction_carry: u64,
    pub overflow: u64,
}

/// ark-ff-macros' M<=5 sum-of-products path, specialized to two pairs.
pub fn sum_product_round(
    b: [u64; 6],
    a_digit: u64,
    d: [u64; 6],
    c_digit: u64,
    r: [u64; 6],
) -> SumProductRound {
    let first = accumulate_product(b, a_digit, r, 0, 0);
    let second = accumulate_product(d, c_digit, first.limbs, first.carry_a, first.carry_b);
    let k = second.limbs[0].wrapping_mul(INV);
    let (discarded, carry) = mac(second.limbs[0], k, MODULUS[0], 0);
    let (o0, carry) = mac(second.limbs[1], k, MODULUS[1], carry);
    let (o1, carry) = mac(second.limbs[2], k, MODULUS[2], carry);
    let (o2, carry) = mac(second.limbs[3], k, MODULUS[3], carry);
    let (o3, carry) = mac(second.limbs[4], k, MODULUS[4], carry);
    let (o4, carry) = mac(second.limbs[5], k, MODULUS[5], carry);
    let (o5, overflow) = crate::field::adc(second.carry_a, second.carry_b, carry);
    SumProductRound {
        first,
        second,
        limbs: [o0, o1, o2, o3, o4, o5],
        factor: k,
        discarded,
        reduction_carry: carry,
        overflow,
    }
}

/// Source-specialized fused a*b+c*d. Field integration follows the arithmetic proof.
pub fn sum_products(a: [u64; 6], b: [u64; 6], c: [u64; 6], d: [u64; 6]) -> [u64; 6] {
    let r0 = sum_product_round(b, a[0], d, c[0], [0; 6]);
    let r1 = sum_product_round(b, a[1], d, c[1], r0.limbs);
    let r2 = sum_product_round(b, a[2], d, c[2], r1.limbs);
    let r3 = sum_product_round(b, a[3], d, c[3], r2.limbs);
    let r4 = sum_product_round(b, a[4], d, c[4], r3.limbs);
    let r5 = sum_product_round(b, a[5], d, c[5], r4.limbs);
    reduce(r5.limbs)
}

pub fn trace_sum_products(
    a: [u64; 6],
    b: [u64; 6],
    c: [u64; 6],
    d: [u64; 6],
) -> [SumProductRound; 6] {
    let r0 = sum_product_round(b, a[0], d, c[0], [0; 6]);
    let r1 = sum_product_round(b, a[1], d, c[1], r0.limbs);
    let r2 = sum_product_round(b, a[2], d, c[2], r1.limbs);
    let r3 = sum_product_round(b, a[3], d, c[3], r2.limbs);
    let r4 = sum_product_round(b, a[4], d, c[4], r3.limbs);
    let r5 = sum_product_round(b, a[5], d, c[5], r4.limbs);
    [r0, r1, r2, r3, r4, r5]
}

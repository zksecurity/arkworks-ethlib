//! Bounded integer backend for the source GLV scalar decomposition.
//! This replaces num-bigint storage; it does not use field arithmetic.
use crate::field::{add_raw, halve, less, subtract};
use crate::montgomery::mac;

pub const ORDER: [u64; 6] = [
    0xffffffff00000001,
    0x53bda402fffe5bfe,
    0x3339d80809a1d805,
    0x73eda753299d7d48,
    0,
    0,
];

/// Unsigned division. Requires 0 < d and both inputs less than 2^383.
/// Recursive halving supplies the numerator bits from most to least significant.
pub fn div_rem(n: [u64; 6], d: [u64; 6]) -> ([u64; 6], [u64; 6]) {
    if !less([0; 6], n) {
        return ([0; 6], [0; 6]);
    }
    let (q, r) = div_rem(halve(n), d);
    let r = add_raw(r, r);
    let r = add_raw(r, [n[0] & 1, 0, 0, 0, 0, 0]);
    let q = add_raw(q, q);
    if !less(r, d) {
        (add_raw(q, [1, 0, 0, 0, 0, 0]), subtract(r, d))
    } else {
        (q, r)
    }
}

/// The positive-numerator quotient block of the pinned scalar decomposition.
/// Requires n < 2^383; ties retain the quotient, as in the source strict test.
pub fn rounded_quotient(n: [u64; 6]) -> [u64; 6] {
    let (q, rem) = div_rem(n, ORDER);
    let twice_rem = add_raw(rem, rem);
    if less(ORDER, twice_rem) {
        add_raw(q, [1, 0, 0, 0, 0, 0])
    } else {
        q
    }
}

/// Exact 256-by-128-bit product in six little-endian words.
pub fn multiply_128(n: [u64; 4], m: [u64; 2]) -> [u64; 6] {
    let (o0, c0) = mac(0, n[0], m[0], 0);
    let (o1, c1) = mac(0, n[1], m[0], c0);
    let (o2, c2) = mac(0, n[2], m[0], c1);
    let (o3, c3) = mac(0, n[3], m[0], c2);
    let (o1, c0) = mac(o1, n[0], m[1], 0);
    let (o2, c1) = mac(o2, n[1], m[1], c0);
    let (o3, c2) = mac(o3, n[2], m[1], c1);
    let (o4, o5) = mac(c3, n[3], m[1], c2);
    [o0, o1, o2, o3, o4, o5]
}

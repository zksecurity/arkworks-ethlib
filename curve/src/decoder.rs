//! Strict BLS12-381 compressed G1 decoding over the extracted field backend.
use crate::{
    field::{in_subgroup, Fp},
    Field, Point,
};

fn word(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8) -> u64 {
    ((((((a as u64 * 256 + b as u64) * 256 + c as u64) * 256 + d as u64) * 256 + e as u64) * 256
        + f as u64)
        * 256
        + g as u64)
        * 256
        + h as u64
}

/// Parse a canonical 48-byte big-endian field element without reducing modulo p.
pub fn field_from_bytes(bytes: [u8; 48]) -> Option<Fp> {
    Fp::from_limbs([
        word(
            bytes[40], bytes[41], bytes[42], bytes[43], bytes[44], bytes[45], bytes[46], bytes[47],
        ),
        word(
            bytes[32], bytes[33], bytes[34], bytes[35], bytes[36], bytes[37], bytes[38], bytes[39],
        ),
        word(
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
        ),
        word(
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
        ),
        word(
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ),
        word(
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ),
    ])
}

fn tail_zero(bytes: [u8; 48], index: usize) -> bool {
    if index == 48 {
        return true;
    }
    if bytes[index] != 0 {
        return false;
    }
    tail_zero(bytes, index + 1)
}

/// ark-bls12-381 0.5.0 `curves::util::EncodingFlags`.
#[derive(Clone, Copy)]
pub struct EncodingFlags {
    pub is_compressed: bool,
    pub is_infinity: bool,
    pub is_lexographically_largest: bool,
}

impl EncodingFlags {
    /// Fixed-array specialization of upstream `get_flags`; errors become `None`.
    pub fn get_flags(bytes: [u8; 48]) -> Option<Self> {
        let compression_flag_set = (bytes[0] >> 7) & 1;
        let infinity_flag_set = (bytes[0] >> 6) & 1;
        let sort_flag_set = (bytes[0] >> 5) & 1;
        let is_compressed = compression_flag_set == 1;
        let is_infinity = infinity_flag_set == 1;
        let is_lexographically_largest = sort_flag_set == 1;
        if is_lexographically_largest && (!is_compressed || is_infinity) {
            return None;
        }
        Some(Self {
            is_compressed,
            is_infinity,
            is_lexographically_largest,
        })
    }

    pub fn remove_flags(mut bytes: [u8; 48]) -> [u8; 48] {
        bytes[0] &= 0b0001_1111;
        bytes
    }
}

/// ark-bls12-381 `read_g1_compressed`, specialized to an already framed array.
/// Array-zero comparison is lowered to the extracted recursive `tail_zero`.
fn uncompress48(bytes: [u8; 48]) -> Option<Point<Fp>> {
    let flags = match EncodingFlags::get_flags(bytes) {
        None => return None,
        Some(flags) => flags,
    };
    if !flags.is_compressed {
        return None;
    }
    let x_bytes = EncodingFlags::remove_flags(bytes);
    if flags.is_infinity {
        if !tail_zero(x_bytes, 0) {
            return None;
        }
        return Some(crate::identity());
    }
    match field_from_bytes(x_bytes) {
        None => None,
        Some(x) => point_from_x_unchecked(x, flags.is_lexographically_largest),
    }
}

/// ark-ec 0.5.0 `Affine::get_ys_from_x_unchecked`, specialized to A=0 and B=4.
pub fn ys_from_x_unchecked(x: Fp) -> Option<(Fp, Fp)> {
    let rhs = x.square().times(x).plus(crate::field::G1_COEFF_B);
    match rhs.sqrt() {
        None => None,
        Some(y) => {
            let negative = y.negative();
            if crate::field::less(y.to_limbs(), negative.to_limbs()) {
                Some((y, negative))
            } else {
                Some((negative, y))
            }
        }
    }
}

/// ark-ec `Affine::get_point_from_x_unchecked`; affine points use projective z=1 here.
pub fn point_from_x_unchecked(x: Fp, greatest: bool) -> Option<Point<Fp>> {
    match ys_from_x_unchecked(x) {
        None => None,
        Some((smaller, larger)) => Some(Point {
            x,
            y: if greatest { larger } else { smaller },
            z: Fp::constant(1),
        }),
    }
}

fn copy48(bytes: &[u8]) -> [u8; 48] {
    [
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7], bytes[8],
        bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15], bytes[16],
        bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23], bytes[24],
        bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31], bytes[32],
        bytes[33], bytes[34], bytes[35], bytes[36], bytes[37], bytes[38], bytes[39], bytes[40],
        bytes[41], bytes[42], bytes[43], bytes[44], bytes[45], bytes[46], bytes[47],
    ]
}

/// Strict framing, flag validation, canonical coordinate parsing and curve reconstruction.
/// This allows infinity and does not check subgroup membership.
pub fn uncompress_g1(bytes: &[u8]) -> Option<Point<Fp>> {
    if bytes.len() != 48 {
        return None;
    }
    uncompress48(copy48(bytes))
}

/// Strict compressed group decoding with subgroup validation; infinity is allowed.
pub fn decode_g1(bytes: &[u8]) -> Option<Point<Fp>> {
    match uncompress_g1(bytes) {
        None => None,
        Some(p) => {
            if in_subgroup(p) {
                Some(p)
            } else {
                None
            }
        }
    }
}

/// Decode a public key, rejecting infinity and points outside the prime-order subgroup.
pub fn decode_public_key(bytes: &[u8]) -> Option<Point<Fp>> {
    match decode_g1(bytes) {
        None => None,
        Some(p) => {
            if p.z.is_zero() {
                None
            } else {
                Some(p)
            }
        }
    }
}

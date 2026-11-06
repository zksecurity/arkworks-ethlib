#![no_std]

//! BLS12-381 G1 compressed-byte formatting, with an explicit affine boundary.
//! For a finite point, `x_be` must be its canonical 48-byte big-endian x and
//! `y_is_largest` must mean y > -y in canonical field order.
//! This function does not validate coordinates, compute signs, or decode points.

/// Fixed-array specialization of ark-bls12-381's EncodingFlags::encode_flags.
pub fn encode_flags(mut bytes: [u8; 48], compressed: bool, infinity: bool, largest: bool) -> [u8; 48] {
    if compressed {
        bytes[0] |= 0x80;
    }
    if infinity {
        bytes[0] |= 0x40;
    }
    if compressed && !infinity && largest {
        bytes[0] |= 0x20;
    }
    bytes
}

pub fn compress_g1(mut x_be: [u8; 48], y_is_largest: bool, infinity: bool) -> [u8; 48] {
    if infinity {
        x_be = [0u8; 48];
    }
    encode_flags(x_be, true, infinity, y_is_largest)
}

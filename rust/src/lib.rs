//! Extraction root: call the real arkworks serializer, without replacing arithmetic.
#![no_std]

use ark_bls12_381::G1Affine;
use ark_serialize::{CanonicalSerialize, SerializationError};

/// Compressed BLS12-381 G1 serialization, including the identity encoding.
/// The eventual refinement theorem requires a valid affine point.
pub fn encode_g1(point: &G1Affine) -> Result<[u8; 48], SerializationError> {
    let mut bytes = [0u8; 48];
    point.serialize_compressed(&mut bytes[..])?;
    Ok(bytes)
}

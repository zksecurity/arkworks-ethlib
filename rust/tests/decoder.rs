#[allow(dead_code)]
#[path = "../src/curve_support.rs"]
mod support;

use ark_bls12_381::{Fq, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_eth_bridge::encode_g1;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalDeserialize;
use curve_g1::{decoder, field, Field};

fn check(bytes: &[u8]) {
    let ark = if bytes.len() == 48 {
        G1Affine::deserialize_compressed(bytes).ok()
    } else {
        None
    };
    let minimal = decoder::decode_g1(bytes).map(|p| support::export_point(p).into_affine());
    assert_eq!(minimal, ark);
    let ark_curve = if bytes.len() == 48 {
        G1Affine::deserialize_compressed_unchecked(bytes).ok()
    } else {
        None
    };
    let raw = decoder::uncompress_g1(bytes).map(|p| support::export_point(p).into_affine());
    assert_eq!(raw, ark_curve);
    let public = decoder::decode_public_key(bytes).map(|p| support::export_point(p).into_affine());
    assert_eq!(public, ark.filter(|p| !p.is_zero()));
}

#[test]
fn strict_decoder_boundaries_and_flags() {
    for n in [0u64, 1, 2, 17, u64::MAX] {
        let p = G1Affine::generator().mul_bigint([n]).into_affine();
        let bytes = encode_g1(&p).unwrap();
        check(&bytes);
        assert!(decoder::decode_g1(&bytes).is_some());
    }
    for n in [0, 1, 47, 49, 96] {
        check(&vec![0; n]);
    }
    let generator_bytes = encode_g1(&G1Affine::generator()).unwrap();
    for flag in 0u16..=255 {
        let mut bytes = [0u8; 48];
        bytes[0] = flag as u8;
        check(&bytes);
        bytes.copy_from_slice(&generator_bytes);
        bytes[0] = flag as u8;
        check(&bytes);
    }
    let mut infinity = [0u8; 48];
    infinity[0] = 0xc0;
    assert!(decoder::decode_g1(&infinity).is_some());
    assert!(decoder::decode_public_key(&infinity).is_none());
    infinity[47] = 1;
    check(&infinity);
    assert!(decoder::decode_g1(&infinity).is_none());
    for sign in [false, true] {
        let torsion = field::from_x(field::Fp::constant(0), sign).unwrap();
        let bytes = field::compress(torsion);
        assert!(decoder::uncompress_g1(&bytes).is_some());
        assert!(decoder::decode_g1(&bytes).is_none());
        check(&bytes);
    }
}

#[test]
fn canonical_big_endian_field_decoding() {
    for n in [0, 1, 255, 256, u64::MAX] {
        let fq = Fq::from(n);
        let bytes: [u8; 48] = fq.into_bigint().to_bytes_be().try_into().unwrap();
        let got = decoder::field_from_bytes(bytes).unwrap();
        assert_eq!(support::export_field(got), fq);
    }
    let modulus: [u8; 48] = Fq::MODULUS.to_bytes_be().try_into().unwrap();
    assert!(decoder::field_from_bytes(modulus).is_none());
    assert!(decoder::field_from_bytes([0xff; 48]).is_none());
}

#[test]
fn reader_prefix_and_strict_slice_framing_are_explicit() {
    for point in [G1Affine::generator(), G1Affine::identity()] {
        let bytes = encode_g1(&point).unwrap();
        for suffix in [vec![], vec![0u8], vec![1u8, 2, 3], vec![0xabu8; 48]] {
            let mut input = bytes.to_vec();
            input.extend_from_slice(&suffix);
            let mut reader = input.as_slice();
            let decoded = G1Affine::deserialize_compressed(&mut reader).unwrap();
            assert_eq!(decoded, point);
            assert_eq!(reader, suffix.as_slice());
            let strict = decoder::decode_g1(&input).map(|p| support::export_point(p).into_affine());
            assert_eq!(strict, if suffix.is_empty() { Some(point) } else { None });
            let raw = decoder::uncompress_g1(&input).map(|p| support::export_point(p).into_affine());
            assert_eq!(raw, if suffix.is_empty() { Some(point) } else { None });
        }
    }
}

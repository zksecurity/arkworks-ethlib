//! The adapter is outside the extracted crate: Montgomery conversion and sign
//! computation remain arkworks operations, not part of the proved formatter.
use ark_bls12_381::{Fq, Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_eth_bridge::encode_g1;
use ark_ff::{BigInteger, PrimeField};
use minimal_g1::compress_g1;

fn check(p: G1Affine) {
    let x = p.x.into_bigint().to_bytes_be().try_into().unwrap();
    let actual = compress_g1(x, p.y > -p.y, p.is_zero());
    assert_eq!(actual, encode_g1(&p).unwrap());
}

#[test]
fn subgroup_points_and_negations() {
    check(G1Affine::identity());
    check(G1Affine::generator());
    check(-G1Affine::generator());
    // Full-width scalar samples, in addition to the shared u64 differential corpus.
    let mut state = 0xaeea5_u64;
    for _ in 0..256 {
        let mut bytes = [0u8; 32];
        for chunk in bytes.chunks_exact_mut(8) {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            chunk.copy_from_slice(&state.to_le_bytes());
        }
        let scalar = Fr::from_le_bytes_mod_order(&bytes);
        let p = G1Affine::generator()
            .mul_bigint(scalar.into_bigint())
            .into_affine();
        check(p);
        check(-p);
    }
}

#[test]
fn canonical_coordinate_boundaries() {
    let mut half = Fq::MODULUS;
    half.div2();
    let half = Fq::from_bigint(half).unwrap();
    let coordinates = [
        Fq::from(0),
        Fq::from(1),
        half,
        half + Fq::from(1),
        -Fq::from(1),
    ];
    for x in coordinates {
        for y in coordinates {
            // Deliberately NOT a curve-validity test. Both formatters accept
            // affine coordinates without validating the curve equation.
            check(G1Affine::new_unchecked(x, y));
        }
    }
}

#[test]
fn infinity_ignores_payload_and_sign() {
    let mut expected = [0u8; 48];
    expected[0] = 0xc0;
    for fill in 0..=255 {
        for sign in [false, true] {
            assert_eq!(compress_g1([fill; 48], sign, true), expected);
        }
    }
}

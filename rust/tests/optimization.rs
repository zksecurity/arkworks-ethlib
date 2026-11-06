//! The optional optimization has the same full input contract as the original power.
use ark_bls12_381::Fq;
use ark_ff::{BigInt, Field, PrimeField};
use curve_g1::field::Fp;

fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

#[test]
fn optimized_power_matches_original_and_arkworks() {
    let mut bases = vec![Fq::from(0u64), Fq::from(1u64), -Fq::from(1u64), Fq::from(7u64)];
    let mut seed = 0x0f71_381u64;
    while bases.len() < 20 {
        let mut limbs = core::array::from_fn(|_| next(&mut seed));
        limbs[5] &= (1u64 << 61) - 1;
        if let Some(a) = Fq::from_bigint(BigInt(limbs)) {
            bases.push(a);
        }
    }
    let mut exponents = vec![[0; 6], [1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
        [17, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1 << 63], [u64::MAX; 6]];
    for _ in 0..16 {
        exponents.push(core::array::from_fn(|_| next(&mut seed)));
    }
    for a in bases {
        let native = Fp::from_limbs(a.into_bigint().0).unwrap();
        for e in &exponents {
            let original = curve_g1::field::pow(native, *e);
            let optimized = curve_g1::optimized::field_power::pow(native, *e);
            let alternative = curve_g1::alternative::field_power::pow(native, *e);
            assert_eq!(alternative.to_montgomery_limbs(), original.to_montgomery_limbs());
            assert_eq!(optimized.to_montgomery_limbs(), original.to_montgomery_limbs());
            assert_eq!(optimized.to_montgomery_limbs(), a.pow(e).0 .0);
        }
    }
}

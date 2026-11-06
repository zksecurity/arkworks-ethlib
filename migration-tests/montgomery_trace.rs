//! Compiled only by scripts/compare_arkworks_intermediates.py with trace-instrumented arkworks.
use ark_bls12_381::{Fq, Fq12, Fq2, Fq6, Fq6Config, FqConfig};
use ark_ff::{
    AdditiveGroup, BigInt, CyclotomicMultSubgroup, Field, Fp6Config, MontConfig, PrimeField, Zero,
};
use curve_g1::{
    field::Fp,
    montgomery,
    pairing::{Fp12, Fp2, Fp6},
    Field as MinimalField,
};

fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn compare_inverse_execution() -> usize {
    let upstream = ark_ff::migration_trace::take_inverse();
    let minimal = curve_g1::migration_trace::take_inverse();
    assert_eq!(minimal.len(), upstream.len());
    for (minimal, upstream) in minimal.iter().zip(&upstream) {
        assert_eq!(minimal.phase, upstream.phase);
        assert_eq!(minimal.words, upstream.words);
    }
    upstream.len()
}

fn compare_fused(
    a: [u64; 6],
    b: [u64; 6],
    c: [u64; 6],
    d: [u64; 6],
    expected: &[ark_ff::migration_trace::Snapshot],
) {
    assert_eq!(expected.len(), 18);
    for (actual, expected) in montgomery::trace_sum_products(a, b, c, d)
        .iter()
        .zip(expected.chunks_exact(3))
    {
        for (actual, expected) in [
            (&actual.first, &expected[0]),
            (&actual.second, &expected[1]),
        ] {
            assert_eq!(actual.limbs.as_slice(), expected.limbs.as_slice());
            assert_eq!(actual.carry_a, expected.product_carry);
            assert_eq!(actual.carry_b, expected.reduction_carry);
        }
        assert_eq!(actual.limbs.as_slice(), expected[2].limbs.as_slice());
        assert_eq!(actual.factor, expected[2].factor);
        assert_eq!(actual.second.carry_a, expected[2].product_carry);
        assert_eq!(actual.reduction_carry, expected[2].reduction_carry);
        assert_eq!(actual.discarded, 0);
        assert_eq!(actual.overflow, 0);
    }
}

fn compare_product(a: [u64; 6], b: [u64; 6], expected: &[ark_ff::migration_trace::Snapshot]) {
    assert_eq!(expected.len(), 6);
    for (actual, expected) in montgomery::trace(a, b).iter().zip(expected) {
        assert_eq!(actual.limbs.as_slice(), expected.limbs.as_slice());
        assert_eq!(actual.factor, expected.factor);
        assert_eq!(actual.product_carry, expected.product_carry);
        assert_eq!(actual.reduction_carry, expected.reduction_carry);
        assert_eq!(actual.discarded, 0);
    }
}

fn compare_square(a: [u64; 6], expected: &[ark_ff::migration_trace::Snapshot]) {
    assert_eq!(expected.len(), 9);
    let cross = montgomery::square_cross(a);
    let doubled = montgomery::square_double(cross);
    let diagonal = montgomery::square_diagonal(a, doubled);
    for (actual, expected) in [cross, doubled, diagonal.limbs].iter().zip(expected) {
        assert_eq!(actual.as_slice(), expected.limbs.as_slice());
    }
    assert_eq!(diagonal.carry, expected[2].reduction_carry);
    assert_eq!(diagonal.carry, 0);
    let mut wide = diagonal.limbs;
    let mut carry = 0;
    for (index, expected) in expected[3..].iter().enumerate() {
        let actual = montgomery::square_reduction_round(wide, index, carry);
        assert_eq!(actual.limbs.as_slice(), expected.limbs.as_slice());
        assert_eq!(actual.factor, expected.factor);
        assert_eq!(actual.mac_carry, expected.product_carry);
        assert_eq!(actual.carry, expected.reduction_carry);
        assert_eq!(actual.discarded, 0);
        wide = actual.limbs;
        carry = actual.carry;
    }
    assert_eq!(carry, 0);
}

fn import_fp2(a: Fq2) -> Fp2 {
    Fp2 {
        c0: Fp::from_limbs(a.c0.into_bigint().0).unwrap(),
        c1: Fp::from_limbs(a.c1.into_bigint().0).unwrap(),
    }
}
fn compare_fp2(actual: Fp2, expected: Fq2) {
    assert_eq!(actual.c0.to_montgomery_limbs(), expected.c0.0 .0);
    assert_eq!(actual.c1.to_montgomery_limbs(), expected.c1.0 .0);
}

fn import_fp6(a: Fq6) -> Fp6 {
    Fp6 {
        c0: import_fp2(a.c0),
        c1: import_fp2(a.c1),
        c2: import_fp2(a.c2),
    }
}
fn compare_fp6(actual: Fp6, expected: Fq6) {
    compare_fp2(actual.c0, expected.c0);
    compare_fp2(actual.c1, expected.c1);
    compare_fp2(actual.c2, expected.c2);
}
fn compare_execution(
    minimal: &[curve_g1::migration_trace::Snapshot],
    upstream: &[ark_ff::migration_trace::Snapshot],
) {
    assert_eq!(
        minimal.len(),
        upstream.len(),
        "actual operation schedules differ"
    );
    for (index, (minimal, upstream)) in minimal.iter().zip(upstream).enumerate() {
        assert_eq!(minimal.limbs, upstream.limbs, "execution boundary {index}");
        assert_eq!(
            minimal.factor, upstream.factor,
            "execution boundary {index}, factor"
        );
        assert_eq!(
            minimal.product_carry, upstream.product_carry,
            "execution boundary {index}, product carry"
        );
        assert_eq!(
            minimal.reduction_carry, upstream.reduction_carry,
            "execution boundary {index}, reduction carry"
        );
    }
}

fn compare_fp2_execution(
    op: impl FnOnce() -> Fp2,
    expected: Fq2,
    upstream: &[ark_ff::migration_trace::Snapshot],
) {
    curve_g1::migration_trace::take();
    let actual = op();
    let minimal = curve_g1::migration_trace::take();
    compare_execution(&minimal, upstream);
    compare_fp2(actual, expected);
}

fn import_fp12(a: Fq12) -> Fp12 {
    Fp12 {
        c0: import_fp6(a.c0),
        c1: import_fp6(a.c1),
    }
}
fn compare_fp12(actual: Fp12, expected: Fq12) {
    compare_fp6(actual.c0, expected.c0);
    compare_fp6(actual.c1, expected.c1);
}

#[test]
fn actual_arkworks_montgomery_rounds() {
    assert_eq!(<FqConfig as MontConfig<6>>::INV, montgomery::INV);
    assert_eq!(<FqConfig as MontConfig<6>>::R.0, montgomery::R);
    assert_eq!(<FqConfig as MontConfig<6>>::R2.0, montgomery::R2);
    assert!(<FqConfig as MontConfig<6>>::CAN_USE_NO_CARRY_MUL_OPT);
    let mut cases = Vec::new();
    let raw = [
        [0; 6],
        [1, 0, 0, 0, 0, 0],
        montgomery::R,
        montgomery::R2,
        [
            0xb9feffffffffaaaa,
            0x1eabfffeb153ffff,
            0x6730d2a0f6b0f624,
            0x64774b84f38512bf,
            0x4b1ba7b6434bacd7,
            0x1a0111ea397fe69a,
        ],
    ];
    for a in raw {
        for b in raw {
            cases.push((a, b));
        }
    }
    let mut rng = 0x7a99_a11c_00bb_1142;
    for _ in 0..512 {
        let mut a = [0u8; 64];
        let mut b = [0u8; 64];
        for chunk in a.chunks_exact_mut(8) {
            chunk.copy_from_slice(&next(&mut rng).to_le_bytes());
        }
        for chunk in b.chunks_exact_mut(8) {
            chunk.copy_from_slice(&next(&mut rng).to_le_bytes());
        }
        cases.push((
            Fq::from_le_bytes_mod_order(&a).0 .0,
            Fq::from_le_bytes_mod_order(&b).0 .0,
        ));
    }
    // Exercise stored coordinates directly: the upstream map also runs on infinity
    // and off-curve representations, without normalizing either representation.
    let mut endomorphism_boundaries = 0;
    for (i, (a, b)) in cases.iter().copied().enumerate() {
        use ark_ec::scalar_mul::glv::GLVConfig;
        let (c, _) = cases[(i * 17 + 13) % cases.len()];
        let x = Fq::new_unchecked(BigInt(a));
        let y = Fq::new_unchecked(BigInt(b));
        let z = Fq::new_unchecked(BigInt(c));
        let minimal = curve_g1::Point {
            x: Fp::from_limbs(x.into_bigint().0).unwrap(),
            y: Fp::from_limbs(y.into_bigint().0).unwrap(),
            z: Fp::from_limbs(z.into_bigint().0).unwrap(),
        };
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let expected =
            <ark_bls12_381::g1::Config as GLVConfig>::endomorphism(&ark_bls12_381::G1Projective {
                x,
                y,
                z,
            });
        let upstream = ark_ff::migration_trace::take();
        let actual = curve_g1::glv::endomorphism(minimal);
        let trace = curve_g1::migration_trace::take();
        compare_execution(&trace, &upstream);
        endomorphism_boundaries += upstream.len();
        assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
        assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
        assert_eq!(actual.z.to_montgomery_limbs(), expected.z.0 .0);
        for infinity in [false, true] {
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = <ark_bls12_381::g1::Config as GLVConfig>::endomorphism_affine(
                &ark_bls12_381::G1Affine { x, y, infinity },
            );
            let upstream = ark_ff::migration_trace::take();
            let actual = curve_g1::glv::endomorphism_affine(curve_g1::AffinePoint {
                x: minimal.x,
                y: minimal.y,
                infinity,
            });
            let trace = curve_g1::migration_trace::take();
            compare_execution(&trace, &upstream);
            endomorphism_boundaries += upstream.len();
            assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
            assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
            assert_eq!(actual.infinity, expected.infinity);
        }
    }
    println!(
        "Compared {} G1 endomorphisms at {endomorphism_boundaries} actual execution boundaries.",
        cases.len() * 3
    );

    let mut fused_cases = Vec::new();
    for a in raw {
        for b in raw {
            for c in raw {
                for d in raw {
                    fused_cases.push((a, b, c, d));
                }
            }
        }
    }
    for (i, (a, b)) in cases.iter().copied().enumerate() {
        let (c, d) = cases[(i * 17 + 13) % cases.len()];
        fused_cases.push((a, b, c, d));
    }
    let fused_count = fused_cases.len();
    for (case, (a, b, c, d)) in fused_cases.into_iter().enumerate() {
        let fq = |x| Fq::new_unchecked(BigInt(x));
        ark_ff::migration_trace::take();
        let expected = Fq::sum_of_products(&[fq(a), fq(c)], &[fq(b), fq(d)]);
        let upstream = ark_ff::migration_trace::take();
        assert_eq!(upstream.len(), 18, "missing fused M=2 path, case {case}");
        compare_fused(a, b, c, d, &upstream);
        assert_eq!(montgomery::sum_products(a, b, c, d), expected.0 .0);
        assert_eq!(expected, fq(a) * fq(b) + fq(c) * fq(d));
    }
    println!(
        "Compared {fused_count} fused products and {} accumulation/reduction boundaries.",
        fused_count * 18
    );
    let mut tower_inverse_states = 0;
    let mut fp2_boundaries = 0;
    let mut fp2_inverse_cases = 0;
    let mut fp2_frobenius_cases = 0;
    let mut fp2_frobenius_boundaries = 0;
    for (i, (a, b)) in cases.iter().copied().enumerate() {
        let (c, d) = cases[(i * 17 + 13) % cases.len()];
        let fq = |x| Fq::new_unchecked(BigInt(x));
        let left = Fq2::new(fq(a), fq(b));
        let right = Fq2::new(fq(c), fq(d));
        let x = import_fp2(left);
        let y = import_fp2(right);
        ark_ff::migration_trace::take();
        let expected = left * right;
        let observed = ark_ff::migration_trace::take();
        assert_eq!(observed.len(), 36, "Fp2 fused multiplication path changed");
        compare_fused(
            a,
            c,
            x.c1.negative().to_montgomery_limbs(),
            d,
            &observed[..18],
        );
        compare_fused(a, d, b, c, &observed[18..]);
        compare_fp2_execution(|| x.times(y), expected, &observed);
        fp2_boundaries += observed.len();
        let expected = left.square();
        let observed = ark_ff::migration_trace::take();
        assert_eq!(observed.len(), 12, "Fp2 dedicated square path changed");
        compare_product(
            x.c0.plus(x.c1).to_montgomery_limbs(),
            x.c0.minus(x.c1).to_montgomery_limbs(),
            &observed[..6],
        );
        compare_product(x.c1.plus(x.c1).to_montgomery_limbs(), a, &observed[6..]);
        compare_fp2_execution(|| x.square(), expected, &observed);
        fp2_boundaries += observed.len();
        ark_ff::migration_trace::start_inverse();
        let expected = left.inverse();
        let observed = ark_ff::migration_trace::take();
        if let Some(expected) = expected {
            assert_eq!(observed.len(), 30, "Fp2 inverse norm/product path changed");
            compare_square(b, &observed[..9]);
            compare_square(a, &observed[9..18]);
            let norm = x.c1.square().plus(x.c0.square());
            let inv = norm.inverse().to_montgomery_limbs();
            compare_product(a, inv, &observed[18..24]);
            compare_product(b, inv, &observed[24..]);
            curve_g1::migration_trace::start_inverse();
            compare_fp2_execution(|| x.inverse(), expected, &observed);
        } else {
            assert!(observed.is_empty());
            curve_g1::migration_trace::start_inverse();
            compare_fp2_execution(|| x.inverse(), Fq2::ZERO, &observed);
        }
        tower_inverse_states += compare_inverse_execution();
        fp2_inverse_cases += 1;
        fp2_boundaries += observed.len();
        let mut expected_xi = left;
        <Fq6Config as Fp6Config>::mul_fp2_by_nonresidue_in_place(&mut expected_xi);
        compare_fp2(x.mul_xi(), expected_xi);
        ark_ff::migration_trace::take();
        for power in [0, 1, 2, 3, 4, 5, 6, 7, 11, 12, usize::MAX - 1, usize::MAX] {
            let expected = left.frobenius_map(power);
            let observed = ark_ff::migration_trace::take();
            assert_eq!(
                observed.len(),
                6,
                "Fp2 Frobenius coefficient product path changed"
            );
            compare_fp2_execution(|| x.frobenius(power), expected, &observed);
            fp2_frobenius_cases += 1;
            fp2_frobenius_boundaries += observed.len();
        }
    }
    println!("Compared {} Fp2 products/squares and {fp2_inverse_cases} inverses at {fp2_boundaries} base-field boundaries.", cases.len());
    println!("Compared {fp2_frobenius_cases} Fp2 Frobenius powers at {fp2_frobenius_boundaries} actual execution boundaries.");
    let mut fp6_boundaries = 0;
    let mut fp6_frobenius_cases = 0;
    let mut fp6_frobenius_boundaries = 0;
    for (i, (a, b)) in cases.iter().copied().enumerate() {
        let (c, d) = cases[(i * 17 + 13) % cases.len()];
        let (e, f) = cases[(i * 31 + 7) % cases.len()];
        let fq = |x| Fq::new_unchecked(BigInt(x));
        let left = if i == 0 {
            Fq6::ZERO
        } else {
            Fq6::new(
                Fq2::new(fq(a), fq(b)),
                Fq2::new(fq(c), fq(d)),
                Fq2::new(fq(e), fq(f)),
            )
        };
        let right = Fq6::new(
            Fq2::new(fq(c), fq(a)),
            Fq2::new(fq(e), fq(b)),
            Fq2::new(fq(f), fq(d)),
        );
        let x = import_fp6(left);
        let y = import_fp6(right);
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let expected = left * right;
        let upstream = ark_ff::migration_trace::take();
        let actual = x.times(y);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), 216);
        compare_execution(&minimal, &upstream);
        compare_fp6(actual, expected);
        fp6_boundaries += upstream.len();
        let expected = left.square();
        let upstream = ark_ff::migration_trace::take();
        let actual = x.square();
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), 108);
        compare_execution(&minimal, &upstream);
        compare_fp6(actual, expected);
        fp6_boundaries += upstream.len();
        ark_ff::migration_trace::start_inverse();
        curve_g1::migration_trace::start_inverse();
        let expected = left.inverse().unwrap_or_default();
        let upstream = ark_ff::migration_trace::take();
        let actual = x.inverse();
        tower_inverse_states += compare_inverse_execution();
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), if i == 0 { 0 } else { 390 });
        compare_execution(&minimal, &upstream);
        compare_fp6(actual, expected);
        fp6_boundaries += upstream.len();
        for power in [0, 1, 2, 3, 4, 5, 6, 7, 11, 12, usize::MAX - 1, usize::MAX] {
            let expected = left.frobenius_map(power);
            let upstream = ark_ff::migration_trace::take();
            let actual = x.frobenius(power);
            let minimal = curve_g1::migration_trace::take();
            assert_eq!(upstream.len(), 90, "Fp6 Frobenius coefficient path changed");
            compare_execution(&minimal, &upstream);
            compare_fp6(actual, expected);
            fp6_frobenius_cases += 1;
            fp6_frobenius_boundaries += upstream.len();
        }
    }
    println!("Compared {} Fp6 products/squares/inverses at {fp6_boundaries} actual execution boundaries (binary inverse states checked separately).",cases.len());
    println!("Compared {fp6_frobenius_cases} Fp6 Frobenius powers at {fp6_frobenius_boundaries} actual execution boundaries.");
    let mut fp12_boundaries = 0;
    assert_eq!(
        ark_ff::biginteger::arithmetic::find_naf(&[curve_g1::pairing::BLS_X]),
        curve_g1::pairing::BLS_X_NAF
    );
    let mut optimized_finals = 0;
    let mut optimized_final_boundaries = 0;
    let mut cyclotomic_exponents = 0;
    let mut cyclotomic_exponent_boundaries = 0;
    let mut cyclotomic_squares = 0;
    let mut cyclotomic_boundaries = 0;
    let mut fp12_frobenius_cases = 0;
    let mut fp12_frobenius_boundaries = 0;
    for (i, (a, b)) in cases.iter().copied().enumerate() {
        let (c, d) = cases[(i * 17 + 13) % cases.len()];
        let (e, f) = cases[(i * 31 + 7) % cases.len()];
        let fq = |x| Fq::new_unchecked(BigInt(x));
        let u = Fq6::new(
            Fq2::new(fq(a), fq(b)),
            Fq2::new(fq(c), fq(d)),
            Fq2::new(fq(e), fq(f)),
        );
        let v = Fq6::new(
            Fq2::new(fq(c), fq(a)),
            Fq2::new(fq(e), fq(b)),
            Fq2::new(fq(f), fq(d)),
        );
        let left = match i {
            0 => Fq12::ZERO,
            1 => Fq12::ONE,
            2 => Fq12::new(Fq6::ZERO, Fq6::ONE),
            3 => -Fq12::ONE,
            4 => Fq12::new(Fq6::ONE, Fq6::ONE),
            _ => Fq12::new(u, v),
        };
        let right = Fq12::new(v, u);
        let x = import_fp12(left);
        let y = import_fp12(right);
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let expected = left * right;
        let upstream = ark_ff::migration_trace::take();
        let actual = x.times(y);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), 648);
        compare_execution(&minimal, &upstream);
        compare_fp12(actual, expected);
        fp12_boundaries += upstream.len();
        let expected = left.square();
        let upstream = ark_ff::migration_trace::take();
        let actual = x.square();
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), 432);
        compare_execution(&minimal, &upstream);
        compare_fp12(actual, expected);
        fp12_boundaries += upstream.len();
        for member in [false, true] {
            use ark_bls12_381::Bls12_381;
            use ark_ec::pairing::{MillerLoopOutput, Pairing};
            let input = if member {
                // Domain preparation is outside the square trace being compared.
                ark_ff::migration_trace::without_recording(|| {
                    Bls12_381::final_exponentiation(MillerLoopOutput(left))
                        .map(|r| r.0)
                        .unwrap_or_default()
                })
            } else {
                left
            };
            let minimal_input = import_fp12(input);
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = input.cyclotomic_square();
            let upstream = ark_ff::migration_trace::take();
            let actual = minimal_input.cyclotomic_square();
            let minimal = curve_g1::migration_trace::take();
            assert_eq!(upstream.len(), 216, "Granger-Scott source schedule changed");
            compare_execution(&minimal, &upstream);
            compare_fp12(actual, expected);
            if member {
                assert_eq!(expected, input.square());
            }
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            cyclotomic_squares += 1;
            cyclotomic_boundaries += upstream.len();
            // Compare actual source exponentiation, including the initial ONE*base product.
            let expected = input.cyclotomic_exp([curve_g1::pairing::BLS_X]);
            let upstream = ark_ff::migration_trace::take();
            let actual = minimal_input.cyclotomic_exp_x_abs();
            let minimal = curve_g1::migration_trace::take();
            assert_eq!(upstream.len(), if input.is_zero() { 0 } else { 17712 });
            compare_execution(&minimal, &upstream);
            compare_fp12(actual, expected);
            let mut signed = expected;
            signed.cyclotomic_inverse_in_place();
            let actual_signed = minimal_input.exp_by_x();
            compare_fp12(actual_signed, signed);
            if member && !input.is_zero() {
                assert_eq!(
                    signed,
                    input.pow([curve_g1::pairing::BLS_X]).inverse().unwrap()
                );
            }
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            cyclotomic_exponents += 1;
            cyclotomic_exponent_boundaries += upstream.len();
            if !member {
                let expected = Bls12_381::final_exponentiation(MillerLoopOutput(input))
                    .map(|r| r.0)
                    .unwrap_or_default();
                let upstream = ark_ff::migration_trace::take();
                let actual = curve_g1::pairing::final_exponentiation(minimal_input);
                let minimal = curve_g1::migration_trace::take();
                compare_execution(&minimal, &upstream);
                compare_fp12(actual, expected);
                optimized_finals += 1;
                optimized_final_boundaries += upstream.len();
            }
        }
        ark_ff::migration_trace::start_inverse();
        curve_g1::migration_trace::start_inverse();
        let expected = left.inverse().unwrap_or_default();
        let upstream = ark_ff::migration_trace::take();
        let actual = x.inverse();
        tower_inverse_states += compare_inverse_execution();
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), if i == 0 { 0 } else { 1038 });
        compare_execution(&minimal, &upstream);
        compare_fp12(actual, expected);
        fp12_boundaries += upstream.len();
        assert_eq!(x.is_zero(), left.is_zero());
        for power in [
            0,
            1,
            2,
            3,
            4,
            5,
            6,
            7,
            8,
            9,
            10,
            11,
            12,
            usize::MAX - 1,
            usize::MAX,
        ] {
            let expected = left.frobenius_map(power);
            let upstream = ark_ff::migration_trace::take();
            let actual = x.frobenius(power);
            let minimal = curve_g1::migration_trace::take();
            assert_eq!(
                upstream.len(),
                288,
                "Fp12 Frobenius coefficient path changed"
            );
            compare_execution(&minimal, &upstream);
            compare_fp12(actual, expected);
            fp12_frobenius_cases += 1;
            fp12_frobenius_boundaries += upstream.len();
        }
    }
    println!("Compared {} Fp12 products/squares/inverses at {fp12_boundaries} actual execution boundaries (binary inverse states checked separately).",cases.len());
    println!(
        "Compared {tower_inverse_states} binary inverse states inside Fp2/Fp6/Fp12 inversion."
    );
    println!("Compared {fp12_frobenius_cases} Fp12 Frobenius powers at {fp12_frobenius_boundaries} actual execution boundaries.");
    println!("Compared {cyclotomic_squares} cyclotomic squares at {cyclotomic_boundaries} actual execution boundaries (half arbitrary, half zero or subgroup inputs).");
    println!("Compared {cyclotomic_exponents} signed-NAF parameter exponents at {cyclotomic_exponent_boundaries} actual execution boundaries.");
    println!("Compared {optimized_finals} optimized final exponents at {optimized_final_boundaries} actual execution boundaries.");
    let mut projective_prepared_boundaries = 0;
    let mut prepared_g2_boundaries = 0;
    let mut prepared_boundaries = 0;
    let two_inv = Fq::from(2u64).inverse().unwrap();
    let native_half = Fp::from_limbs(two_inv.into_bigint().0).unwrap();
    for (i, (a, b)) in cases.iter().copied().enumerate() {
        use ark_ec::bls12::{g2::G2HomProjective, Bls12};
        use curve_g1::pairing::prepared::{self, HomG2, LineCoeff};
        let (c, d) = cases[(i * 17 + 13) % cases.len()];
        let (e, f) = cases[(i * 31 + 7) % cases.len()];
        let fq = |v| Fq::new_unchecked(BigInt(v));
        let x = Fq2::new(fq(a), fq(b));
        let y = Fq2::new(fq(c), fq(d));
        let z = Fq2::new(fq(e), fq(f));
        let native = HomG2 {
            x: import_fp2(x),
            y: import_fp2(y),
            z: import_fp2(z),
        };
        let compare_coeff = |actual: LineCoeff, expected: (Fq2, Fq2, Fq2)| {
            compare_fp2(actual.c0, expected.0);
            compare_fp2(actual.c1, expected.1);
            compare_fp2(actual.c2, expected.2);
        };
        let native_px = Fp::from_limbs(fq(a).into_bigint().0).unwrap();
        let native_py = Fp::from_limbs(fq(c).into_bigint().0).unwrap();
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let mut upstream = G2HomProjective::<ark_bls12_381::Config> { x, y, z };
        let coeff = upstream.double_in_place(&two_inv);
        let observed = ark_ff::migration_trace::take();
        let (actual, actual_coeff) = native.double(native_half);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(observed.len(), 240);
        compare_execution(&minimal, &observed);
        compare_fp2(actual.x, upstream.x);
        compare_fp2(actual.y, upstream.y);
        compare_fp2(actual.z, upstream.z);
        compare_coeff(actual_coeff, coeff);
        let doubled_coeff = actual_coeff;
        prepared_boundaries += observed.len();

        let mut upstream = G2HomProjective::<ark_bls12_381::Config> { x, y, z };
        let addend = ark_bls12_381::G2Affine::new_unchecked(y, z);
        let expected = upstream.add_in_place(&addend);
        let observed = ark_ff::migration_trace::take();
        let (actual, actual_coeff) = native.add(native.y, native.z);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(observed.len(), 420);
        compare_execution(&minimal, &observed);
        compare_fp2(actual.x, upstream.x);
        compare_fp2(actual.y, upstream.y);
        compare_fp2(actual.z, upstream.z);
        compare_coeff(actual_coeff, expected);
        prepared_boundaries += observed.len();

        let value = Fq12::new(Fq6::new(x, y, z), Fq6::new(z, x, y));
        let native_value = import_fp12(value);
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let point = ark_bls12_381::G1Affine::new_unchecked(fq(a), fq(c));
        let mut expected = value;
        Bls12::<ark_bls12_381::Config>::ell(&mut expected, &coeff, &point);
        let observed = ark_ff::migration_trace::take();
        let actual = prepared::ell(native_value, doubled_coeff, native_px, native_py);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(observed.len(), 492);
        compare_execution(&minimal, &observed);
        compare_fp12(actual, expected);
        prepared_boundaries += observed.len();

        let mut expected = x;
        expected.mul_assign_by_fp(&fq(c));
        let observed = ark_ff::migration_trace::take();
        let actual = native.x.mul_by_fp(native_py);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(observed.len(), 12);
        compare_execution(&minimal, &observed);
        compare_fp2(actual, expected);
        prepared_boundaries += observed.len();

        let infinity = i == 0;
        let q = ark_bls12_381::G2Affine { x, y, infinity };
        let expected = ark_ec::bls12::G2Prepared::<ark_bls12_381::Config>::from(q);
        let observed = ark_ff::migration_trace::take();
        let actual = prepared::prepare_affine(native.x, native.y, infinity);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(observed.len(), if infinity { 0 } else { 17220 });
        compare_execution(&minimal, &observed);
        assert_eq!(actual.infinity, expected.infinity);
        assert_eq!(actual.ell_coeffs.len(), expected.ell_coeffs.len());
        for (a, b) in actual.ell_coeffs.into_iter().zip(expected.ell_coeffs) {
            compare_coeff(a, b);
        }
        prepared_g2_boundaries += observed.len();
        let z1 = if i == 0 {
            Fq::ZERO
        } else if i == 1 {
            Fq::ONE
        } else {
            fq(e)
        };
        let z2 = if i == 0 {
            Fq2::ZERO
        } else if i == 1 {
            Fq2::ONE
        } else {
            z
        };
        let native_z1 = Fp::from_limbs(z1.into_bigint().0).unwrap();
        let native_z2 = import_fp2(z2);
        let native_p = curve_g1::Point {
            x: native_px,
            y: native_py,
            z: native_z1,
        };
        let native_q = curve_g1::pairing::G2 {
            x: native.x,
            y: native.y,
            z: native_z2,
        };
        let p = ark_bls12_381::G1Projective::new_unchecked(fq(a), fq(c), z1);
        let q = ark_bls12_381::G2Projective::new_unchecked(x, y, z2);
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let expected = ark_ec::bls12::G1Prepared::<ark_bls12_381::Config>::from(p);
        let observed = ark_ff::migration_trace::take();
        let actual = prepared::prepare_g1(native_p);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(
            observed.len(),
            if z1.is_zero() || z1 == Fq::ONE { 0 } else { 27 }
        );
        compare_execution(&minimal, &observed);
        assert_eq!(actual.x.to_montgomery_limbs(), expected.0.x.0 .0);
        assert_eq!(actual.y.to_montgomery_limbs(), expected.0.y.0 .0);
        assert_eq!(actual.infinity, expected.0.infinity);
        projective_prepared_boundaries += observed.len();

        use ark_ec::CurveGroup;
        let expected = q.into_affine();
        let observed = ark_ff::migration_trace::take();
        let actual = prepared::normalize_g2(native_q);
        let minimal = curve_g1::migration_trace::take();
        let normalization_rounds = if z2.is_zero() || z2 == Fq2::ONE {
            0
        } else {
            150
        };
        assert_eq!(observed.len(), normalization_rounds);
        compare_execution(&minimal, &observed);
        compare_fp2(actual.x, expected.x);
        compare_fp2(actual.y, expected.y);
        assert_eq!(actual.infinity, expected.infinity);
        projective_prepared_boundaries += observed.len();

        let expected = ark_ec::bls12::G2Prepared::<ark_bls12_381::Config>::from(q);
        let observed = ark_ff::migration_trace::take();
        let actual = prepared::prepare_g2(native_q);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(
            observed.len(),
            normalization_rounds + if z2.is_zero() { 0 } else { 17220 }
        );
        compare_execution(&minimal, &observed);
        assert_eq!(actual.infinity, expected.infinity);
        assert_eq!(actual.ell_coeffs.len(), expected.ell_coeffs.len());
        for (a, b) in actual.ell_coeffs.into_iter().zip(expected.ell_coeffs) {
            compare_coeff(a, b);
        }
        projective_prepared_boundaries += observed.len();
    }
    println!(
        "Compared {} G2 preparations at {prepared_g2_boundaries} actual execution boundaries.",
        cases.len()
    );
    println!("Compared {} homogeneous doubles/adds/lines and scalar products at {prepared_boundaries} actual execution boundaries.",cases.len());
    println!("Compared {} projective preparation cases at {projective_prepared_boundaries} actual execution boundaries.",cases.len());
    let mut sparse_boundaries = 0;
    for (i, (a, b)) in cases.iter().copied().enumerate() {
        let (c, d) = cases[(i * 17 + 13) % cases.len()];
        let (e, f) = cases[(i * 31 + 7) % cases.len()];
        let fq = |x| Fq::new_unchecked(BigInt(x));
        let left = Fq6::new(
            Fq2::new(fq(a), fq(b)),
            Fq2::new(fq(c), fq(d)),
            Fq2::new(fq(e), fq(f)),
        );
        let c0 = Fq2::new(fq(c), fq(a));
        let c1 = Fq2::new(fq(e), fq(b));
        let c4 = Fq2::new(fq(f), fq(d));
        let x = import_fp6(left);
        let n0 = import_fp2(c0);
        let n1 = import_fp2(c1);
        let n4 = import_fp2(c4);
        let dense = left * Fq6::new(Fq2::ZERO, c1, Fq2::ZERO);
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let mut expected = left;
        expected.mul_by_1(&c1);
        let upstream = ark_ff::migration_trace::take();
        let actual = x.mul_by_1(n1);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), 108);
        compare_execution(&minimal, &upstream);
        compare_fp6(actual, expected);
        assert_eq!(expected, dense);
        sparse_boundaries += upstream.len();
        let dense = left * Fq6::new(c0, c1, Fq2::ZERO);
        ark_ff::migration_trace::take();
        let mut expected = left;
        expected.mul_by_01(&c0, &c1);
        let upstream = ark_ff::migration_trace::take();
        let actual = x.mul_by_01(n0, n1);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), 180);
        compare_execution(&minimal, &upstream);
        compare_fp6(actual, expected);
        assert_eq!(expected, dense);
        sparse_boundaries += upstream.len();
        let left = Fq12::new(left, Fq6::new(c4, c1, c0));
        let x = import_fp12(left);
        let dense = left
            * Fq12::new(
                Fq6::new(c0, c1, Fq2::ZERO),
                Fq6::new(Fq2::ZERO, c4, Fq2::ZERO),
            );
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let mut expected = left;
        expected.mul_by_014(&c0, &c1, &c4);
        let upstream = ark_ff::migration_trace::take();
        let actual = x.mul_by_014(n0, n1, n4);
        let minimal = curve_g1::migration_trace::take();
        assert_eq!(upstream.len(), 468);
        compare_execution(&minimal, &upstream);
        compare_fp12(actual, expected);
        assert_eq!(expected, dense);
        sparse_boundaries += upstream.len();
    }
    println!("Compared {} cases for each sparse helper at {sparse_boundaries} actual execution boundaries.",cases.len());
    let mut inverse_states = 0;
    for (a, _) in cases.iter().copied() {
        let input = Fq::new_unchecked(BigInt(a));
        let x = Fp::from_limbs(input.into_bigint().0).unwrap();
        ark_ff::migration_trace::start_inverse();
        let expected = input.inverse().map(|r| r.0 .0);
        let upstream = ark_ff::migration_trace::take_inverse();
        curve_g1::migration_trace::start_inverse();
        let actual = curve_g1::field::inversion::inverse(x).map(|r| r.to_montgomery_limbs());
        let minimal = curve_g1::migration_trace::take_inverse();
        assert_eq!(actual, expected);
        assert_eq!(minimal.len(), upstream.len());
        for (minimal, upstream) in minimal.iter().zip(&upstream) {
            assert_eq!(minimal.phase, upstream.phase);
            assert_eq!(minimal.words, upstream.words);
        }
        if a == [0; 6] {
            assert!(upstream.is_empty());
        } else {
            assert!(!upstream.is_empty());
            assert_eq!(upstream[0].phase, 0);
            assert_eq!(upstream.last().unwrap().phase, 4);
            assert_eq!(actual, Some(x.inverse().to_montgomery_limbs()));
            let fermat = curve_g1::field::pow(
                x,
                [
                    0xb9feffffffffaaa9,
                    0x1eabfffeb153ffff,
                    0x6730d2a0f6b0f624,
                    0x64774b84f38512bf,
                    0x4b1ba7b6434bacd7,
                    0x1a0111ea397fe69a,
                ],
            );
            assert_eq!(actual, Some(fermat.to_montgomery_limbs()));
        }
        inverse_states += upstream.len();
    }
    println!(
        "Compared {} binary inverses and {inverse_states} actual u/v/b/c state boundaries.",
        cases.len()
    );
    let count = cases.len();
    let mut conversion_rounds = 0;
    let mut constructor_rounds = 0;
    for (case, (a, b)) in cases.into_iter().enumerate() {
        ark_ff::migration_trace::take();
        let expected_square = Fq::new_unchecked(BigInt(a)).square();
        let upstream_square = ark_ff::migration_trace::take();
        assert_eq!(
            upstream_square.len(),
            9,
            "missing actual square path for case {case}"
        );
        compare_square(a, &upstream_square);
        assert_eq!(montgomery::square(a), expected_square.0 .0);
        assert_eq!(montgomery::multiply(a, a), expected_square.0 .0);
        let expected = Fq::new_unchecked(BigInt(a)) * Fq::new_unchecked(BigInt(b));
        let upstream = ark_ff::migration_trace::take();
        assert_eq!(
            upstream.len(),
            6,
            "upstream macro trace missing for case {case}"
        );
        compare_product(a, b, &upstream);
        assert_eq!(
            montgomery::multiply(a, b),
            expected.0 .0,
            "case {case}, final raw Montgomery limbs"
        );
        assert_eq!(
            montgomery::reduce(montgomery::trace(a, b)[5].limbs),
            expected.0 .0
        );
        ark_ff::migration_trace::take();
        let canonical = Fq::new_unchecked(BigInt(a)).into_bigint().0;
        let conversion = ark_ff::migration_trace::take();
        assert_eq!(
            conversion.len(),
            6,
            "conversion trace missing for case {case}"
        );
        conversion_rounds += conversion.len();
        let minimal_conversion = montgomery::trace_into_canonical(a);
        for (round, (actual, expected)) in
            minimal_conversion.iter().zip(conversion.iter()).enumerate()
        {
            assert_eq!(
                actual.limbs.as_slice(),
                expected.limbs.as_slice(),
                "conversion case {case}, round {round}, cyclic limbs"
            );
            assert_eq!(
                actual.factor, expected.factor,
                "conversion case {case}, round {round}, factor"
            );
            assert_eq!(
                actual.carry, expected.reduction_carry,
                "conversion case {case}, round {round}, carry"
            );
            assert_eq!(actual.discarded, 0);
        }
        assert_eq!(montgomery::into_canonical(a), canonical);
        let from = Fq::from_bigint(BigInt(a)).map(|x| x.0 .0);
        let constructor = ark_ff::migration_trace::take();
        assert_eq!(montgomery::from_canonical(a), from);
        if a == [0; 6] {
            assert!(constructor.is_empty(), "upstream zero shortcut changed");
        } else {
            assert_eq!(constructor.len(), 6);
            constructor_rounds += constructor.len();
            let minimal_from = montgomery::trace(a, montgomery::R2);
            for (actual, expected) in minimal_from.iter().zip(constructor.iter()) {
                assert_eq!(actual.limbs.as_slice(), expected.limbs.as_slice());
                assert_eq!(actual.factor, expected.factor);
                assert_eq!(actual.product_carry, expected.product_carry);
                assert_eq!(actual.reduction_carry, expected.reduction_carry);
            }
        }
    }
    println!(
        "Compared {count} products and {} actual arkworks macro-generated round boundaries.",
        count * 6
    );
    println!(
        "Compared {count} squares, {} square phase boundaries and {} square reduction rounds.",
        count * 3,
        count * 6
    );
    for invalid in [Fq::MODULUS.0, [u64::MAX; 6]] {
        assert!(montgomery::from_canonical(invalid).is_none());
        assert!(Fq::from_bigint(BigInt(invalid)).is_none());
    }
    println!("Compared {count} conversion calls and {conversion_rounds} actual conversion round boundaries; {count} constructors and {constructor_rounds} constructor round boundaries.");
}

#[test]
fn actual_prepared_miller_schedule() {
    use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
    use ark_ec::{pairing::Pairing, PrimeGroup};
    let mut calls = 0;
    let mut boundaries = 0;
    for size in [0, 1, 2, 3, 4, 5, 7, 8, 9, 12] {
        for mode in 0..3 {
            let (ps, qs) = ark_ff::migration_trace::without_recording(|| {
                let mut ps = Vec::new();
                let mut qs = Vec::new();
                for i in 0..size {
                    let mut p = G1Projective::generator() * Fr::from((i + 1) as u64);
                    let mut q = G2Projective::generator() * Fr::from((i + 2) as u64);
                    if mode == 2 || (mode == 1 && i % 3 == 0) {
                        p = G1Projective::zero();
                    }
                    if mode == 1 && i % 3 == 1 {
                        q = G2Projective::zero();
                    }
                    ps.push(p);
                    qs.push(q);
                }
                (ps, qs)
            });
            let fp = |x: Fq| Fp::from_limbs(x.into_bigint().0).unwrap();
            let native: Vec<_> = ps
                .iter()
                .zip(&qs)
                .map(|(p, q)| {
                    (
                        curve_g1::Point {
                            x: fp(p.x),
                            y: fp(p.y),
                            z: fp(p.z),
                        },
                        curve_g1::pairing::G2 {
                            x: import_fp2(q.x),
                            y: import_fp2(q.y),
                            z: import_fp2(q.z),
                        },
                    )
                })
                .collect();
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = Bls12_381::multi_miller_loop(ps, qs).0;
            let upstream = ark_ff::migration_trace::take();
            let actual = curve_g1::pairing::prepared_miller::multi_miller_loop(&native);
            let minimal = curve_g1::migration_trace::take();
            assert_eq!(minimal.len(), upstream.len(), "size={size}, mode={mode}");
            compare_execution(&minimal, &upstream);
            compare_fp12(actual, expected);
            calls += 1;
            boundaries += upstream.len();
        }
    }
    println!(
        "Compared {calls} prepared multi-Miller loops at {boundaries} actual execution boundaries."
    );
}

#[test]
fn actual_glv_projective_schedule() {
    use ark_ec::{short_weierstrass::SWCurveConfig, AffineRepr, CurveGroup};
    let generator = ark_bls12_381::G1Affine::generator().into_group();
    let scale = Fq::from(7u64);
    let points = [
        generator,
        ark_bls12_381::G1Projective {
            x: generator.x * scale * scale,
            y: generator.y * scale * scale * scale,
            z: generator.z * scale,
        },
        ark_bls12_381::G1Projective::default(),
        ark_bls12_381::G1Projective {
            x: Fq::from(13u64),
            y: Fq::from(7u64),
            z: Fq::from(0u64),
        },
        ark_bls12_381::G1Projective {
            x: Fq::from(3u64),
            y: Fq::from(7u64),
            z: Fq::from(2u64),
        },
        ark_bls12_381::G1Projective {
            x: Fq::from(0u64),
            y: Fq::from(2u64),
            z: Fq::from(1u64),
        },
    ];
    let order = ark_bls12_381::Fr::MODULUS.0;
    let mut above = order;
    above[0] += 1;
    let mut scalars = vec![[0; 4], [1, 0, 0, 0], order, above, [u64::MAX; 4]];
    let mut state = 0x381_61_05u64;
    for _ in 0..8 {
        scalars.push([
            next(&mut state),
            next(&mut state),
            next(&mut state),
            next(&mut state),
        ]);
    }
    let cases = points.len() * scalars.len();
    let mut boundaries = 0;
    let mut excluded_fr = 0;
    for scalar in scalars {
        for point in points {
            let native = curve_g1::Point {
                x: Fp::from_limbs(point.x.into_bigint().0).unwrap(),
                y: Fp::from_limbs(point.y.into_bigint().0).unwrap(),
                z: Fp::from_limbs(point.z.into_bigint().0).unwrap(),
            };
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected =
                <ark_bls12_381::g1::Config as SWCurveConfig>::mul_projective(&point, &scalar);
            let upstream: Vec<_> = ark_ff::migration_trace::take()
                .into_iter()
                .filter(|event| match event.limbs.len() {
                    6 | 12 => true,
                    4 | 8 => {
                        excluded_fr += 1;
                        false
                    }
                    n => panic!("Unexpected field trace width {n}"),
                })
                .collect();
            let actual = curve_g1::field::mul_256_concrete(native, scalar);
            let minimal = curve_g1::migration_trace::take();
            compare_execution(&minimal, &upstream);
            boundaries += upstream.len();
            assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
            assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
            assert_eq!(actual.z.to_montgomery_limbs(), expected.z.0 .0);
        }
    }
    println!("Compared {cases} GLV projective cases at {boundaries} actual Fq execution boundaries; {excluded_fr} Fr boundaries excluded.");
}

#[test]
fn actual_affine_integer_schedule() {
    use ark_ec::AffineRepr;
    let points = [ark_bls12_381::G1Affine::generator(), ark_bls12_381::G1Affine::default(),
        ark_bls12_381::G1Affine { x: Fq::from(13u64), y: Fq::from(7u64), infinity: true },
        ark_bls12_381::G1Affine::new_unchecked(Fq::from(4u64), Fq::from(7u64)),
        ark_bls12_381::G1Affine::new_unchecked(Fq::from(0u64), Fq::from(2u64)),
        ark_bls12_381::G1Affine::new_unchecked(Fq::from(0u64), -Fq::from(2u64))];
    let mut scalars = vec![[0; 4], [1, 0, 0, 0], [0xd201000000010000, 0, 0, 0],
        [0xd201000000010001, 0, 0, 0], ark_bls12_381::Fr::MODULUS.0, [u64::MAX; 4]];
    let mut state = 0xaff1_381_2026u64;
    for _ in 0..7 {
        scalars.push([next(&mut state), next(&mut state), next(&mut state), next(&mut state)]);
    }
    let cases = points.len()*scalars.len();
    let mut boundaries = 0;
    for scalar in scalars {
        for p in points {
            let native = curve_g1::AffinePoint {
                x: Fp::from_limbs(p.x.into_bigint().0).unwrap(),
                y: Fp::from_limbs(p.y.into_bigint().0).unwrap(), infinity: p.infinity,
            };
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = p.mul_bigint(scalar);
            let upstream = ark_ff::migration_trace::take();
            let actual = curve_g1::scalar::mul_affine(native, scalar);
            let minimal = curve_g1::migration_trace::take();
            compare_execution(&minimal, &upstream);
            boundaries += upstream.len();
            assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
            assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
            assert_eq!(actual.z.to_montgomery_limbs(), expected.z.0 .0);
        }
    }
    println!("Compared {cases} affine integer cases at {boundaries} actual Fq execution boundaries.");
}

#[test]
fn actual_source_cofactor_schedule() {
    use ark_ec::{AffineRepr, CurveGroup};
    let generator = ark_bls12_381::G1Affine::generator().into_group();
    let scale = Fq::from(7u64);
    let mut points = vec![generator,
        ark_bls12_381::G1Projective { x: generator.x*scale*scale,
            y: generator.y*scale*scale*scale, z: scale },
        ark_bls12_381::G1Projective::default(),
        ark_bls12_381::G1Projective { x: Fq::from(13u64), y: Fq::from(7u64), z: Fq::from(0u64) },
        ark_bls12_381::G1Projective { x: Fq::from(3u64), y: Fq::from(7u64), z: Fq::from(2u64) },
        ark_bls12_381::G1Affine::new_unchecked(Fq::from(0u64), Fq::from(2u64)).into_group()];
    let mut state = 0xc0fa_c703_381u64;
    while points.len() < 14 {
        if let Some(p) = ark_bls12_381::G1Affine::get_point_from_x_unchecked(Fq::from(next(&mut state)), false) {
            points.push(p.into_group());
        }
    }
    let cases = points.len();
    let mut boundaries = 0;
    let mut excluded_fr = 0;
    let mut inverse_states = 0;
    for p in points {
        let native = curve_g1::Point { x: Fp::from_limbs(p.x.into_bigint().0).unwrap(),
            y: Fp::from_limbs(p.y.into_bigint().0).unwrap(), z: Fp::from_limbs(p.z.into_bigint().0).unwrap() };
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        ark_ff::migration_trace::start_inverse();
        curve_g1::migration_trace::start_inverse();
        let expected = p.into_affine().clear_cofactor().into_group();
        let upstream: Vec<_> = ark_ff::migration_trace::take().into_iter().filter(|event| match event.limbs.len() {
            6 | 12 => true,
            4 | 8 => { excluded_fr += 1; false },
            n => panic!("Unexpected field trace width {n}"),
        }).collect();
        let actual = curve_g1::field::clear_cofactor(native);
        let minimal = curve_g1::migration_trace::take();
        compare_execution(&minimal, &upstream);
        inverse_states += compare_inverse_execution();
        boundaries += upstream.len();
        assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
        assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
        assert_eq!(actual.z.to_montgomery_limbs(), expected.z.0 .0);
    }
    assert!(inverse_states > 0, "cofactor normalization must exercise inverse state comparisons");
    println!("Compared {cases} source cofactor cases at {boundaries} actual Fq execution boundaries and {inverse_states} inverse states; {excluded_fr} Fr boundaries excluded.");
}

#[test]
fn actual_source_fast_subgroup_schedule() {
    use ark_ec::{AffineRepr, CurveGroup};
    let generator = ark_bls12_381::G1Affine::generator().into_group();
    let scale = Fq::from(7u64);
    let mut points = vec![generator,
        ark_bls12_381::G1Projective { x: generator.x*scale*scale,
            y: generator.y*scale*scale*scale, z: scale },
        ark_bls12_381::G1Projective::default(),
        ark_bls12_381::G1Projective { x: Fq::from(13u64), y: Fq::from(7u64), z: Fq::from(0u64) },
        ark_bls12_381::G1Projective { x: Fq::from(3u64), y: Fq::from(7u64), z: Fq::from(2u64) },
        ark_bls12_381::G1Affine::new_unchecked(Fq::from(0u64), Fq::from(2u64)).into_group()];
    let mut state = 0xc0fa_c703_381u64;
    while points.len() < 14 {
        if let Some(p) = ark_bls12_381::G1Affine::get_point_from_x_unchecked(Fq::from(next(&mut state)), false) {
            points.push(p.into_group());
        }
    }
    let cases = points.len();
    let mut boundaries = 0;
    let mut excluded_fr = 0;
    let mut inverse_states = 0;
    for p in points {
        let native = curve_g1::Point { x: Fp::from_limbs(p.x.into_bigint().0).unwrap(),
            y: Fp::from_limbs(p.y.into_bigint().0).unwrap(), z: Fp::from_limbs(p.z.into_bigint().0).unwrap() };
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        ark_ff::migration_trace::start_inverse();
        curve_g1::migration_trace::start_inverse();
        let expected = p.into_affine().is_in_correct_subgroup_assuming_on_curve();
        let upstream: Vec<_> = ark_ff::migration_trace::take().into_iter().filter(|event| match event.limbs.len() {
            6 | 12 => true,
            4 | 8 => { excluded_fr += 1; false },
            n => panic!("Unexpected field trace width {n}"),
        }).collect();
        let actual = curve_g1::scalar::in_subgroup(native);
        let minimal = curve_g1::migration_trace::take();
        compare_execution(&minimal, &upstream);
        inverse_states += compare_inverse_execution();
        boundaries += upstream.len();
        assert_eq!(actual, expected);
    }
    assert!(inverse_states > 0, "subgroup normalization must exercise inverse state comparisons");
    println!("Compared {cases} source fast subgroup cases at {boundaries} actual Fq execution boundaries and {inverse_states} inverse states; {excluded_fr} Fr boundaries excluded.");
}

#[test]
fn actual_source_field_power_schedule() {
    let mut bases = vec![Fq::from(0u64), Fq::from(1u64), -Fq::from(1u64)];
    let mut state = 0xf13d_9038_1u64;
    while bases.len() < 13 {
        bases.push(Fq::from(next(&mut state)));
    }
    let exponents = [
        [0u64; 6], [1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
        [17, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [u64::MAX; 6],
        [0xee7fbfffffffeaab, 0x7aaffffac54ffff, 0xd9cc34a83dac3d89,
         0xd91dd2e13ce144af, 0x92c6e9ed90d2eb35, 0x680447a8e5ff9a6],
    ];
    let mut boundaries = 0;
    let mut cases = 0;
    let mut sqrt_boundaries = 0;
    for a in &bases {
        let native = Fp::from_limbs(a.into_bigint().0).unwrap();
        for exponent in exponents {
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = a.pow(exponent);
            let upstream = ark_ff::migration_trace::take();
            let actual = curve_g1::field::pow(native, exponent);
            let minimal = curve_g1::migration_trace::take();
            compare_execution(&minimal, &upstream);
            assert_eq!(actual.to_montgomery_limbs(), expected.0 .0);
            boundaries += upstream.len();
            cases += 1;
        }
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let expected = a.sqrt();
        let upstream = ark_ff::migration_trace::take();
        let actual = native.sqrt();
        let minimal = curve_g1::migration_trace::take();
        compare_execution(&minimal, &upstream);
        assert_eq!(actual.map(|x| x.to_montgomery_limbs()), expected.map(|x| x.0 .0));
        sqrt_boundaries += upstream.len();
    }
    println!("Compared {cases} source Fq powers at {boundaries} actual execution boundaries and {} square roots at {sqrt_boundaries} boundaries.", bases.len());
}

#[test]
fn actual_source_integer_api_schedule() {
    use ark_ec::{AffineRepr, CurveGroup};
    let generator = ark_bls12_381::G1Affine::generator().into_group();
    let scale = Fq::from(7u64);
    let mut points = vec![generator,
        ark_bls12_381::G1Projective { x: generator.x*scale*scale,
            y: generator.y*scale*scale*scale, z: scale },
        ark_bls12_381::G1Projective::default(),
        ark_bls12_381::G1Projective { x: Fq::from(13u64), y: Fq::from(7u64), z: Fq::from(0u64) },
        ark_bls12_381::G1Projective { x: Fq::from(3u64), y: Fq::from(7u64), z: Fq::from(2u64) },
        ark_bls12_381::G1Affine::new_unchecked(Fq::from(0u64), Fq::from(2u64)).into_group()];
    let mut state = 0xc0fa_c703_381u64;
    while points.len() < 14 {
        if let Some(p) = ark_bls12_381::G1Affine::get_point_from_x_unchecked(Fq::from(next(&mut state)), false) {
            points.push(p.into_group());
        }
    }
    let scalars = [[0; 4], [1, 0, 0, 0], ark_bls12_381::Fr::MODULUS.0, [u64::MAX; 4]];
    let mut cases = 0;
    let mut boundaries = 0;
    let mut inverse_states = 0;
    for p in points {
        let native = curve_g1::Point { x: Fp::from_limbs(p.x.into_bigint().0).unwrap(),
            y: Fp::from_limbs(p.y.into_bigint().0).unwrap(), z: Fp::from_limbs(p.z.into_bigint().0).unwrap() };
        for scalar in scalars {
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            ark_ff::migration_trace::start_inverse();
            curve_g1::migration_trace::start_inverse();
            let expected = p.into_affine().mul_bigint(scalar);
            let upstream = ark_ff::migration_trace::take();
            let actual = curve_g1::mul_256(native, scalar);
            let minimal = curve_g1::migration_trace::take();
            compare_execution(&minimal, &upstream);
            inverse_states += compare_inverse_execution();
            boundaries += upstream.len();
            cases += 1;
            assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
            assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
            assert_eq!(actual.z.to_montgomery_limbs(), expected.z.0 .0);
        }
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        ark_ff::migration_trace::start_inverse();
        curve_g1::migration_trace::start_inverse();
        let expected = p.into_affine().mul_bigint([u64::MAX, 0, 0, 0]);
        let upstream = ark_ff::migration_trace::take();
        let actual = curve_g1::field::mul_u64_concrete(native, u64::MAX);
        let minimal = curve_g1::migration_trace::take();
        compare_execution(&minimal, &upstream);
        inverse_states += compare_inverse_execution();
        boundaries += upstream.len();
        cases += 1;
        assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
        assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
        assert_eq!(actual.z.to_montgomery_limbs(), expected.z.0 .0);
    }
    assert!(inverse_states > 0);
    println!("Compared {cases} source integer API cases at {boundaries} actual Fq execution boundaries and {inverse_states} inverse states.");
}

#[test]
fn actual_source_compressed_encoding_schedule() {
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_serialize::CanonicalSerialize;
    let generator = ark_bls12_381::G1Affine::generator().into_group();
    let scale = Fq::from(7u64);
    let mut points = vec![generator,
        ark_bls12_381::G1Projective { x: generator.x*scale*scale,
            y: generator.y*scale*scale*scale, z: scale },
        ark_bls12_381::G1Projective::default(),
        ark_bls12_381::G1Projective { x: Fq::from(13u64), y: Fq::from(7u64), z: Fq::from(0u64) },
        ark_bls12_381::G1Projective { x: Fq::from(3u64), y: Fq::from(7u64), z: Fq::from(2u64) },
        ark_bls12_381::G1Affine::new_unchecked(Fq::from(0u64), Fq::from(2u64)).into_group()];
    let mut state = 0xc0fa_c703_381u64;
    while points.len() < 14 {
        if let Some(p) = ark_bls12_381::G1Affine::get_point_from_x_unchecked(Fq::from(next(&mut state)), false) {
            points.push(p.into_group());
        }
    }
    let cases = points.len();
    let mut boundaries = 0;
    let mut inverse_states = 0;
    for p in points {
        let native = curve_g1::Point { x: Fp::from_limbs(p.x.into_bigint().0).unwrap(),
            y: Fp::from_limbs(p.y.into_bigint().0).unwrap(), z: Fp::from_limbs(p.z.into_bigint().0).unwrap() };
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        ark_ff::migration_trace::start_inverse();
        curve_g1::migration_trace::start_inverse();
        let mut expected = vec![];
        p.into_affine().serialize_compressed(&mut expected).unwrap();
        let upstream = ark_ff::migration_trace::take();
        let actual = curve_g1::field::compress(native);
        let minimal = curve_g1::migration_trace::take();
        compare_execution(&minimal, &upstream);
        inverse_states += compare_inverse_execution();
        boundaries += upstream.len();
        assert_eq!(actual.as_slice(), expected.as_slice());
    }
    assert!(inverse_states > 0);
    println!("Compared {cases} source compressed encodings at {boundaries} actual Fq execution boundaries and {inverse_states} inverse states.");
}

#[test]
fn actual_source_point_recovery_schedule() {
    let mut xs = vec![Fq::from(0u64), Fq::from(1u64), -Fq::from(1u64)];
    let mut state = 0xdec0_de38_1u64;
    while xs.len() < 13 {
        xs.push(Fq::from(next(&mut state)));
    }
    let mut cases = 0;
    let mut boundaries = 0;
    for x in xs {
        let native = Fp::from_limbs(x.into_bigint().0).unwrap();
        ark_ff::migration_trace::take();
        curve_g1::migration_trace::take();
        let expected = ark_bls12_381::G1Affine::get_ys_from_x_unchecked(x);
        let upstream = ark_ff::migration_trace::take();
        let actual = curve_g1::decoder::ys_from_x_unchecked(native);
        let minimal = curve_g1::migration_trace::take();
        compare_execution(&minimal, &upstream);
        assert_eq!(actual.map(|(a,b)| (a.to_montgomery_limbs(),b.to_montgomery_limbs())),
            expected.map(|(a,b)| (a.0 .0,b.0 .0)));
        boundaries += upstream.len();
        cases += 1;
        for sign in [false,true] {
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = ark_bls12_381::G1Affine::get_point_from_x_unchecked(x, sign);
            let upstream = ark_ff::migration_trace::take();
            let actual = curve_g1::field::from_x(native, sign);
            let minimal = curve_g1::migration_trace::take();
            compare_execution(&minimal, &upstream);
            assert_eq!(actual.map(|p| (p.x.to_montgomery_limbs(),p.y.to_montgomery_limbs(),p.z.to_montgomery_limbs())),
                expected.map(|p| (p.x.0 .0,p.y.0 .0,Fq::from(1u64).0 .0)));
            boundaries += upstream.len();
            cases += 1;
        }
    }
    println!("Compared {cases} source point recovery calls at {boundaries} actual Fq execution boundaries.");
}

#[test]
fn optimized_power_changes_trace_preserves_result() {
    let bases = [Fq::from(0u64), Fq::from(1u64), -Fq::from(1u64), Fq::from(7u64), Fq::from(1234567u64)];
    let exponents = [[0u64; 6], [1, 0, 0, 0, 0, 0], [17, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1 << 63], [u64::MAX; 6]];
    let mut cases = 0;
    let mut different = 0;
    for a in bases {
        let native = Fp::from_limbs(a.into_bigint().0).unwrap();
        for e in exponents {
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = a.pow(e);
            let upstream = ark_ff::migration_trace::take();
            let original = curve_g1::field::pow(native, e);
            let original_trace = curve_g1::migration_trace::take();
            compare_execution(&original_trace, &upstream);
            let optimized = curve_g1::optimized::field_power::pow(native, e);
            let optimized_trace = curve_g1::migration_trace::take();
            assert_eq!(original.to_montgomery_limbs(), expected.0 .0);
            assert_eq!(optimized.to_montgomery_limbs(), original.to_montgomery_limbs());
            if e == [0; 6] {
                assert!(original_trace.is_empty());
                assert!(optimized_trace.is_empty());
            } else {
                // One complete square (3 phases + 6 reduction rounds) and one
                // multiplication (6 rounds) are removed, rather than reordered.
                assert_eq!(original_trace.len(), optimized_trace.len() + 15);
                different += 1;
            }
            if a == Fq::from(7u64) && e == [17, 0, 0, 0, 0, 0] {
                assert_ne!(original_trace[0].limbs, optimized_trace[0].limbs);
                assert_eq!(original_trace.len(), 57);
                assert_eq!(optimized_trace.len(), 42);
                println!("Optimized power example 7^17: original 57 boundaries, optimized 42; first boundary differs; raw output identical.");
            }
            cases += 1;
        }
    }
    println!("Compared {cases} optimized powers; {different} nonzero-exponent traces differ by 15 fewer boundaries, with identical raw outputs.");
}

#[test]
fn alternative_power_reverses_bit_order_preserves_result() {
    let bases = [Fq::from(0u64), Fq::from(1u64), -Fq::from(1u64), Fq::from(7u64), Fq::from(1234567u64)];
    let exponents = [[0u64; 6], [1, 0, 0, 0, 0, 0], [17, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1 << 63], [u64::MAX; 6]];
    let mut cases = 0;
    for a in bases {
        let native = Fp::from_limbs(a.into_bigint().0).unwrap();
        for e in exponents {
            ark_ff::migration_trace::take();
            curve_g1::migration_trace::take();
            let expected = a.pow(e);
            let upstream = ark_ff::migration_trace::take();
            let original = curve_g1::field::pow(native, e);
            let original_trace = curve_g1::migration_trace::take();
            compare_execution(&original_trace, &upstream);
            let alternative = curve_g1::alternative::field_power::pow(native, e);
            let alternative_trace = curve_g1::migration_trace::take();
            assert_eq!(original.to_montgomery_limbs(), expected.0 .0);
            assert_eq!(alternative.to_montgomery_limbs(), original.to_montgomery_limbs());
            let multiplications: usize = e.iter().map(|word| word.count_ones() as usize).sum();
            assert_eq!(alternative_trace.len(), 384 * 9 + multiplications * 6);
            if a == Fq::from(7u64) && e == [17, 0, 0, 0, 0, 0] {
                assert_eq!(original_trace.len(), 57);
                assert_eq!(alternative_trace.len(), 3468);
                assert_ne!(original_trace[0].limbs, alternative_trace[0].limbs);
                if let Ok(path) = std::env::var("POWER_TRACE_EXPORT") {
                    let arkworks = upstream.iter().map(|s| format!(
                        "{{\"limbs\":{:?},\"factor\":{},\"product_carry\":{},\"reduction_carry\":{}}}",
                        s.limbs, s.factor, s.product_carry, s.reduction_carry)).collect::<Vec<_>>().join(",");
                    let encode = |trace: &[curve_g1::migration_trace::Snapshot]| trace.iter().map(|s| format!(
                        "{{\"limbs\":{:?},\"factor\":{},\"product_carry\":{},\"reduction_carry\":{}}}",
                        s.limbs, s.factor, s.product_carry, s.reduction_carry)).collect::<Vec<_>>().join(",");
                    let data = format!(
                        "{{\"base\":7,\"exponent\":17,\"arkworks\":[{}],\"minimal\":[{}],\"alternative\":[{}],\"result_montgomery\":{:?}}}",
                        arkworks, encode(&original_trace), encode(&alternative_trace), original.to_montgomery_limbs());
                    std::fs::write(path, data).unwrap();
                }
                println!("Alternative power example 7^17: Arkworks/minimal 57 matching boundaries, LSB-first 3468 different boundaries; raw output identical.");
            }
            cases += 1;
        }
    }
    println!("Compared {cases} LSB-first powers against original and actual arkworks, with 384 squares per call.");
}

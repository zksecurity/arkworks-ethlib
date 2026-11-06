#[allow(dead_code)]
#[path = "../src/curve_support.rs"]
mod support;

use ark_bls12_381::{Fq, Fq12, Fq2, Fq6, G2Projective};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{CyclotomicMultSubgroup, Field as ArkField, Zero};
use curve_g1::pairing::{self, Fp12, Fp2, Fp6, G2};
use support::{export_field, import_field};

fn import2(x: Fq2) -> Fp2 {
    Fp2 {
        c0: import_field(x.c0),
        c1: import_field(x.c1),
    }
}
fn export2(x: Fp2) -> Fq2 {
    Fq2::new(export_field(x.c0), export_field(x.c1))
}
fn import6(x: Fq6) -> Fp6 {
    Fp6 {
        c0: import2(x.c0),
        c1: import2(x.c1),
        c2: import2(x.c2),
    }
}
fn export6(x: Fp6) -> Fq6 {
    Fq6::new(export2(x.c0), export2(x.c1), export2(x.c2))
}
fn import12(x: Fq12) -> Fp12 {
    Fp12 {
        c0: import6(x.c0),
        c1: import6(x.c1),
    }
}
fn export12(x: Fp12) -> Fq12 {
    Fq12::new(export6(x.c0), export6(x.c1))
}
fn sample2(n: u64) -> Fq2 {
    Fq2::new(Fq::from(n), -Fq::from(n + 1))
}
fn sample6(n: u64) -> Fq6 {
    Fq6::new(sample2(n), sample2(n + 2), sample2(n + 4))
}

#[test]
fn extension_arithmetic_matches_arkworks() {
    for n in [0, 1, 17] {
        let a = sample2(n);
        let b = sample2(n + 7);
        let x = import2(a);
        let y = import2(b);
        assert_eq!(export2(x.plus(y)), a + b);
        assert_eq!(export2(x.minus(y)), a - b);
        assert_eq!(export2(x.times(y)), a * b);
        assert_eq!(export2(x.square()), a.square());
        for power in [0, 1, 2, 3, 6, 11, 12, usize::MAX - 1, usize::MAX] {
            let expected = a.frobenius_map(power);
            let actual = x.frobenius(power);
            assert_eq!(export2(actual), expected);
            assert_eq!(actual.c0.to_montgomery_limbs(), expected.c0.0 .0);
            assert_eq!(actual.c1.to_montgomery_limbs(), expected.c1.0 .0);
        }
        assert_eq!(export2(x.negative()), -a);
        assert_eq!(export2(x.inverse()), a.inverse().unwrap_or_default());
        assert_eq!(export2(x.mul_xi()), a * Fq2::new(Fq::from(1), Fq::from(1)));
        let a = sample6(n);
        let b = sample6(n + 7);
        let x = import6(a);
        let y = import6(b);
        assert_eq!(export6(x.plus(y)), a + b);
        assert_eq!(export6(x.minus(y)), a - b);
        assert_eq!(export6(x.times(y)), a * b);
        assert_eq!(export6(x.square()), a.square());
        for power in [0, 1, 2, 3, 4, 5, 6, 11, 12, usize::MAX - 1, usize::MAX] {
            assert_eq!(export6(x.frobenius(power)), a.frobenius_map(power));
        }
        let mut sparse = a;
        sparse.mul_by_1(&b.c1);
        assert_eq!(export6(x.mul_by_1(y.c1)), sparse);
        assert_eq!(sparse, a * Fq6::new(Fq2::zero(), b.c1, Fq2::zero()));
        let mut sparse = a;
        sparse.mul_by_01(&b.c0, &b.c1);
        assert_eq!(export6(x.mul_by_01(y.c0, y.c1)), sparse);
        assert_eq!(sparse, a * Fq6::new(b.c0, b.c1, Fq2::zero()));
        assert_eq!(export6(x.negative()), -a);
        assert_eq!(export6(x.inverse()), a.inverse().unwrap_or_default());
        assert_eq!(
            export6(x.mul_v()),
            a * Fq6::new(Fq2::zero(), Fq2::from(1u64), Fq2::zero())
        );
        let a = Fq12::new(a, b);
        let b = Fq12::new(b, sample6(n + 19));
        let x = import12(a);
        let y = import12(b);
        assert_eq!(export12(x.plus(y)), a + b);
        assert_eq!(export12(x.minus(y)), a - b);
        assert_eq!(export12(x.times(y)), a * b);
        assert_eq!(export12(x.square()), a.square());
        assert_eq!(export12(x.cyclotomic_square()), a.cyclotomic_square());
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
            assert_eq!(export12(x.frobenius(power)), a.frobenius_map(power));
        }
        let mut sparse = a;
        sparse.mul_by_014(&b.c0.c0, &b.c0.c1, &b.c1.c1);
        assert_eq!(export12(x.mul_by_014(y.c0.c0, y.c0.c1, y.c1.c1)), sparse);
        assert_eq!(
            sparse,
            a * Fq12::new(
                Fq6::new(b.c0.c0, b.c0.c1, Fq2::zero()),
                Fq6::new(Fq2::zero(), b.c1.c1, Fq2::zero())
            )
        );
        assert_eq!(x.is_zero(), a.is_zero());
        assert_eq!(export12(x.negative()), -a);
        assert_eq!(export12(x.inverse()), a.inverse().unwrap_or_default());
        assert_eq!(export12(x.conjugate()), Fq12::new(a.c0, -a.c1));
        assert!(x.equal(x));
        assert!(!x.is_one());
    }
    assert!(Fp12::one().is_one());
    assert!(Fp2::zero().inverse().is_zero());
    assert!(Fp6::zero().inverse().is_zero());
    assert!(Fp12::zero().inverse().equal(Fp12::zero()));
}

#[test]
fn g2_affine_matches_arkworks() {
    let p = G2Projective::generator();
    for z in [Fq2::from(1u64), sample2(11)] {
        let scaled = G2Projective::new_unchecked(p.x * z * z, p.y * z * z * z, p.z * z);
        let raw = G2 {
            x: import2(scaled.x),
            y: import2(scaled.y),
            z: import2(scaled.z),
        };
        let normalized = pairing::prepared::normalize_g2(raw);
        let (x, y) = (normalized.x, normalized.y);
        assert!(!normalized.infinity);
        let affine = scaled.into_affine();
        assert_eq!(export2(x), affine.x);
        assert_eq!(export2(y), affine.y);
    }
    let normalized = pairing::prepared::normalize_g2(G2 {
        x: Fp2::one(),
        y: Fp2::one(),
        z: Fp2::zero(),
    });
    assert!(normalized.infinity && normalized.x.is_zero() && normalized.y.is_zero());
}

#[test]
fn minimal_pairing_cancellation_and_non_degeneracy() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            use ark_bls12_381::{G1Projective, G2Affine};
            use ark_ec::AffineRepr;
            let p = G1Projective::generator();
            let q = G2Affine::generator();
            let raw_q = G2 {
                x: import2(q.x),
                y: import2(q.y),
                z: Fp2::one(),
            };
            let f =
                pairing::prepared_miller::multi_miller_loop(&[(support::import_point(p), raw_q)]);
            assert!(!pairing::final_exponentiation(f).is_one());
            let neg =
                pairing::prepared_miller::multi_miller_loop(&[(support::import_point(-p), raw_q)]);
            assert!(pairing::final_exponentiation(f.times(neg)).is_one());
            let infinity = curve_g1::identity::<curve_g1::field::Fp>();
            assert!(pairing::prepared_miller::multi_miller_loop(&[(infinity, raw_q)]).is_one());
            assert!(pairing::final_exponentiation(Fp12::one()).is_one());
            assert!(pairing::pairing_check(&[]));
            assert!(pairing::final_exponentiation(Fp12::zero()).equal(Fp12::zero()));
            assert!(pairing::pairing_check(&[
                (infinity, raw_q),
                (support::import_point(p), raw_q),
                (support::import_point(-p), raw_q),
                (infinity, raw_q),
            ]));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn arkworks_final_exponentiation_uses_cubed_convention() {
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::{MillerLoopOutput, Pairing};

    // EthLib finalExpHard, used only as an independent ordinary-power reference.
    const ETHLIB_HARD_EXPONENT: [u64; 20] = [
        0xe516c3f438e3ba79,
        0xfa9912aae208ccf1,
        0x905ce937335d5b68,
        0xc71a2629b0dea236,
        0x83774940996754c8,
        0x21d160aeb6a1e799,
        0x2ed0b283ed237db4,
        0x915c97f36c6f1821,
        0x67f17fcbde783765,
        0x2378b9039096d1b7,
        0x7988f8761bdc51dc,
        0x2076995003fc77a1,
        0x827eca0ba621315b,
        0xe5a72bce8d63cb9f,
        0xf68f7764c28b6f8a,
        0x2f230063cf081517,
        0x94506632528d6a9a,
        0xd3cde88eeb996ca3,
        0xc0bd38c3195c899e,
        0x000f686b3d807d01,
    ];

    let mut nontrivial_difference = false;
    for n in [0, 1, 17] {
        let input = Fq12::new(sample6(n), sample6(n + 3));
        let easy = export12(pairing::final_exponentiation_easy(import12(input)));
        let ordinary = easy.pow(ETHLIB_HARD_EXPONENT);
        let actual = export12(pairing::final_exponentiation(import12(input)));
        let upstream = Bls12_381::final_exponentiation(MillerLoopOutput(input))
            .unwrap()
            .0;
        assert_eq!(ordinary.square() * ordinary, upstream);
        assert_eq!(actual, upstream);
        nontrivial_difference |= ordinary != upstream;
    }
    assert!(nontrivial_difference);
    assert!(Bls12_381::final_exponentiation(MillerLoopOutput(Fq12::zero())).is_none());
    assert!(pairing::final_exponentiation(Fp12::zero()).equal(Fp12::zero()));
}

#[test]
fn easy_final_exponentiation_matches_arkworks_and_enters_cyclotomic_group() {
    for n in [0, 1, 17] {
        let input = Fq12::new(sample6(n), sample6(n + 3));
        let mut expected = input;
        expected.conjugate_in_place();
        expected *= input.inverse().unwrap();
        let first = expected;
        expected.frobenius_map_in_place(2);
        expected *= first;
        let raw = pairing::final_exponentiation_easy(import12(input));
        let actual = export12(raw);
        assert_eq!(actual, expected);
        assert_eq!(export12(raw.cyclotomic_square()), actual.square());
        assert_eq!(actual.cyclotomic_square(), actual.square());
        assert!(!actual.is_zero());
        assert_eq!(actual.frobenius_map(4) * actual, actual.frobenius_map(2));
        assert_eq!(actual * actual.frobenius_map(6), Fq12::from(1u64));
    }
    assert!(pairing::final_exponentiation_easy(Fp12::zero()).equal(Fp12::zero()));
    assert!(Fp12::zero().cyclotomic_square().equal(Fp12::zero()));
}

#[test]
fn signed_parameter_exponent_matches_arkworks() {
    assert_eq!(
        ark_ff::biginteger::arithmetic::find_naf(&[pairing::BLS_X]),
        pairing::BLS_X_NAF
    );
    assert_eq!(export12(Fp12::cyclotomic_one()), Fq12::ONE);
    for n in 0..16 {
        let raw = if n == 0 {
            Fq12::zero()
        } else {
            Fq12::new(sample6(n), sample6(n + 8))
        };
        let easy = pairing::final_exponentiation_easy(import12(raw));
        for input in [raw, export12(easy)] {
            let expected = input.cyclotomic_exp([pairing::BLS_X]);
            let mut signed = expected;
            signed.cyclotomic_inverse_in_place();
            let minimal = import12(input);
            assert_eq!(export12(minimal.cyclotomic_exp_x_abs()), expected);
            assert_eq!(export12(minimal.exp_by_x()), signed);
        }
        let input = export12(easy);
        let expected = input.pow([pairing::BLS_X]).inverse().unwrap_or_default();
        assert_eq!(export12(easy.exp_by_x()), expected);
    }
}

#[test]
fn optimized_hard_chain_matches_actual_arkworks_final_exponent() {
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::{MillerLoopOutput, Pairing};
    for n in 0..16 {
        let raw = if n == 0 {
            Fq12::zero()
        } else {
            Fq12::new(sample6(n), sample6(n + 8))
        };
        let expected = Bls12_381::final_exponentiation(MillerLoopOutput(raw))
            .map(|r| r.0)
            .unwrap_or_default();
        let actual = if raw.is_zero() {
            Fp12::zero()
        } else {
            pairing::final_exponentiation_hard(pairing::final_exponentiation_easy(import12(raw)))
        };
        assert_eq!(export12(actual), expected);
    }
}

#[test]
fn prepared_g2_matches_actual_arkworks() {
    use ark_bls12_381::{Config, G1Affine};
    use ark_ec::bls12::G2Prepared;
    use ark_ec::AffineRepr;
    use curve_g1::pairing::prepared::{self, LineCoeff};
    let compare = |c: LineCoeff, expected: &(Fq2, Fq2, Fq2)| {
        assert_eq!(export2(c.c0), expected.0);
        assert_eq!(export2(c.c1), expected.1);
        assert_eq!(export2(c.c2), expected.2);
    };
    for n in 1..=8 {
        let q = (G2Projective::generator() * ark_bls12_381::Fr::from(n)).into_affine();
        let upstream = G2Prepared::<Config>::from(q);
        let qx = import2(q.x);
        let qy = import2(q.y);
        let actual = prepared::prepare_affine(qx, qy, false);
        assert!(!actual.infinity);
        assert_eq!(actual.ell_coeffs.len(), upstream.ell_coeffs.len());
        for (a, b) in actual.ell_coeffs.into_iter().zip(&upstream.ell_coeffs) {
            compare(a, b);
        }
        let zero = prepared::prepare_affine(qx, qy, true);
        assert!(zero.infinity);
        assert!(zero.ell_coeffs.is_empty());
        let c = upstream.ell_coeffs[0];
        let point = G1Affine::generator();
        let f = Fq12::new(sample6(n), sample6(n + 9));
        let mut c1 = c.1;
        let mut c2 = c.2;
        c2.mul_assign_by_fp(&point.y);
        c1.mul_assign_by_fp(&point.x);
        let mut expected = f;
        expected.mul_by_014(&c.0, &c1, &c2);
        let actual = prepared::ell(
            import12(f),
            LineCoeff {
                c0: import2(c.0),
                c1: import2(c.1),
                c2: import2(c.2),
            },
            import_field(point.x),
            import_field(point.y),
        );
        assert_eq!(export12(actual), expected);
    }
}

#[test]
fn off_curve_pairing_uses_upstream_zero_adapter() {
    use ark_bls12_381::{Bls12_381, G1Projective, G2Affine};
    use ark_ec::pairing::Pairing;
    let p = G1Projective::generator();
    let q = G2Affine::new_unchecked(Fq2::ONE, Fq2::zero());
    assert!(p.into_affine().is_on_curve());
    assert!(!q.is_on_curve());
    let miller = Bls12_381::multi_miller_loop([p.into_affine()], [q]);
    assert!(miller.0.is_zero());
    let upstream = Bls12_381::final_exponentiation(miller);
    assert!(upstream.is_none());
    let native_q = G2 {
        x: Fp2::one(),
        y: Fp2::zero(),
        z: Fp2::one(),
    };
    let prepared =
        pairing::prepared_miller::multi_miller_loop(&[(support::import_point(p), native_q)]);
    assert!(prepared.is_zero());
    assert!(!pairing::prepared_miller::pairing_check(&[(
        support::import_point(p),
        native_q
    )]));
    // The default source path maps upstream None to false on this off-curve input.
    // Its EthLib equivalence theorem explicitly requires the finite-G2 subgroup domain.
    assert!(!pairing::pairing_check(&[(
        support::import_point(p),
        native_q
    )]));
}

#[test]
fn projective_preparation_matches_arkworks() {
    use ark_bls12_381::{Config, Fr, G1Projective};
    use ark_ec::bls12::{G1Prepared, G2Prepared};
    use curve_g1::pairing::prepared;
    for n in [0, 1, 2, 17] {
        let p = (G1Projective::generator() * Fr::from(n)).into_affine();
        let q = (G2Projective::generator() * Fr::from(n)).into_affine();
        for (z1, z2) in [
            (Fq::from(0u64), Fq2::zero()),
            (Fq::ONE, Fq2::ONE),
            (Fq::from(17u64), sample2(7)),
        ] {
            let pz = if p.infinity { Fq::from(0u64) } else { z1 };
            let qz = if q.infinity { Fq2::zero() } else { z2 };
            let pp = G1Projective::new_unchecked(p.x * z1 * z1, p.y * z1 * z1 * z1, pz);
            let qp = G2Projective::new_unchecked(q.x * z2 * z2, q.y * z2 * z2 * z2, qz);
            let expected_p = G1Prepared::<Config>::from(pp);
            let actual_p = prepared::prepare_g1(support::import_point(pp));
            assert_eq!(actual_p.x.to_montgomery_limbs(), expected_p.0.x.0 .0);
            assert_eq!(actual_p.y.to_montgomery_limbs(), expected_p.0.y.0 .0);
            assert_eq!(actual_p.infinity, expected_p.0.infinity);
            let native_q = G2 {
                x: import2(qp.x),
                y: import2(qp.y),
                z: import2(qp.z),
            };
            let affine = qp.into_affine();
            let actual_q = prepared::normalize_g2(native_q);
            assert_eq!(export2(actual_q.x), affine.x);
            assert_eq!(export2(actual_q.y), affine.y);
            assert_eq!(actual_q.infinity, affine.infinity);
            let expected = G2Prepared::<Config>::from(qp);
            let actual = prepared::prepare_g2(native_q);
            assert_eq!(actual.infinity, expected.infinity);
            assert_eq!(actual.ell_coeffs.len(), expected.ell_coeffs.len());
            for (a, b) in actual.ell_coeffs.into_iter().zip(expected.ell_coeffs) {
                assert_eq!(export2(a.c0), b.0);
                assert_eq!(export2(a.c1), b.1);
                assert_eq!(export2(a.c2), b.2);
            }
        }
    }
}

#[test]
fn prepared_miller_matches_actual_arkworks() {
    use ark_bls12_381::{Bls12_381, Fr, G1Projective};
    use ark_ec::pairing::Pairing;
    for size in [0, 1, 3, 4, 5, 8, 9] {
        for with_infinity in [false, true] {
            let mut ps = Vec::new();
            let mut qs = Vec::new();
            let mut native = Vec::new();
            for i in 0..size {
                let mut p = G1Projective::generator() * Fr::from((i + 1) as u64);
                let mut q = G2Projective::generator() * Fr::from((i + 2) as u64);
                if with_infinity && i % 3 == 0 {
                    p = G1Projective::zero();
                }
                if with_infinity && i % 3 == 1 {
                    q = G2Projective::zero();
                }
                native.push((
                    support::import_point(p),
                    G2 {
                        x: import2(q.x),
                        y: import2(q.y),
                        z: import2(q.z),
                    },
                ));
                ps.push(p);
                qs.push(q);
            }
            let expected = Bls12_381::multi_miller_loop(ps, qs).0;
            let actual = pairing::prepared_miller::multi_miller_loop(&native);
            assert_eq!(export12(actual), expected);
            let expected_check =
                Bls12_381::final_exponentiation(ark_ec::pairing::MillerLoopOutput(expected))
                    .map(|r| r.0 == Fq12::ONE)
                    .unwrap_or(false);
            assert_eq!(
                pairing::prepared_miller::pairing_check(&native),
                expected_check
            );
        }
    }
}

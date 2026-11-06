#[path = "../src/curve_support.rs"]
mod support;

use ark_bls12_381::{Fq, Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, BigInteger, Field as ArkField, PrimeField};
use curve_g1::{
    field::{Fp, MODULUS},
    Field, Point,
};
use support::*;

fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn assert_point(actual: Point<Fp>, expected: G1Projective) {
    let actual = export_point(actual).into_affine();
    assert!(actual.is_on_curve());
    assert_eq!(actual, expected.into_affine());
}

fn assert_montgomery_coordinates(actual: Point<Fp>, expected: G1Projective) {
    assert_eq!(actual.x.to_montgomery_limbs(), expected.x.0 .0);
    assert_eq!(actual.y.to_montgomery_limbs(), expected.y.0 .0);
    assert_eq!(actual.z.to_montgomery_limbs(), expected.z.0 .0);
}

fn scaled(p: G1Projective, scale: Fq) -> G1Projective {
    G1Projective::new_unchecked(
        p.x * scale * scale,
        p.y * scale * scale * scale,
        p.z * scale,
    )
}

#[test]
fn canonical_field_against_arkworks() {
    assert_eq!(MODULUS, Fq::MODULUS.0);
    assert!(Fp::from_limbs(MODULUS).is_none());
    assert!(Fp::from_limbs([u64::MAX; 6]).is_none());
    let mut half = Fq::MODULUS;
    half.div2();
    let half = Fq::from_bigint(half).unwrap();
    let edge = [
        Fq::from(0),
        Fq::from(1),
        -Fq::from(1),
        half,
        half + Fq::from(1),
        Fq::from(u64::MAX),
        Fq::from(u64::MAX) + Fq::from(1),
    ];
    let mut pairs = Vec::new();
    for a in edge {
        for b in edge {
            pairs.push((a, b));
        }
    }
    let mut state = 0x371aeea5;
    for _ in 0..128 {
        let mut bytes = [0u8; 96];
        for chunk in bytes.chunks_exact_mut(8) {
            chunk.copy_from_slice(&next(&mut state).to_le_bytes());
        }
        pairs.push((
            Fq::from_le_bytes_mod_order(&bytes[..48]),
            Fq::from_le_bytes_mod_order(&bytes[48..]),
        ));
    }
    for (a, b) in pairs {
        let (x, y) = (import_field(a), import_field(b));
        assert_eq!(x.to_montgomery_limbs(), a.0 .0);
        assert_eq!(y.to_montgomery_limbs(), b.0 .0);
        for (actual, expected) in [
            (x.plus(y), a + b),
            (x.minus(y), a - b),
            (x.times(y), a * b),
            (x.square(), a.square()),
            (Fp::sum_products(x, y, x, y), a * b + a * b),
            (Fp::sum_products(x, y, x.negative(), y), Fq::from(0)),
            (x.negative(), -a),
        ] {
            assert_eq!(actual.to_montgomery_limbs(), expected.0 .0);
        }
        assert_eq!(export_field(x.plus(y)), a + b);
        assert_eq!(export_field(x.minus(y)), a - b);
        assert_eq!(export_field(x.times(y)), a * b);
        assert_eq!(export_field(x.square()), a.square());
        assert_eq!(export_field(x.negative()), -a);
        assert_eq!(x.equal(y), a == b);
        assert_eq!(x.is_zero(), a == Fq::from(0));
        let binary = curve_g1::field::inversion::inverse(x);
        assert_eq!(binary.map(export_field), a.inverse());
        assert_eq!(
            binary.map(|v| v.to_montgomery_limbs()),
            a.inverse().map(|v| v.0 .0)
        );
    }
}

#[test]
fn jacobian_branches_and_rescaling() {
    let g = G1Affine::generator().into_group();
    assert_point(curve_g1::field::generator(), g);
    assert_montgomery_coordinates(curve_g1::field::generator(), g);
    let zero = G1Affine::identity().into_group();
    let unusual_zero = G1Projective::new_unchecked(Fq::from(37), Fq::from(91), Fq::from(0));
    let mut points = vec![
        zero,
        unusual_zero,
        g,
        -g,
        scaled(g, Fq::from(7)),
        scaled(-g, Fq::from(19)),
    ];
    for n in [2, 3, 17, 63, 12345] {
        points.push(G1Affine::generator().mul_bigint([n]));
    }
    // (0,2) is on the curve but outside the prime-order subgroup.
    let torsion = G1Affine::new_unchecked(Fq::from(0), Fq::from(2));
    assert!(torsion.is_on_curve());
    assert!(!torsion.is_in_correct_subgroup_assuming_on_curve());
    points.push(torsion.into_group());
    for p in &points {
        assert_point(curve_g1::negate(import_point(*p)), -*p);
        let doubled = curve_g1::double(import_point(*p));
        let expected = p.double();
        assert_montgomery_coordinates(doubled, expected);
        let raw = export_point(doubled);
        assert_eq!((raw.x, raw.y, raw.z), (expected.x, expected.y, expected.z));
        assert_point(doubled, expected);
        for q in &points {
            let sum = curve_g1::add(import_point(*p), import_point(*q));
            let expected = *p + *q;
            assert_montgomery_coordinates(sum, expected);
            let raw = export_point(sum);
            assert_eq!((raw.x, raw.y, raw.z), (expected.x, expected.y, expected.z));
            assert_point(sum, expected);
            let affine = q.into_affine();
            let sum = curve_g1::add_affine(
                import_point(*p),
                curve_g1::AffinePoint {
                    x: import_field(affine.x),
                    y: import_field(affine.y),
                    infinity: affine.infinity,
                },
            );
            let mut expected = *p;
            expected += affine;
            assert_montgomery_coordinates(sum, expected);
            assert_point(sum, expected);
        }
    }
}

#[test]
fn scalar_multiplication_boundaries() {
    let g = G1Affine::generator();
    let p = g.mul_bigint([17]);
    for n in [0, 1, 2, 3, 63, 64, 65, 1 << 63, u64::MAX] {
        assert_point(
            curve_g1::mul_u64(import_point(p), n),
            p.into_affine().mul_bigint([n]),
        );
    }
    let r = Fr::MODULUS.0;
    let mut rm1 = r;
    rm1[0] -= 1;
    let mut rp1 = r;
    rp1[0] += 1;
    let mut scalars = vec![
        [0; 4],
        [1, 0, 0, 0],
        r,
        rm1,
        rp1,
        [u64::MAX; 4],
        [0, 0, 0, 1 << 63],
    ];
    let mut state = 0x123aeea5;
    for _ in 0..4 {
        scalars.push(core::array::from_fn(|_| next(&mut state)));
    }
    let torsion = G1Affine::new_unchecked(Fq::from(0), Fq::from(2));
    for point in [g, torsion] {
        for k in &scalars {
            assert_point(
                curve_g1::mul_256(import_point(point.into_group()), *k),
                point.mul_bigint(*k),
            );
        }
    }
    assert_point(
        curve_g1::mul_256(curve_g1::identity::<Fp>(), [u64::MAX; 4]),
        G1Affine::identity().into_group(),
    );
}

#[test]
fn encoding_boundaries_and_pipeline() {
    use ark_ff::Field as ArkField;
    let mut half = Fq::MODULUS;
    half.div2();
    let half = Fq::from_bigint(half).unwrap();
    let mut values = vec![
        Fq::from(0),
        Fq::from(1),
        -Fq::from(1),
        half,
        half + Fq::from(1),
    ];
    // Exercise every limb and byte boundary, including truncation of high bits.
    for bit in 0..381 {
        let mut limbs = [0u64; 6];
        limbs[bit / 64] = 1 << (bit % 64);
        values.push(Fq::from_bigint(ark_ff::BigInt(limbs)).unwrap());
    }
    for a in values {
        let x = import_field(a);
        assert_eq!(x.to_bytes_be().as_slice(), a.into_bigint().to_bytes_be());
        assert_eq!(x.sign_bit(), a > -a);
    }
    for a in [Fq::from(0), Fq::from(1), Fq::from(7), -Fq::from(1), half] {
        assert_eq!(
            export_field(import_field(a).inverse()),
            a.inverse().unwrap_or(Fq::from(0))
        );
    }
    let g = G1Affine::generator().into_group();
    let torsion = G1Affine::new_unchecked(Fq::from(0), Fq::from(2)).into_group();
    let unusual_zero = G1Projective::new_unchecked(Fq::from(37), Fq::from(91), Fq::from(0));
    for p in [g, -g, scaled(g, Fq::from(7)), torsion, unusual_zero] {
        assert_eq!(
            curve_g1::field::compress(import_point(p)),
            ark_eth_bridge::encode_g1(&p.into_affine()).unwrap()
        );
        for k in [
            [0; 4],
            [1, 0, 0, 0],
            [17, 0, 0, 0],
            Fr::MODULUS.0,
            [u64::MAX; 4],
        ] {
            assert_eq!(
                curve_g1::field::mul_compressed(import_point(p), k),
                ark_eth_bridge::encode_g1(&p.into_affine().mul_bigint(k).into_affine()).unwrap()
            );
        }
    }
}

#[test]
fn subgroup_check_against_arkworks() {
    use ark_ff::Field as ArkField;
    let g = G1Affine::generator().into_group();
    let torsion = G1Affine::new_unchecked(Fq::from(0), Fq::from(2)).into_group();
    let mut points = vec![
        G1Affine::identity().into_group(),
        g,
        -g,
        torsion,
        -torsion,
        g + torsion,
        g - torsion,
        scaled(g, Fq::from(7)),
        scaled(torsion, Fq::from(19)),
        scaled(g + torsion, Fq::from(37)),
    ];
    for n in [2, 17, 12345, u64::MAX] {
        points.push(G1Affine::generator().mul_bigint([n]));
    }
    // Sample full-curve points without clearing their cofactor.
    let mut state = 0x5ab670a;
    for _ in 0..32 {
        let x = Fq::from(next(&mut state));
        if let Some(y) = (x * x * x + Fq::from(4)).sqrt() {
            points.push(G1Affine::new_unchecked(x, y).into_group());
        }
    }
    let mut accepted = 0;
    let mut rejected = 0;
    for p in points {
        let affine = p.into_affine();
        assert!(affine.is_on_curve());
        let expected = affine.is_in_correct_subgroup_assuming_on_curve();
        assert_eq!(curve_g1::field::in_subgroup(import_point(p)), expected);
        if expected {
            accepted += 1;
        } else {
            rejected += 1;
        }
    }
    assert!(accepted >= 8 && rejected >= 5);
    // Any Jacobian representation with z=0 denotes infinity.
    let zero = Point {
        x: Fp::constant(37),
        y: Fp::constant(91),
        z: Fp::constant(0),
    };
    assert!(curve_g1::field::in_subgroup(zero));
}

#[test]
fn checked_point_validation_against_arkworks() {
    use ark_ff::Field as ArkField;
    let g = G1Affine::generator().into_group();
    let torsion = G1Affine::new_unchecked(Fq::from(0), Fq::from(2)).into_group();
    let mut points = vec![
        g,
        -g,
        torsion,
        g + torsion,
        G1Affine::identity().into_group(),
        scaled(g, Fq::from(7)),
        scaled(torsion, Fq::from(19)),
        G1Projective::new_unchecked(Fq::from(37), Fq::from(91), Fq::from(0)),
        G1Projective::new_unchecked(Fq::from(0), Fq::from(0), Fq::from(1)),
        G1Projective::new_unchecked(g.x, g.y + Fq::from(1), g.z),
    ];
    let mut state = 0xdecaf381;
    for _ in 0..32 {
        let x = Fq::from(next(&mut state));
        if let Some(y) = (x * x * x + Fq::from(4)).sqrt() {
            points.push(G1Affine::new_unchecked(x, y).into_group());
        }
        points.push(G1Projective::new_unchecked(
            x,
            Fq::from(next(&mut state)),
            Fq::from(3),
        ));
    }
    let mut off_curve = 0;
    let mut non_subgroup = 0;
    for point in points {
        let affine = point.into_affine();
        let on_curve = affine.is_on_curve();
        let valid = on_curve && affine.is_in_correct_subgroup_assuming_on_curve();
        let public_key = affine != G1Affine::identity() && valid;
        let p = import_point(point);
        assert_eq!(curve_g1::field::is_on_curve(p), on_curve);
        assert_eq!(curve_g1::field::is_valid_subgroup_point(p), valid);
        assert_eq!(curve_g1::field::is_valid_public_key_point(p), public_key);
        off_curve += usize::from(!on_curve);
        non_subgroup += usize::from(on_curve && !valid);
    }
    assert!(off_curve >= 32 && non_subgroup >= 2);
}

#[test]
fn square_roots_and_checked_affine_construction() {
    use ark_ff::Field as ArkField;
    let mut state = 0x5a7e381;
    let mut values = vec![Fq::from(0), Fq::from(1), Fq::from(4), -Fq::from(1)];
    for _ in 0..16 {
        let mut bytes = [0u8; 48];
        for chunk in bytes.chunks_exact_mut(8) {
            chunk.copy_from_slice(&next(&mut state).to_le_bytes());
        }
        values.push(Fq::from_le_bytes_mod_order(&bytes));
    }
    for a in values {
        let actual = import_field(a).sqrt();
        assert_eq!(actual.is_some(), a.sqrt().is_some());
        if let Some(root) = actual {
            assert_eq!(export_field(root) * export_field(root), a);
        }
        let square = a * a;
        let root = import_field(square)
            .sqrt()
            .expect("square must have a root");
        assert_eq!(export_field(root) * export_field(root), square);
    }
    let g = G1Affine::generator();
    for (x, y) in [
        (g.x, g.y),
        (g.x, -g.y),
        (Fq::from(0), Fq::from(2)),
        (Fq::from(0), Fq::from(0)),
        (g.x, g.y + Fq::from(1)),
    ] {
        let expected = G1Affine::new_unchecked(x, y);
        let actual = curve_g1::field::from_affine(import_field(x), import_field(y));
        assert_eq!(actual.is_some(), expected.is_on_curve());
        if let Some(p) = actual {
            assert_eq!(export_point(p).into_affine(), expected);
            assert_eq!(export_field(p.z), Fq::from(1));
        }
    }
}

#[test]
fn normalized_equality_and_checked_serialization() {
    let g = G1Affine::generator().into_group();
    let torsion = G1Affine::new_unchecked(Fq::from(0), Fq::from(2)).into_group();
    let points = [
        g,
        -g,
        g + g,
        torsion,
        g + torsion,
        scaled(g, Fq::from(7)),
        scaled(torsion, Fq::from(19)),
        G1Affine::identity().into_group(),
        G1Projective::new_unchecked(Fq::from(37), Fq::from(91), Fq::from(0)),
        G1Projective::new_unchecked(Fq::from(0), Fq::from(0), Fq::from(1)),
    ];
    for p in points {
        let raw = import_point(p);
        let affine = p.into_affine();
        let normal = curve_g1::field::normalize(raw);
        assert_eq!(export_point(normal).into_affine(), affine);
        assert_eq!(
            export_field(normal.z),
            Fq::from(u64::from(affine != G1Affine::identity()))
        );
        if affine == G1Affine::identity() {
            assert_eq!(export_field(normal.x), Fq::from(1));
            assert_eq!(export_field(normal.y), Fq::from(1));
        }
        let valid = affine.is_on_curve() && affine.is_in_correct_subgroup_assuming_on_curve();
        let expected = valid.then(|| ark_eth_bridge::encode_g1(&affine).unwrap());
        assert_eq!(curve_g1::field::compress_checked(raw), expected);
        let key_expected = if affine == G1Affine::identity() {
            None
        } else {
            expected
        };
        assert_eq!(curve_g1::field::compress_public_key(raw), key_expected);
        // Equality's public contract assumes on-curve inputs.
        if affine.is_on_curve() {
            for q in points {
                let aq = q.into_affine();
                if aq.is_on_curve() {
                    assert_eq!(
                        curve_g1::field::points_equal(raw, import_point(q)),
                        affine == aq
                    );
                }
            }
        }
    }
}

#[test]
fn recover_point_from_x_and_sign() {
    use ark_serialize::CanonicalDeserialize;
    let vectors =
        include_bytes!("../../test-vectors/zkcrypto/g1_compressed_valid_test_vectors.dat");
    // Published finite points exercise both root choices; infinity has no finite x/sign recovery.
    for bytes in vectors.chunks_exact(48).skip(1) {
        let expected = G1Affine::deserialize_compressed(bytes).unwrap();
        let actual = curve_g1::field::from_x(import_field(expected.x), bytes[0] & 0x20 != 0)
            .expect("published curve point has a square root");
        assert_eq!(export_point(actual).into_affine(), expected);
    }
    let mut state = 0x12345a7;
    for _ in 0..32 {
        let x = Fq::from(next(&mut state));
        let expected_ys = G1Affine::get_ys_from_x_unchecked(x);
        let actual_ys = curve_g1::decoder::ys_from_x_unchecked(import_field(x));
        assert_eq!(actual_ys.is_some(), expected_ys.is_some());
        if let (Some((lo, hi)), Some((expected_lo, expected_hi))) = (actual_ys, expected_ys) {
            assert_eq!(lo.to_montgomery_limbs(), expected_lo.0 .0);
            assert_eq!(hi.to_montgomery_limbs(), expected_hi.0 .0);
        }
        for sign in [false, true] {
            let expected = G1Affine::get_point_from_x_unchecked(x, sign);
            let actual = curve_g1::field::from_x(import_field(x), sign);
            let recovered = curve_g1::decoder::point_from_x_unchecked(import_field(x), sign);
            assert_eq!(recovered.is_some(), expected.is_some());
            if let (Some(p), Some(q)) = (recovered, expected) {
                assert_montgomery_coordinates(p, q.into_group());
            }

            assert_eq!(actual.is_some(), expected.is_some());
            if let (Some(p), Some(q)) = (actual, expected) {
                assert_eq!(export_point(p).into_affine(), q);
                assert!(q.is_on_curve());
                assert_eq!(
                    curve_g1::field::is_valid_subgroup_point(p),
                    q.is_in_correct_subgroup_assuming_on_curve()
                );
            }
        }
    }
    // Recovery accepts full-curve torsion; subgroup policy is intentionally separate.
    let torsion = curve_g1::field::from_x(Fp::constant(0), false).unwrap();
    assert!(curve_g1::field::is_on_curve(torsion));
    assert!(!curve_g1::field::is_valid_subgroup_point(torsion));
}

#[test]
fn rfc9380_published_g1_coordinates() {
    // These test the RFC's published points, not the message-to-point algorithms.
    let table = include_str!("../../test-vectors/rfc9380/g1-points.tsv");
    let mut total = 0;
    let mut final_points = 0;
    let mut published = std::collections::BTreeMap::new();
    for line in table.lines().filter(|line| !line.starts_with('#')) {
        let columns: Vec<_> = line.split('\t').collect();
        assert_eq!(columns.len(), 5);
        let coordinate = |s: &str| {
            assert_eq!(s.len(), 96);
            let bytes: Vec<u8> = (0..96)
                .step_by(2)
                .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
                .collect();
            let value = Fq::from_be_bytes_mod_order(&bytes);
            assert_eq!(
                value.into_bigint().to_bytes_be(),
                bytes,
                "RFC coordinate must be canonical"
            );
            value
        };
        let point = G1Affine::new_unchecked(coordinate(columns[3]), coordinate(columns[4]));
        published.insert((columns[0], columns[1], columns[2]), point);
        let raw = import_point(point.into_group());
        assert!(
            point.is_on_curve(),
            "{} case {} {}",
            columns[0],
            columns[1],
            columns[2]
        );
        assert!(curve_g1::field::is_on_curve(raw));
        assert_eq!(
            curve_g1::field::in_subgroup(raw),
            point.is_in_correct_subgroup_assuming_on_curve()
        );
        if columns[2] == "P" {
            assert!(curve_g1::field::is_valid_public_key_point(raw));
            final_points += 1;
        }
        let encoded = curve_g1::field::compress(raw);
        assert_eq!(encoded, ark_eth_bridge::encode_g1(&point).unwrap());
        let recovered = curve_g1::field::from_x(raw.x, encoded[0] & 0x20 != 0).unwrap();
        assert_eq!(export_point(recovered).into_affine(), point);
        total += 1;
    }
    assert_eq!((total, final_points), (25, 10));
    let mut operation_cases = 0;
    for section in ["J.9.1", "J.9.2"] {
        for case in 0..5 {
            let case = case.to_string();
            let expected = published[&(section, case.as_str(), "P")];
            let (raw, reference) = if section == "J.9.1" {
                let q0 = published[&(section, case.as_str(), "Q0")].into_group();
                let q1 = published[&(section, case.as_str(), "Q1")].into_group();
                (curve_g1::add(import_point(q0), import_point(q1)), q0 + q1)
            } else {
                let q = published[&(section, case.as_str(), "Q")].into_group();
                (import_point(q), q)
            };
            let actual = curve_g1::field::clear_cofactor(raw);
            assert_eq!(export_point(actual).into_affine(), expected);
            assert_eq!(
                reference
                    .into_affine()
                    .mul_bigint([0xd201000000010001])
                    .into_affine(),
                expected
            );
            assert_eq!(reference.into_affine().clear_cofactor(), expected);
            operation_cases += 1;
        }
    }
    assert_eq!(operation_cases, 10);
    let zero = curve_g1::field::clear_cofactor(curve_g1::identity::<Fp>());
    assert!(zero.z.is_zero());
}

#[test]
fn source_glv_projective_coordinates_and_scalar_reduction() {
    use ark_bls12_381::g1::Config;
    use ark_ec::short_weierstrass::SWCurveConfig;
    let generator = G1Affine::generator().into_group();
    let points = [
        generator,
        scaled(generator, Fq::from(7u64)),
        G1Projective::ZERO,
        G1Projective {
            x: Fq::from(13u64),
            y: Fq::from(7u64),
            z: Fq::from(0u64),
        },
        G1Projective {
            x: Fq::from(3u64),
            y: Fq::from(7u64),
            z: Fq::from(2u64),
        },
        G1Projective {
            x: Fq::from(0u64),
            y: Fq::from(2u64),
            z: Fq::from(1u64),
        },
    ];
    let order = Fr::MODULUS.0;
    let mut below = order;
    below[0] -= 1;
    let mut above = order;
    above[0] += 1;
    let mut scalars = vec![[0; 4], [1, 0, 0, 0], below, order, above, [u64::MAX; 4]];
    let mut state = 0x381_61_05u64;
    for _ in 0..64 {
        scalars.push([
            next(&mut state),
            next(&mut state),
            next(&mut state),
            next(&mut state),
        ]);
    }
    for scalar in scalars {
        let bytes: Vec<_> = scalar.iter().flat_map(|word| word.to_le_bytes()).collect();
        let reduced = Fr::from_le_bytes_mod_order(&bytes);
        assert_eq!(
            curve_g1::glv::reduce_scalar(scalar),
            reduced.into_bigint().0
        );
        for point in points {
            let expected = <Config as SWCurveConfig>::mul_projective(&point, &scalar);
            let actual = curve_g1::field::mul_256_concrete(import_point(point), scalar);
            assert_montgomery_coordinates(actual, expected);
        }
    }
}

#[test]
fn source_affine_integer_multiplication_coordinates() {
    let mut scalars = vec![[0; 4], [1, 0, 0, 0], [2, 0, 0, 0], [3, 0, 0, 0],
        [0xd201000000010000, 0, 0, 0], [0xd201000000010001, 0, 0, 0],
        Fr::MODULUS.0, [u64::MAX; 4]];
    let mut state = 0x992af681ccb2u64;
    for _ in 0..32 {
        scalars.push([next(&mut state), next(&mut state), next(&mut state), next(&mut state)]);
    }
    let points = [G1Affine::generator(), G1Affine::zero(),
        G1Affine { x: Fq::from(4), y: Fq::from(7), infinity: true },
        G1Affine::new_unchecked(Fq::from(4), Fq::from(7)),
        G1Affine::new_unchecked(Fq::from(0), Fq::from(2)),
        (G1Affine::generator().into_group() + G1Affine::new_unchecked(Fq::from(0), Fq::from(2))).into_affine()];
    for p in points {
        for scalar in &scalars {
            let actual = curve_g1::scalar::mul_affine(curve_g1::AffinePoint {
                x: import_field(p.x), y: import_field(p.y), infinity: p.infinity,
            }, *scalar);
            assert_montgomery_coordinates(actual, p.mul_bigint(*scalar));
        }
    }
}

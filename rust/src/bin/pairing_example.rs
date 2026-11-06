//! Executable pairing example and EIP-2537 vector adapter; outside extraction.
use ark_bls12_381::{Bls12_381, Fq, Fq2, G1Affine, G2Affine};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{BigInt, BigInteger, One, PrimeField};
use curve_g1::Field;
use std::io::{self, BufRead};
#[allow(dead_code)] // The shared test adapter also exposes exports used by other runners.
#[path = "../curve_support.rs"]
mod support;

fn unhex(s: &str) -> Option<Vec<u8>> {
    if !s.is_ascii() || s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}
fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
fn fp(b: &[u8]) -> Option<Fq> {
    if b.len() != 64 || b[..16].iter().any(|v| *v != 0) {
        return None;
    }
    let limbs =
        core::array::from_fn(|i| u64::from_be_bytes(b[56 - i * 8..64 - i * 8].try_into().unwrap()));
    Fq::from_bigint(BigInt(limbs))
}
fn g1(b: &[u8]) -> Option<G1Affine> {
    if b.len() != 128 {
        return None;
    }
    if b.iter().all(|x| *x == 0) {
        return Some(G1Affine::identity());
    }
    let p = G1Affine::new_unchecked(fp(&b[..64])?, fp(&b[64..])?);
    (p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve()).then_some(p)
}
fn g2(b: &[u8]) -> Option<G2Affine> {
    if b.len() != 256 {
        return None;
    }
    if b.iter().all(|x| *x == 0) {
        return Some(G2Affine::identity());
    }
    let p = G2Affine::new_unchecked(
        Fq2::new(fp(&b[..64])?, fp(&b[64..128])?),
        Fq2::new(fp(&b[128..192])?, fp(&b[192..])?),
    );
    (p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve()).then_some(p)
}
fn check(pairs: &[(G1Affine, G2Affine)]) -> bool {
    use curve_g1::pairing::{self, Fp2, G2};
    let mut raw_pairs = Vec::new();
    for (p, q) in pairs {
        let q = q.into_group();
        let lift = |x: Fq2| Fp2 {
            c0: support::import_field(x.c0),
            c1: support::import_field(x.c1),
        };
        let raw_q = G2 {
            x: lift(q.x),
            y: lift(q.y),
            z: lift(q.z),
        };
        raw_pairs.push((support::import_point(p.into_group()), raw_q));
    }
    let minimal = pairing::pairing_check(&raw_pairs);
    let arkworks = Bls12_381::multi_pairing(pairs.iter().map(|p| p.0), pairs.iter().map(|p| p.1))
        .0
        .is_one();
    assert_eq!(minimal, arkworks, "minimal pairing differs from arkworks");
    minimal
}
fn encode_g1(p: G1Affine) -> Vec<u8> {
    if p.is_zero() {
        return vec![0; 128];
    }
    let mut out = vec![0; 16];
    out.extend(p.x.into_bigint().to_bytes_be());
    out.extend([0; 16]);
    out.extend(p.y.into_bigint().to_bytes_be());
    out
}
fn run(line: &str) -> Option<String> {
    let (op, data) = line.split_once('\t')?;
    let b = unhex(data)?;
    match op {
        "pair" => {
            if b.is_empty() || b.len() % 384 != 0 {
                return None;
            }
            let pairs: Option<Vec<_>> = b
                .chunks_exact(384)
                .map(|b| Some((g1(&b[..128])?, g2(&b[128..])?)))
                .collect();
            Some(format!("pair\t{}", check(&pairs?)))
        }
        "mul" if b.len() == 160 => {
            let p = g1(&b[..128])?;
            let k = core::array::from_fn::<_, 4, _>(|i| {
                u64::from_be_bytes(b[152 - i * 8..160 - i * 8].try_into().unwrap())
            });
            let actual = curve_g1::mul_256(support::import_point(p.into_group()), k);
            let actual_bytes = if actual.z.is_zero() {
                vec![0; 128]
            } else {
                let (x, y) = curve_g1::field::to_affine(actual);
                let mut out = vec![0; 16];
                out.extend(x.to_bytes_be());
                out.extend([0; 16]);
                out.extend(y.to_bytes_be());
                out
            };
            Some(format!(
                "mul\t{}\t{}",
                hex(&actual_bytes),
                hex(&encode_g1(p.mul_bigint(k).into_affine()))
            ))
        }
        _ => None,
    }
}
fn demo() {
    let p = G1Affine::generator();
    let q = G2Affine::generator();
    let p2 = p.mul_bigint([2]).into_affine();
    let q3 = q.mul_bigint([3]).into_affine();
    let p6 = p.mul_bigint([6]).into_affine();
    let p5 = p.mul_bigint([5]).into_affine();
    for (name, pairs) in [
        ("cancellation", vec![(p, q), (-p, q)]),
        ("non_degeneracy", vec![(p, q)]),
        ("bilinearity", vec![(p2, q3), (-p6, q)]),
        ("wrong_scalar", vec![(p2, q3), (-p5, q)]),
        (
            "identity",
            vec![(G1Affine::identity(), q), (p, G2Affine::identity())],
        ),
    ] {
        println!("{name}\t{}", check(&pairs));
    }
}
fn run_main() -> io::Result<()> {
    if std::env::args().any(|a| a == "--demo") {
        demo();
        return Ok(());
    }
    for line in io::stdin().lock().lines() {
        println!("{}", run(&line?).unwrap_or_else(|| "invalid".into()));
    }
    Ok(())
}

fn main() -> io::Result<()> {
    // Recursive arithmetic runs on a dedicated stack.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(run_main)?
        .join()
        .expect("pairing worker panicked")
}

//! Compare concrete minimal operations with arkworks; adapters are outside extraction.
#[path = "../curve_support.rs"]
mod support;

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use std::io::{self, BufRead};
use support::*;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn run(line: &str) -> Option<String> {
    let args: Vec<_> = line.split('\t').collect();
    let n = args.get(1)?.parse::<u64>().ok()?;
    let p = G1Affine::generator()
        .mul_bigint([n])
        .into_affine()
        .into_group();
    let mp = import_point(p);
    let (actual, expected) = match args.as_slice() {
        ["neg", _] => (curve_g1::negate(mp), -p),
        ["double", _] => (curve_g1::double(mp), p + p),
        ["add", _, m] => {
            let q = G1Affine::generator()
                .mul_bigint([m.parse::<u64>().ok()?])
                .into_affine()
                .into_group();
            (curve_g1::add(mp, import_point(q)), p + q)
        }
        ["mul", _, k] => {
            let k = k.parse::<u64>().ok()?;
            (curve_g1::mul_u64(mp, k), p.into_affine().mul_bigint([k]))
        }
        ["mul256", _, k] if k.is_ascii() && k.len() == 64 => {
            let mut scalar = [0u64; 4];
            for (i, limb) in scalar.iter_mut().enumerate() {
                *limb = u64::from_str_radix(&k[(3 - i) * 16..(4 - i) * 16], 16).ok()?;
            }
            (
                curve_g1::mul_256(mp, scalar),
                p.into_affine().mul_bigint(scalar),
            )
        }
        _ => return None,
    };
    let point = export_point(actual);
    let affine = point.into_affine();
    assert!(affine.is_on_curve());
    let actual_bytes = curve_g1::field::compress(actual);
    let expected_bytes = ark_eth_bridge::encode_g1(&expected.into_affine()).ok()?;
    Some(format!(
        "ok\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        hex(&actual_bytes),
        hex(&expected_bytes),
        hex(&point.x.into_bigint().to_bytes_be()),
        hex(&point.y.into_bigint().to_bytes_be()),
        hex(&point.z.into_bigint().to_bytes_be()),
        hex(&expected.x.into_bigint().to_bytes_be()),
        hex(&expected.y.into_bigint().to_bytes_be()),
        hex(&expected.z.into_bigint().to_bytes_be())
    ))
}

fn main() -> io::Result<()> {
    for line in io::stdin().lock().lines() {
        println!("{}", run(&line?).unwrap_or_else(|| "invalid".into()));
    }
    Ok(())
}

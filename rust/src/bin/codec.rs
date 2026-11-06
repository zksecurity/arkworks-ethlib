//! Line-oriented differential-test runner. This binary is outside the extraction root.
use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_eth_bridge::encode_g1;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalDeserialize;
use std::io::{self, BufRead};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    if !s.is_ascii() || s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

fn encode_scalar(s: &str, minimal: bool) -> Option<String> {
    let n = s.parse::<u64>().ok()?;
    let p = G1Affine::generator().mul_bigint([n]).into_affine();
    let bytes = if minimal {
        minimal_g1::compress_g1(
            p.x.into_bigint().to_bytes_be().try_into().ok()?,
            p.y > -p.y,
            p.is_zero(),
        )
    } else {
        encode_g1(&p).ok()?
    };
    let (x, y) = if p.is_zero() {
        (vec![0; 48], vec![0; 48])
    } else {
        (
            p.x.into_bigint().to_bytes_be(),
            p.y.into_bigint().to_bytes_be(),
        )
    };
    Some(format!("ok\t{}\t{}\t{}", hex(&x), hex(&y), hex(&bytes)))
}

fn decode(s: &str) -> Option<String> {
    let bytes = unhex(s)?;
    // arkworks itself is a stream parser; this wrapper enforces exact framing.
    if bytes.len() != 48 {
        return None;
    }
    let p = G1Affine::deserialize_compressed(bytes.as_slice()).ok()?;
    Some(format!("ok\t{}", hex(&encode_g1(&p).ok()?)))
}

fn decode_minimal(s: &str) -> Option<String> {
    let bytes = unhex(s)?;
    let p = curve_g1::decoder::decode_g1(&bytes)?;
    Some(format!("ok\t{}", hex(&curve_g1::field::compress(p))))
}

fn main() -> io::Result<()> {
    for line in io::stdin().lock().lines() {
        let line = line?;
        let result = line.split_once('\t').and_then(|(op, arg)| match op {
            "encode" => encode_scalar(arg, false),
            "encode_minimal" => encode_scalar(arg, true),
            "decode" => decode(arg),
            "decode_minimal" => decode_minimal(arg),
            _ => None,
        });
        println!("{}", result.unwrap_or_else(|| "invalid".into()));
    }
    Ok(())
}

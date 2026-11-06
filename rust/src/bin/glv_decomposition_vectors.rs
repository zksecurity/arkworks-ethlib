//! Actual pinned arkworks results for the Lean GLV arithmetic cross-check.
use ark_bls12_381::{g1::Config, Fr};
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ff::PrimeField;
use std::io::{self, BufRead};
use std::str::FromStr;

fn magnitude(k: Fr) -> String {
    k.into_bigint()
        .0
        .iter()
        .rev()
        .map(|word| format!("{word:016x}"))
        .collect()
}

fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.expect("scalar input");
        let k = Fr::from_str(&line).expect("canonical decimal scalar");
        let ((positive1, k1), (positive2, k2)) = Config::scalar_decomposition(k);
        let (minimal1, minimal2) = curve_g1::glv::scalar_decomposition(k.into_bigint().0)
            .expect("canonical scalar accepted");
        assert_eq!(minimal1.positive, positive1);
        assert_eq!(minimal2.positive, positive2);
        assert_eq!(minimal1.magnitude, k1.into_bigint().0);
        assert_eq!(minimal2.magnitude, k2.into_bigint().0);
        println!(
            "{}\t{}\t{}\t{}\t{}",
            line,
            positive1,
            magnitude(k1),
            positive2,
            magnitude(k2)
        );
    }
}

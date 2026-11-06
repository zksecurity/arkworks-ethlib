//! Test-only representation bridge. No curve arithmetic is delegated to arkworks here.
use ark_bls12_381::{Fq, G1Projective};
use ark_ff::{BigInt, PrimeField};
use curve_g1::{field::Fp, Point};

pub fn import_field(x: Fq) -> Fp {
    Fp::from_limbs(x.into_bigint().0).expect("arkworks field is canonical")
}

pub fn export_field(x: Fp) -> Fq {
    Fq::from_bigint(BigInt(x.to_limbs())).expect("minimal field output must be canonical")
}

pub fn import_point(p: G1Projective) -> Point<Fp> {
    Point {
        x: import_field(p.x),
        y: import_field(p.y),
        z: import_field(p.z),
    }
}

pub fn export_point(p: Point<Fp>) -> G1Projective {
    G1Projective::new_unchecked(export_field(p.x), export_field(p.y), export_field(p.z))
}

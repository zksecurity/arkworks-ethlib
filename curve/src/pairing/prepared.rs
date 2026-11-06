//! Source-specialized BLS12-381 M-twist prepared line steps from ark-ec.
use super::{Fp12, Fp2};
use crate::field::{Fp, G2_COEFF_B_COMPONENT};
use crate::Field;
use alloc::vec::Vec;

pub const COEFF_B: Fp2 = Fp2 {
    c0: G2_COEFF_B_COMPONENT,
    c1: G2_COEFF_B_COMPONENT,
};

/// Homogeneous coordinates: x/z and y/z, as used by arkworks' preparation.
#[derive(Clone, Copy)]
pub struct HomG2 {
    pub x: Fp2,
    pub y: Fp2,
    pub z: Fp2,
}

/// The three line coefficients in the M-twist order returned by arkworks.
#[derive(Clone, Copy)]
pub struct LineCoeff {
    pub c0: Fp2,
    pub c1: Fp2,
    pub c2: Fp2,
}

impl HomG2 {
    pub fn double(self, two_inv: Fp) -> (Self, LineCoeff) {
        let a = self.x.times(self.y).mul_by_fp(two_inv);
        let b = self.y.square();
        let c = self.z.square();
        let e = COEFF_B.times(c.plus(c).plus(c));
        let f = e.plus(e).plus(e);
        let g = b.plus(f).mul_by_fp(two_inv);
        let h = self.y.plus(self.z).square().minus(b.plus(c));
        let i = e.minus(b);
        let j = self.x.square();
        let e_square = e.square();
        let x = a.times(b.minus(f));
        let y = g.square().minus(e_square.plus(e_square).plus(e_square));
        let z = b.times(h);
        (
            Self { x, y, z },
            LineCoeff {
                c0: i,
                c1: j.plus(j).plus(j),
                c2: h.negative(),
            },
        )
    }

    /// The caller supplies the coordinates of the non-infinity affine addend.
    pub fn add(self, qx: Fp2, qy: Fp2) -> (Self, LineCoeff) {
        let theta = self.y.minus(qy.times(self.z));
        let lambda = self.x.minus(qx.times(self.z));
        let c = theta.square();
        let d = lambda.square();
        let e = lambda.times(d);
        let f = self.z.times(c);
        let g = self.x.times(d);
        let h = e.plus(f).minus(g.plus(g));
        let x = lambda.times(h);
        let y = theta.times(g.minus(h)).minus(e.times(self.y));
        let z = self.z.times(e);
        let j = theta.times(qx).minus(lambda.times(qy));
        (
            Self { x, y, z },
            LineCoeff {
                c0: j,
                c1: theta.negative(),
                c2: lambda,
            },
        )
    }
}

/// ark-ec's M-twist line evaluation, preserving its scalar-product order.
pub fn ell(f: Fp12, coeff: LineCoeff, px: Fp, py: Fp) -> Fp12 {
    let c2 = coeff.c2.mul_by_fp(py);
    let c1 = coeff.c1.mul_by_fp(px);
    f.mul_by_014(coeff.c0, c1, c2)
}

/// Arkworks' affine preparation result, retaining its coefficient vector.
pub struct PreparedG2 {
    pub ell_coeffs: Vec<LineCoeff>,
    pub infinity: bool,
}

fn prepare_bits(
    qx: Fp2,
    qy: Fp2,
    two_inv: Fp,
    state: HomG2,
    mut coeffs: Vec<LineCoeff>,
    bits: u32,
) -> Vec<LineCoeff> {
    if bits == 0 {
        return coeffs;
    }
    let bit = bits - 1;
    let (state, line) = state.double(two_inv);
    coeffs.push(line);
    let state = if (super::BLS_X >> bit) & 1 == 1 {
        let (state, line) = state.add(qx, qy);
        coeffs.push(line);
        state
    } else {
        state
    };
    prepare_bits(qx, qy, two_inv, state, coeffs, bit)
}

/// Specialization of G2Prepared::from(G2Affine) for the fixed negative BLS parameter.
/// As upstream, two_inv is computed even for an infinity input.
pub fn prepare_affine(qx: Fp2, qy: Fp2, infinity: bool) -> PreparedG2 {
    let one = crate::field::FROBENIUS_FP2_C1[0];
    let two_inv = one.plus(one).inverse();
    if infinity {
        return PreparedG2 {
            ell_coeffs: Vec::new(),
            infinity: true,
        };
    }
    let state = HomG2 {
        x: qx,
        y: qy,
        z: Fp2 {
            c0: one,
            c1: Fp::constant(0),
        },
    };
    PreparedG2 {
        ell_coeffs: prepare_bits(qx, qy, two_inv, state, Vec::new(), 63),
        infinity: false,
    }
}

/// ark-ec's G1Prepared::from(Projective), including the normalized-Z shortcut.
pub fn prepare_g1(p: crate::Point<Fp>) -> crate::AffinePoint<Fp> {
    crate::scalar::normalize(p)
}

#[derive(Clone, Copy)]
pub struct AffineG2 {
    pub x: Fp2,
    pub y: Fp2,
    pub infinity: bool,
}

/// Precomputed quadratic identity; there is no nonzero integer conversion product.
pub fn one_fp2() -> Fp2 {
    Fp2 {
        c0: crate::field::FROBENIUS_FP2_C1[0],
        c1: Fp::constant(0),
    }
}

/// The same projective-to-affine schedule over Fp2, used by G2Prepared::from.
pub fn normalize_g2(p: super::G2) -> AffineG2 {
    if p.z.is_zero() {
        return AffineG2 {
            x: Fp2::zero(),
            y: Fp2::zero(),
            infinity: true,
        };
    }
    if p.z.equal(one_fp2()) {
        return AffineG2 {
            x: p.x,
            y: p.y,
            infinity: false,
        };
    }
    let zi = p.z.inverse();
    let zi2 = zi.square();
    let x = p.x.times(zi2);
    let y = p.y.times(zi2.times(zi));
    AffineG2 {
        x,
        y,
        infinity: false,
    }
}

/// ark-ec's projective G2 preparation: normalize, then prepare the affine point.
pub fn prepare_g2(p: super::G2) -> PreparedG2 {
    let q = normalize_g2(p);
    prepare_affine(q.x, q.y, q.infinity)
}

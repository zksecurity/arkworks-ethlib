//! Source affine double-and-add for full-curve integer multiplication.
use crate::{field::Fp, AffinePoint, Field, Point};

fn affine_loop(
    base: AffinePoint<Fp>,
    k: [u64; 4],
    bits: u32,
    started: bool,
    res: Point<Fp>,
) -> Point<Fp> {
    if bits == 0 {
        return res;
    }
    let bit = bits - 1;
    let set = crate::glv::scalar_bit(k, bit);
    if !started && !set {
        return affine_loop(base, k, bit, false, res);
    }
    let res = crate::double(res);
    let res = if set { crate::add_affine(res, base) } else { res };
    affine_loop(base, k, bit, true, res)
}

/// ark-ec 0.5.0 `sw_double_and_add_affine`, with a fixed four-word iterator.
/// Leading zero bits perform no field operations; the scalar is not reduced modulo r.
pub fn mul_affine(base: AffinePoint<Fp>, k: [u64; 4]) -> Point<Fp> {
    affine_loop(base, k, 256, false, crate::identity())
}

/// ark-ec's projective-to-affine conversion, shared by curve and pairing callers.
pub fn normalize(p: Point<Fp>) -> AffinePoint<Fp> {
    if p.z.is_zero() {
        return crate::AffinePoint {
            x: Fp::constant(0),
            y: Fp::constant(0),
            infinity: true,
        };
    }
    if p.z.equal(crate::field::FROBENIUS_FP2_C1[0]) {
        return crate::AffinePoint {
            x: p.x,
            y: p.y,
            infinity: false,
        };
    }
    let zi = p.z.inverse();
    let zi2 = zi.square();
    let x = p.x.times(zi2);
    let y = p.y.times(zi2.times(zi));
    crate::AffinePoint {
        x,
        y,
        infinity: false,
    }
}

/// ark-ec's affine-to-projective conversion, including its canonical infinity.
pub fn projective_from_affine(p: AffinePoint<Fp>) -> Point<Fp> {
    if p.infinity {
        crate::identity()
    } else {
        Point { x: p.x, y: p.y, z: Fp::constant(1) }
    }
}

pub fn normalize_projective(p: Point<Fp>) -> Point<Fp> {
    projective_from_affine(normalize(p))
}

/// Source effective-cofactor path: affine integer multiplication and affine conversion.
pub fn clear_cofactor_projective(p: Point<Fp>) -> Point<Fp> {
    let base = normalize(p);
    let multiple = mul_affine(base, [0xd201000000010001, 0, 0, 0]);
    normalize_projective(multiple)
}

/// ark-ec projective equality, retaining the source multiplication grouping.
pub fn points_equal(p: Point<Fp>, q: Point<Fp>) -> bool {
    if p.z.is_zero() {
        return q.z.is_zero();
    }
    if q.z.is_zero() {
        return false;
    }
    let z1sq = p.z.square();
    let z2sq = q.z.square();
    p.x.times(z2sq).equal(q.x.times(z1sq))
        && p.y.times(z2sq.times(q.z)).equal(q.y.times(z1sq.times(p.z)))
}

/// The source BLS12-381 fast subgroup algorithm on a normalized affine input.
/// The caller must establish the curve equation before calling this function.
pub fn in_subgroup(p: Point<Fp>) -> bool {
    let affine = normalize(p);
    let base = projective_from_affine(affine);
    let x_times_p = mul_affine(affine, [0xd201000000010000, 0, 0, 0]);
    if points_equal(x_times_p, base) && !affine.infinity {
        return false;
    }
    let minus_x_squared_times_p = crate::negate(crate::glv::mul_projective(
        x_times_p, [0xd201000000010000, 0, 0, 0],
    ));
    let endomorphism_p = projective_from_affine(crate::glv::endomorphism_affine(affine));
    points_equal(minus_x_squared_times_p, endomorphism_p)
}

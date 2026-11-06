#![no_std]

//! Small, variable-time BLS12-381 G1 reference implementation.
//! Intended for extraction and verification experiments, not secret-key use.
//! Points use Jacobian coordinates; callers are responsible for curve/subgroup validity.
extern crate alloc;

pub mod alternative;
pub mod decoder;
pub mod field;
pub mod glv;
pub mod montgomery;
pub mod optimized;
pub mod pairing;
pub mod scalar;

/// The exact field boundary used by the extracted point formulas.
pub trait Field: Copy {
    fn constant(n: u32) -> Self;
    fn plus(self, rhs: Self) -> Self;
    fn minus(self, rhs: Self) -> Self;
    fn times(self, rhs: Self) -> Self;
    fn square(self) -> Self;
    fn sum_products(a: Self, b: Self, c: Self, d: Self) -> Self;
    fn negative(self) -> Self;
    fn equal(self, rhs: Self) -> bool;
    fn is_zero(self) -> bool;
}

#[derive(Clone, Copy)]
pub struct Point<F: Field> {
    pub x: F,
    pub y: F,
    pub z: F,
}

/// ark-ec's affine representation, specialized to this field interface.
#[derive(Clone, Copy)]
pub struct AffinePoint<F: Field> {
    pub x: F,
    pub y: F,
    pub infinity: bool,
}

pub fn identity<F: Field>() -> Point<F> {
    Point {
        x: F::constant(1),
        y: F::constant(1),
        z: F::constant(0),
    }
}

pub fn negate<F: Field>(p: Point<F>) -> Point<F> {
    Point {
        x: p.x,
        y: p.y.negative(),
        z: p.z,
    }
}

/// ark-ec 0.5.0 `Projective::double_in_place`, specialized to BLS12-381 G1.
/// Source mapping and remaining representation differences: docs/arkworks-alignment.md.
pub fn double<F: Field>(p: Point<F>) -> Point<F> {
    if p.z.is_zero() {
        return p;
    }
    let a = p.x.square();
    let b = p.y.square();
    let c = b.square();
    let d = p.x.times(b);
    let d = d.plus(d);
    let d = d.plus(d);
    let e = a.plus(a.plus(a));
    let z = p.z.times(p.y);
    let z = z.plus(z);
    let f = e.square();
    let x = f.minus(d.plus(d));
    let c2 = c.plus(c);
    let c4 = c2.plus(c2);
    let y = d.minus(x).times(e).minus(c4.plus(c4));
    Point { x, y, z }
}

/// Complete branch handling: either identity, equal points, and opposites.
pub fn add<F: Field>(p: Point<F>, q: Point<F>) -> Point<F> {
    if p.z.is_zero() {
        return q;
    }
    if q.z.is_zero() {
        return p;
    }
    add_general(p, q)
}

/// ark-ec 0.5.0 projective AddAssign polynomial schedule (see alignment ledger).
fn add_general<F: Field>(p: Point<F>, q: Point<F>) -> Point<F> {
    let z1z1 = p.z.square();
    let z2z2 = q.z.square();
    let u1 = p.x.times(z2z2);
    let u2 = q.x.times(z1z1);
    let s1 = p.y.times(q.z).times(z2z2);
    let s2 = q.y.times(p.z).times(z1z1);
    if u1.equal(u2) {
        return if s1.equal(s2) { double(p) } else { identity() };
    }
    let h = u2.minus(u1);
    let two_h = h.plus(h);
    let i = two_h.square();
    let j = h.negative().times(i);
    let delta = s2.minus(s1);
    let r = delta.plus(delta);
    let v = u1.times(i);
    let x = r.square().plus(j).minus(v.plus(v));
    let y = F::sum_products(r, v.minus(x), s1.plus(s1), j);
    let z = p.z.times(q.z);
    let z = z.plus(z).times(h);
    Point { x, y, z }
}

/// ark-ec 0.5.0 affine AddAssign identity handling and mixed-addition path.
pub fn add_affine<F: Field>(p: Point<F>, q: AffinePoint<F>) -> Point<F> {
    if q.infinity {
        return p;
    }
    if p.z.is_zero() {
        return Point {
            x: q.x,
            y: q.y,
            z: F::constant(1),
        };
    }
    add_mixed(p, q)
}

/// ark-ec 0.5.0 affine AddAssign polynomial schedule (see alignment ledger).
fn add_mixed<F: Field>(p: Point<F>, q: AffinePoint<F>) -> Point<F> {
    let z1z1 = p.z.square();
    let u2 = q.x.times(z1z1);
    let s2 = p.z.times(q.y).times(z1z1);
    if p.x.equal(u2) {
        return if p.y.equal(s2) { double(p) } else { identity() };
    }
    let h = u2.minus(p.x);
    let hh = h.square();
    let i = hh.plus(hh);
    let i = i.plus(i);
    let j = h.negative().times(i);
    let delta = s2.minus(p.y);
    let r = delta.plus(delta);
    let v = p.x.times(i);
    let x = r.square().plus(j).minus(v.plus(v));
    let y = F::sum_products(r, v.minus(x), p.y.plus(p.y), j);
    let z = p.z.times(h);
    let z = z.plus(z);
    Point { x, y, z }
}

/// Full-curve integer multiplication through ark-ec's affine scalar schedule.
pub fn mul_u64(p: Point<field::Fp>, k: u64) -> Point<field::Fp> {
    scalar::mul_affine(scalar::normalize(p), [k, 0, 0, 0])
}

/// Full 256-bit unsigned integer action; projective GLV is `field::mul_256_concrete`.
pub fn mul_256(p: Point<field::Fp>, k: [u64; 4]) -> Point<field::Fp> {
    scalar::mul_affine(scalar::normalize(p), k)
}

//! Minimal, variable-time BLS12-381 pairing arithmetic over the proved Fp backend.
//! Reference implementation: not suitable for secret-dependent inputs.
use crate::{field::Fp, Field};

pub mod prepared;
pub mod prepared_miller;

#[derive(Clone, Copy)]
pub struct Fp2 {
    pub c0: Fp,
    pub c1: Fp,
}
impl Fp2 {
    pub fn zero() -> Self {
        Self::of_fp(Fp::constant(0))
    }
    pub fn one() -> Self {
        Self::of_fp(Fp::constant(1))
    }
    pub fn of_fp(x: Fp) -> Self {
        Self {
            c0: x,
            c1: Fp::constant(0),
        }
    }
    pub fn plus(self, b: Self) -> Self {
        Self {
            c0: self.c0.plus(b.c0),
            c1: self.c1.plus(b.c1),
        }
    }
    pub fn minus(self, b: Self) -> Self {
        Self {
            c0: self.c0.minus(b.c0),
            c1: self.c1.minus(b.c1),
        }
    }
    pub fn negative(self) -> Self {
        Self {
            c0: self.c0.negative(),
            c1: self.c1.negative(),
        }
    }
    /// ark-ff's scalar multiplication of a quadratic-extension coefficient.
    pub fn mul_by_fp(self, b: Fp) -> Self {
        Self {
            c0: self.c0.times(b),
            c1: self.c1.times(b),
        }
    }
    /// ark-ff's degree-two quadratic-extension path, with nonresidue -1.
    pub fn times(self, b: Self) -> Self {
        let neg_c1 = self.c1.negative();
        Self {
            c0: Fp::sum_products(self.c0, b.c0, neg_c1, b.c1),
            c1: Fp::sum_products(self.c0, b.c1, self.c1, b.c0),
        }
    }
    /// ark-ff's dedicated quadratic square for nonresidue -1.
    pub fn square(self) -> Self {
        let v0 = self.c0.minus(self.c1);
        let c0 = self.c0.plus(self.c1).times(v0);
        let c1 = self.c1.plus(self.c1).times(self.c0);
        Self { c0, c1 }
    }
    /// ark-ff quadratic Frobenius: base maps are identities; multiply c1 by the table entry.
    pub fn frobenius(self, power: usize) -> Self {
        let coefficient = crate::field::FROBENIUS_FP2_C1[power % 2];
        Self {
            c0: self.c0,
            c1: self.c1.times(coefficient),
        }
    }
    pub fn mul_xi(self) -> Self {
        Self {
            c0: self.c0.minus(self.c1),
            c1: self.c1.plus(self.c0),
        }
    }
    pub fn inverse(self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let v1 = self.c1.square();
        let norm = v1.plus(self.c0.square());
        let inv = norm.inverse();
        Self {
            c0: self.c0.times(inv),
            c1: self.c1.times(inv).negative(),
        }
    }
    pub fn equal(self, b: Self) -> bool {
        self.c0.equal(b.c0) && self.c1.equal(b.c1)
    }
    pub fn is_zero(self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }
}
#[derive(Clone, Copy)]
pub struct Fp6 {
    pub c0: Fp2,
    pub c1: Fp2,
    pub c2: Fp2,
}
impl Fp6 {
    pub fn zero() -> Self {
        Self {
            c0: Fp2::zero(),
            c1: Fp2::zero(),
            c2: Fp2::zero(),
        }
    }
    pub fn one() -> Self {
        Self::of_fp2(Fp2::one())
    }
    pub fn of_fp2(x: Fp2) -> Self {
        Self {
            c0: x,
            c1: Fp2::zero(),
            c2: Fp2::zero(),
        }
    }
    pub fn plus(self, b: Self) -> Self {
        Self {
            c0: self.c0.plus(b.c0),
            c1: self.c1.plus(b.c1),
            c2: self.c2.plus(b.c2),
        }
    }
    pub fn minus(self, b: Self) -> Self {
        Self {
            c0: self.c0.minus(b.c0),
            c1: self.c1.minus(b.c1),
            c2: self.c2.minus(b.c2),
        }
    }
    pub fn negative(self) -> Self {
        Self {
            c0: self.c0.negative(),
            c1: self.c1.negative(),
            c2: self.c2.negative(),
        }
    }
    /// ark-ff's cubic Karatsuba schedule, specialized to the Fp2 tower.
    pub fn times(self, b: Self) -> Self {
        let ad = self.c0.times(b.c0);
        let be = self.c1.times(b.c1);
        let cf = self.c2.times(b.c2);
        let x = self
            .c1
            .plus(self.c2)
            .times(b.c1.plus(b.c2))
            .minus(be)
            .minus(cf);
        let y = self
            .c0
            .plus(self.c1)
            .times(b.c0.plus(b.c1))
            .minus(ad)
            .minus(be);
        let z = self
            .c0
            .plus(self.c2)
            .times(b.c0.plus(b.c2))
            .minus(ad)
            .plus(be)
            .minus(cf);
        Self {
            c0: ad.plus(x.mul_xi()),
            c1: y.plus(cf.mul_xi()),
            c2: z,
        }
    }
    /// ark-ff's cubic CH-SQR2 schedule.
    pub fn square(self) -> Self {
        let s0 = self.c0.square();
        let ab = self.c0.times(self.c1);
        let s1 = ab.plus(ab);
        let v = self.c0.minus(self.c1).plus(self.c2);
        let s2 = v.square();
        let bc = self.c1.times(self.c2);
        let s3 = bc.plus(bc);
        let s4 = self.c2.square();
        Self {
            c0: s3.mul_xi().plus(s0),
            c1: s4.mul_xi().plus(s1),
            c2: s1.plus(s2).plus(s3).minus(s0).minus(s4),
        }
    }
    /// ark-ff's sparse cubic product by (0,c1,0).
    pub fn mul_by_1(self, c1: Fp2) -> Self {
        let bb = self.c1.times(c1);
        let t1 = c1.times(self.c1.plus(self.c2)).minus(bb).mul_xi();
        let t2 = c1.times(self.c0.plus(self.c1)).minus(bb);
        Self {
            c0: t1,
            c1: t2,
            c2: bb,
        }
    }
    /// ark-ff's sparse cubic product by (c0,c1,0).
    pub fn mul_by_01(self, c0: Fp2, c1: Fp2) -> Self {
        let aa = self.c0.times(c0);
        let bb = self.c1.times(c1);
        let t1 = c1.times(self.c1.plus(self.c2)).minus(bb).mul_xi().plus(aa);
        let t3 = c0.times(self.c0.plus(self.c2)).minus(aa).plus(bb);
        let t2 = c0.plus(c1).times(self.c0.plus(self.c1)).minus(aa).minus(bb);
        Self {
            c0: t1,
            c1: t2,
            c2: t3,
        }
    }
    /// ark-ff cubic Frobenius: map each coefficient, then multiply c1 and c2 by their table entries.
    pub fn frobenius(self, power: usize) -> Self {
        let c0 = self.c0.frobenius(power);
        let c1 = self.c1.frobenius(power);
        let c2 = self.c2.frobenius(power);
        let first = crate::field::FROBENIUS_FP6_C1[power % 6];
        let second = crate::field::FROBENIUS_FP6_C2[power % 6];
        Self {
            c0,
            c1: c1.times(Fp2 {
                c0: first[0],
                c1: first[1],
            }),
            c2: c2.times(Fp2 {
                c0: second[0],
                c1: second[1],
            }),
        }
    }
    pub fn mul_v(self) -> Self {
        Self {
            c0: self.c2.mul_xi(),
            c1: self.c0,
            c2: self.c1,
        }
    }
    pub fn inverse(self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let t0 = self.c0.square();
        let t1 = self.c1.square();
        let t2 = self.c2.square();
        let t3 = self.c0.times(self.c1);
        let t4 = self.c0.times(self.c2);
        let t5 = self.c1.times(self.c2);
        let n5 = t5.mul_xi();
        let s0 = t0.minus(n5);
        let s1 = t2.mul_xi().minus(t3);
        let s2 = t1.minus(t4);
        let a1 = self.c2.times(s1);
        let a2 = self.c1.times(s2);
        let a3 = a1.plus(a2).mul_xi();
        let inv = self.c0.times(s0).plus(a3).inverse();
        Self {
            c0: inv.times(s0),
            c1: inv.times(s1),
            c2: inv.times(s2),
        }
    }
    pub fn equal(self, b: Self) -> bool {
        self.c0.equal(b.c0) && self.c1.equal(b.c1) && self.c2.equal(b.c2)
    }
    pub fn is_zero(self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }
}
#[derive(Clone, Copy)]
pub struct Fp12 {
    pub c0: Fp6,
    pub c1: Fp6,
}
impl Fp12 {
    pub fn zero() -> Self {
        Self {
            c0: Fp6::zero(),
            c1: Fp6::zero(),
        }
    }
    pub fn one() -> Self {
        Self {
            c0: Fp6::one(),
            c1: Fp6::zero(),
        }
    }
    /// Precomputed arkworks ONE: initializing an exponent accumulator performs no products.
    pub fn cyclotomic_one() -> Self {
        Self {
            c0: Fp6 {
                c0: Fp2 {
                    c0: crate::field::FROBENIUS_FP2_C1[0],
                    c1: Fp::constant(0),
                },
                c1: Fp2::zero(),
                c2: Fp2::zero(),
            },
            c1: Fp6::zero(),
        }
    }
    /// ark-ff's fast-inverse NAF loop, specialized to the absolute BLS parameter.
    /// On non-cyclotomic inputs this retains the source algorithm, not ordinary powering.
    pub fn cyclotomic_exp_x_abs(self) -> Self {
        if self.is_zero() {
            return self;
        }
        cyclotomic_x_digits(self, self.conjugate(), Self::cyclotomic_one(), 65, false)
    }
    /// ark-ec's exp_by_x wrapper for the negative BLS12-381 parameter.
    pub fn exp_by_x(self) -> Self {
        self.cyclotomic_exp_x_abs().conjugate()
    }
    pub fn of_fp2(x: Fp2) -> Self {
        Self {
            c0: Fp6::of_fp2(x),
            c1: Fp6::zero(),
        }
    }
    pub fn plus(self, b: Self) -> Self {
        Self {
            c0: self.c0.plus(b.c0),
            c1: self.c1.plus(b.c1),
        }
    }
    pub fn minus(self, b: Self) -> Self {
        Self {
            c0: self.c0.minus(b.c0),
            c1: self.c1.minus(b.c1),
        }
    }
    pub fn negative(self) -> Self {
        Self {
            c0: self.c0.negative(),
            c1: self.c1.negative(),
        }
    }
    /// ark-ff's quadratic Karatsuba path over Fp6 (extension degree 12).
    pub fn times(self, b: Self) -> Self {
        let v0 = self.c0.times(b.c0);
        let v1 = self.c1.times(b.c1);
        let c1 = self
            .c1
            .plus(self.c0)
            .times(b.c0.plus(b.c1))
            .minus(v0)
            .minus(v1);
        let c0 = v1.mul_v().plus(v0);
        Self { c0, c1 }
    }
    /// ark-ff's complex square for the quadratic nonresidue v.
    pub fn square(self) -> Self {
        let v0 = self.c0.minus(self.c1);
        let v3 = self.c0.minus(self.c1.mul_v());
        let v2 = self.c0.times(self.c1);
        let v0 = v0.times(v3);
        let c1 = v2.plus(v2);
        let c0 = v2.mul_v().plus(v0).plus(v2);
        Self { c0, c1 }
    }
    /// ark-ff's sparse quadratic product used by BLS12-381's M-twist line evaluation.
    pub fn mul_by_014(self, c0: Fp2, c1: Fp2, c4: Fp2) -> Self {
        let aa = self.c0.mul_by_01(c0, c1);
        let bb = self.c1.mul_by_1(c4);
        let o = c1.plus(c4);
        let c1 = self.c1.plus(self.c0).mul_by_01(c0, o).minus(aa).minus(bb);
        let c0 = bb.mul_v().plus(aa);
        Self { c0, c1 }
    }
    pub fn is_zero(self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }
    pub fn inverse(self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let v1 = self.c1.square();
        let norm = self.c0.square().minus(v1.mul_v());
        let inv = norm.inverse();
        Self {
            c0: self.c0.times(inv),
            c1: self.c1.times(inv).negative(),
        }
    }
    /// ark-ff Granger–Scott square, specialized to the BLS12-381 characteristic.
    /// Correct as ordinary squaring on zero or cyclotomic inputs.
    pub fn cyclotomic_square(self) -> Self {
        let r0 = self.c0.c0;
        let r4 = self.c0.c1;
        let r3 = self.c0.c2;
        let r2 = self.c1.c0;
        let r1 = self.c1.c1;
        let r5 = self.c1.c2;
        let tmp = r0.times(r1);
        let t0 = r0
            .plus(r1)
            .times(r1.mul_xi().plus(r0))
            .minus(tmp)
            .minus(tmp.mul_xi());
        let t1 = tmp.plus(tmp);
        let tmp = r2.times(r3);
        let t2 = r2
            .plus(r3)
            .times(r3.mul_xi().plus(r2))
            .minus(tmp)
            .minus(tmp.mul_xi());
        let t3 = tmp.plus(tmp);
        let tmp = r4.times(r5);
        let t4 = r4
            .plus(r5)
            .times(r5.mul_xi().plus(r4))
            .minus(tmp)
            .minus(tmp.mul_xi());
        let t5 = tmp.plus(tmp);
        let z0 = t0.minus(r0);
        let z0 = z0.plus(z0).plus(t0);
        let z1 = t1.plus(r1);
        let z1 = z1.plus(z1).plus(t1);
        let tmp = t5.mul_xi();
        let z2 = r2.plus(tmp);
        let z2 = z2.plus(z2).plus(tmp);
        let z3 = t4.minus(r3);
        let z3 = z3.plus(z3).plus(t4);
        let z4 = t2.minus(r4);
        let z4 = z4.plus(z4).plus(t2);
        let z5 = r5.plus(t3);
        let z5 = z5.plus(z5).plus(t3);
        Self {
            c0: Fp6 {
                c0: z0,
                c1: z4,
                c2: z3,
            },
            c1: Fp6 {
                c0: z2,
                c1: z1,
                c2: z5,
            },
        }
    }
    /// ark-ff quadratic Frobenius with the Fp6-by-Fp2 coefficient multiplication.
    pub fn frobenius(self, power: usize) -> Self {
        let c0 = self.c0.frobenius(power);
        let c1 = self.c1.frobenius(power);
        let entry = crate::field::FROBENIUS_FP12_C1[power % 12];
        let coefficient = Fp2 {
            c0: entry[0],
            c1: entry[1],
        };
        Self {
            c0,
            c1: Fp6 {
                c0: c1.c0.times(coefficient),
                c1: c1.c1.times(coefficient),
                c2: c1.c2.times(coefficient),
            },
        }
    }
    pub fn conjugate(self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1.negative(),
        }
    }
    pub fn is_one(self) -> bool {
        self.c0.equal(Fp6::one()) && self.c1.is_zero()
    }
    pub fn equal(self, b: Self) -> bool {
        self.c0.equal(b.c0) && self.c1.equal(b.c1)
    }
}

#[derive(Clone, Copy)]
pub struct G2 {
    pub x: Fp2,
    pub y: Fp2,
    pub z: Fp2,
}
/// The absolute value of the negative BLS12-381 parameter.
pub const BLS_X: u64 = 0xd201000000010000;

/// Little-endian signed NAF digits returned by ark-ff's find_naf([BLS_X]).
pub const BLS_X_NAF: [i8; 65] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -1,
    0, 1,
];

fn cyclotomic_x_digits(base: Fp12, inverse: Fp12, acc: Fp12, remaining: u32, found: bool) -> Fp12 {
    if remaining == 0 {
        return acc;
    }
    let bit = remaining - 1;
    let digit = BLS_X_NAF[bit as usize];
    let acc = if found { acc.cyclotomic_square() } else { acc };
    let acc = if digit > 0 {
        acc.times(base)
    } else if digit < 0 {
        acc.times(inverse)
    } else {
        acc
    };
    cyclotomic_x_digits(base, inverse, acc, bit, found || digit != 0)
}

/// arkworks' easy final-exponent stages, with the total zero adapter retained.
pub fn final_exponentiation_easy(f: Fp12) -> Fp12 {
    let easy = f.conjugate().times(f.inverse());
    easy.frobenius(2).times(easy)
}

/// ark-ec's BLS12 hard chain, retaining its cubed final-exponent convention.
/// The caller must supply zero or a cyclotomic element from the easy stages.
pub fn final_exponentiation_hard(mut r: Fp12) -> Fp12 {
    let mut y0 = r.cyclotomic_square();
    let mut y1 = r.exp_by_x();
    let mut y2 = r.conjugate();
    y1 = y1.times(y2);
    y2 = y1.exp_by_x();
    y1 = y1.conjugate();
    y1 = y1.times(y2);
    y2 = y1.exp_by_x();
    y1 = y1.frobenius(1);
    y1 = y1.times(y2);
    r = r.times(y0);
    y0 = y1.exp_by_x();
    y2 = y0.exp_by_x();
    y0 = y1.frobenius(2);
    y1 = y1.conjugate();
    y1 = y1.times(y2);
    y1 = y1.times(y0);
    r.times(y1)
}

/// Source-scheduled arkworks final exponentiation, with zero replacing upstream None.
pub fn final_exponentiation(f: Fp12) -> Fp12 {
    if f.is_zero() {
        return f;
    }
    final_exponentiation_hard(final_exponentiation_easy(f))
}

/// Source-scheduled arkworks pairing-product check.
/// EthLib equivalence requires canonical coordinates and finite G2 inputs that
/// normalize to on-curve points killed by the subgroup order. Callers validate inputs.
pub fn pairing_check(pairs: &[(crate::Point<Fp>, G2)]) -> bool {
    prepared_miller::pairing_check(pairs)
}

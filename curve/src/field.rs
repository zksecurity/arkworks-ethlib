//! Six-limb Montgomery storage for the BLS12-381 base field, matching arkworks.
//! Public limb/byte constructors and exporters use canonical integers; stored limbs
//! represent x*R mod p. Portable multiplication and conversion are source-adapted.
use crate::{montgomery, Field, Point};

pub mod inversion;

pub const MODULUS: [u64; 6] = [
    0xb9feffffffffaaab,
    0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624,
    0x64774b84f38512bf,
    0x4b1ba7b6434bacd7,
    0x1a0111ea397fe69a,
];

#[derive(Clone, Copy)]
pub struct Fp {
    limbs: [u64; 6],
}

/// ark-bls12-381 G1Config's coefficient B = 4, in Montgomery form.
pub const G1_COEFF_B: Fp = Fp {
    limbs: [
        0xaa270000000cfff3,
        0x53cc0032fc34000a,
        0x478fe97a6b0a807f,
        0xb1d37ebee6ba24d7,
        0x8ec9733bbf78ab2f,
        0x09d645513d83de7e,
    ],
};

/// Montgomery component of ark-bls12-381 G2Config's coefficient B = (4, 4).
pub const G2_COEFF_B_COMPONENT: Fp = Fp {
    limbs: [
        0xaa270000000cfff3,
        0x53cc0032fc34000a,
        0x478fe97a6b0a807f,
        0xb1d37ebee6ba24d7,
        0x8ec9733bbf78ab2f,
        0x09d645513d83de7e,
    ],
};

/// ark-bls12-381 Fq2Config's Frobenius coefficient table, stored in Montgomery form.
pub const FROBENIUS_FP2_C1: [Fp; 2] = [
    Fp {
        limbs: montgomery::R,
    },
    Fp {
        limbs: [
            0x43f5fffffffcaaae,
            0x32b7fff2ed47fffd,
            0x07e83a49a2e99d69,
            0xeca8f3318332bb7a,
            0xef148d1ea0f4c069,
            0x040ab3263eff0206,
        ],
    },
];

/// The upstream `ENDO_COEFFS[0]`, stored in Montgomery representation.
pub const G1_BETA: Fp = Fp {
    limbs: [
        0x30f1361b798a64e8,
        0xf3b8ddab7ece5a2a,
        0x16a8ca3ac61577f7,
        0xc26a2ff874fd029b,
        0x3636b76660701c6e,
        0x051ba4ab241b6160,
    ],
};

/// ark-bls12-381 Fq6Config Frobenius coefficient table C1.
pub const FROBENIUS_FP6_C1: [[Fp; 2]; 6] = [
    [
        Fp {
            limbs: [
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
        Fp {
            limbs: [
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x03f97d6e83d050d2,
                0x18f0206554638741,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x30f1361b798a64e8,
                0xf3b8ddab7ece5a2a,
                0x16a8ca3ac61577f7,
                0xc26a2ff874fd029b,
                0x3636b76660701c6e,
                0x051ba4ab241b6160,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
        Fp {
            limbs: [
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x03f97d6e83d050d2,
                0x18f0206554638741,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
        Fp {
            limbs: [
                0x30f1361b798a64e8,
                0xf3b8ddab7ece5a2a,
                0x16a8ca3ac61577f7,
                0xc26a2ff874fd029b,
                0x3636b76660701c6e,
                0x051ba4ab241b6160,
            ],
        },
    ],
];

/// ark-bls12-381 Fq6Config Frobenius coefficient table C2.
pub const FROBENIUS_FP6_C2: [[Fp; 2]; 6] = [
    [
        Fp {
            limbs: [
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x890dc9e4867545c3,
                0x2af322533285a5d5,
                0x50880866309b7e2c,
                0xa20d1b8c7e881024,
                0x14e4f04fe2db9068,
                0x14e56d3f1564853a,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x03f97d6e83d050d2,
                0x18f0206554638741,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x43f5fffffffcaaae,
                0x32b7fff2ed47fffd,
                0x07e83a49a2e99d69,
                0xeca8f3318332bb7a,
                0xef148d1ea0f4c069,
                0x040ab3263eff0206,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x30f1361b798a64e8,
                0xf3b8ddab7ece5a2a,
                0x16a8ca3ac61577f7,
                0xc26a2ff874fd029b,
                0x3636b76660701c6e,
                0x051ba4ab241b6160,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0xecfb361b798dba3a,
                0xc100ddb891865a2c,
                0x0ec08ff1232bda8e,
                0xd5c13cc6f1ca4721,
                0x47222a47bf7b5c04,
                0x0110f184e51c5f59,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
];

/// ark-bls12-381 Fq12Config Frobenius coefficient table.
pub const FROBENIUS_FP12_C1: [[Fp; 2]; 12] = [
    [
        Fp {
            limbs: [
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x07089552b319d465,
                0xc6695f92b50a8313,
                0x97e83cccd117228f,
                0xa35baecab2dc29ee,
                0x1ce393ea5daace4d,
                0x08f2220fb0fb66eb,
            ],
        },
        Fp {
            limbs: [
                0xb2f66aad4ce5d646,
                0x5842a06bfc497cec,
                0xcf4895d42599d394,
                0xc11b9cba40a8e8d0,
                0x2e3813cbe5a0de89,
                0x110eefda88847faf,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0xecfb361b798dba3a,
                0xc100ddb891865a2c,
                0x0ec08ff1232bda8e,
                0xd5c13cc6f1ca4721,
                0x47222a47bf7b5c04,
                0x0110f184e51c5f59,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x3e2f585da55c9ad1,
                0x4294213d86c18183,
                0x382844c88b623732,
                0x92ad2afd19103e18,
                0x1d794e4fac7cf0b9,
                0x0bd592fc7d825ec8,
            ],
        },
        Fp {
            limbs: [
                0x7bcfa7a25aa30fda,
                0xdc17dec12a927e7c,
                0x2f088dd86b4ebef1,
                0xd1ca2087da74d4a7,
                0x2da2596696cebc1d,
                0x0e2b7eedbbfd87d2,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x30f1361b798a64e8,
                0xf3b8ddab7ece5a2a,
                0x16a8ca3ac61577f7,
                0xc26a2ff874fd029b,
                0x3636b76660701c6e,
                0x051ba4ab241b6160,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x3726c30af242c66c,
                0x7c2ac1aad1b6fe70,
                0xa04007fbba4b14a2,
                0xef517c3266341429,
                0x0095ba654ed2226b,
                0x02e370eccc86f7dd,
            ],
        },
        Fp {
            limbs: [
                0x82d83cf50dbce43f,
                0xa2813e53df9d018f,
                0xc6f0caa53c65e181,
                0x7525cf528d50fe95,
                0x4a85ed50f4798a6b,
                0x171da0fd6cf8eebd,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x43f5fffffffcaaae,
                0x32b7fff2ed47fffd,
                0x07e83a49a2e99d69,
                0xeca8f3318332bb7a,
                0xef148d1ea0f4c069,
                0x040ab3263eff0206,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0xb2f66aad4ce5d646,
                0x5842a06bfc497cec,
                0xcf4895d42599d394,
                0xc11b9cba40a8e8d0,
                0x2e3813cbe5a0de89,
                0x110eefda88847faf,
            ],
        },
        Fp {
            limbs: [
                0x07089552b319d465,
                0xc6695f92b50a8313,
                0x97e83cccd117228f,
                0xa35baecab2dc29ee,
                0x1ce393ea5daace4d,
                0x08f2220fb0fb66eb,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x03f97d6e83d050d2,
                0x18f0206554638741,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x7bcfa7a25aa30fda,
                0xdc17dec12a927e7c,
                0x2f088dd86b4ebef1,
                0xd1ca2087da74d4a7,
                0x2da2596696cebc1d,
                0x0e2b7eedbbfd87d2,
            ],
        },
        Fp {
            limbs: [
                0x3e2f585da55c9ad1,
                0x4294213d86c18183,
                0x382844c88b623732,
                0x92ad2afd19103e18,
                0x1d794e4fac7cf0b9,
                0x0bd592fc7d825ec8,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x890dc9e4867545c3,
                0x2af322533285a5d5,
                0x50880866309b7e2c,
                0xa20d1b8c7e881024,
                0x14e4f04fe2db9068,
                0x14e56d3f1564853a,
            ],
        },
        Fp {
            limbs: [
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ],
        },
    ],
    [
        Fp {
            limbs: [
                0x82d83cf50dbce43f,
                0xa2813e53df9d018f,
                0xc6f0caa53c65e181,
                0x7525cf528d50fe95,
                0x4a85ed50f4798a6b,
                0x171da0fd6cf8eebd,
            ],
        },
        Fp {
            limbs: [
                0x3726c30af242c66c,
                0x7c2ac1aad1b6fe70,
                0xa04007fbba4b14a2,
                0xef517c3266341429,
                0x0095ba654ed2226b,
                0x02e370eccc86f7dd,
            ],
        },
    ],
];

/// Standard BLS12-381 G1 generator, with Montgomery affine coordinates and z=1.
pub fn generator() -> Point<Fp> {
    Point {
        x: Fp {
            limbs: [
                0x5cb38790fd530c16,
                0x7817fc679976fff5,
                0x154f95c7143ba1c1,
                0xf0ae6acdf3d0e747,
                0xedce6ecc21dbf440,
                0x120177419e0bfb75,
            ],
        },
        y: Fp {
            limbs: [
                0xbaac93d50ce72271,
                0x8c22631a7918fd8e,
                0xdd595f13570725ce,
                0x51ac582950405194,
                0x0e1c8c3fad0059c0,
                0x0bbc3efc5008a26a,
            ],
        },
        z: Fp::constant(1),
    }
}

pub(crate) fn less(a: [u64; 6], b: [u64; 6]) -> bool {
    if a[5] != b[5] {
        return a[5] < b[5];
    }
    if a[4] != b[4] {
        return a[4] < b[4];
    }
    if a[3] != b[3] {
        return a[3] < b[3];
    }
    if a[2] != b[2] {
        return a[2] < b[2];
    }
    if a[1] != b[1] {
        return a[1] < b[1];
    }
    a[0] < b[0]
}

pub(crate) fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let wide = a as u128 + b as u128 + carry as u128;
    (wide as u64, (wide >> 64) as u64)
}

fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let wide = (1u128 << 64) + a as u128 - b as u128 - borrow as u128;
    (wide as u64, (1 - (wide >> 64)) as u64)
}

/// Low 384 bits of a-b. Calls below have a>=b, so final borrow is zero.
pub(crate) fn subtract(a: [u64; 6], b: [u64; 6]) -> [u64; 6] {
    let (o0, c0) = sbb(a[0], b[0], 0);
    let (o1, c1) = sbb(a[1], b[1], c0);
    let (o2, c2) = sbb(a[2], b[2], c1);
    let (o3, c3) = sbb(a[3], b[3], c2);
    let (o4, c4) = sbb(a[4], b[4], c3);
    let (o5, _) = sbb(a[5], b[5], c4);
    [o0, o1, o2, o3, o4, o5]
}

pub(crate) fn add_raw(a: [u64; 6], b: [u64; 6]) -> [u64; 6] {
    let (o0, c0) = adc(a[0], b[0], 0);
    let (o1, c1) = adc(a[1], b[1], c0);
    let (o2, c2) = adc(a[2], b[2], c1);
    let (o3, c3) = adc(a[3], b[3], c2);
    let (o4, c4) = adc(a[4], b[4], c3);
    let (o5, _) = adc(a[5], b[5], c4);
    [o0, o1, o2, o3, o4, o5]
}

pub(crate) fn halve(a: [u64; 6]) -> [u64; 6] {
    [
        (a[0] >> 1) | (a[1] << 63),
        (a[1] >> 1) | (a[2] << 63),
        (a[2] >> 1) | (a[3] << 63),
        (a[3] >> 1) | (a[4] << 63),
        (a[4] >> 1) | (a[5] << 63),
        a[5] >> 1,
    ]
}

impl Fp {
    /// Reject noncanonical inputs; private limbs preserve this invariant in Rust.
    pub fn from_limbs(limbs: [u64; 6]) -> Option<Self> {
        match montgomery::from_canonical(limbs) {
            Some(limbs) => Some(Self { limbs }),
            None => None,
        }
    }

    pub fn to_limbs(self) -> [u64; 6] {
        montgomery::into_canonical(self.limbs)
    }

    /// Stored Montgomery limbs, exposed for representation/intermediate comparisons.
    pub fn to_montgomery_limbs(self) -> [u64; 6] {
        self.limbs
    }
}

impl Field for Fp {
    fn constant(n: u32) -> Self {
        if n == 1 {
            return FROBENIUS_FP2_C1[0];
        }
        Self::from_limbs([n as u64, 0, 0, 0, 0, 0]).unwrap()
    }

    fn plus(self, rhs: Self) -> Self {
        let mut out = add_raw(self.limbs, rhs.limbs);
        // a+b < 2p < 2^382, so the final carry is zero and one reduction suffices.
        if !less(out, MODULUS) {
            out = subtract(out, MODULUS);
        }
        Self { limbs: out }
    }

    fn minus(self, rhs: Self) -> Self {
        let limbs = if less(self.limbs, rhs.limbs) {
            add_raw(self.limbs, MODULUS)
        } else {
            self.limbs
        };
        Self {
            limbs: subtract(limbs, rhs.limbs),
        }
    }

    fn times(self, rhs: Self) -> Self {
        Self {
            limbs: montgomery::multiply(self.limbs, rhs.limbs),
        }
    }

    fn square(self) -> Self {
        Self {
            limbs: montgomery::square(self.limbs),
        }
    }

    fn sum_products(a: Self, b: Self, c: Self, d: Self) -> Self {
        Self {
            limbs: montgomery::sum_products(a.limbs, b.limbs, c.limbs, d.limbs),
        }
    }

    fn negative(self) -> Self {
        if self.is_zero() {
            self
        } else {
            Self {
                limbs: subtract(MODULUS, self.limbs),
            }
        }
    }

    fn equal(self, rhs: Self) -> bool {
        self.limbs[0] == rhs.limbs[0]
            && self.limbs[1] == rhs.limbs[1]
            && self.limbs[2] == rhs.limbs[2]
            && self.limbs[3] == rhs.limbs[3]
            && self.limbs[4] == rhs.limbs[4]
            && self.limbs[5] == rhs.limbs[5]
    }

    fn is_zero(self) -> bool {
        self.limbs[0] == 0
            && self.limbs[1] == 0
            && self.limbs[2] == 0
            && self.limbs[3] == 0
            && self.limbs[4] == 0
            && self.limbs[5] == 0
    }
}

/// Concrete entry points keep the field implementation reachable during extraction.
pub fn add_concrete(p: Point<Fp>, q: Point<Fp>) -> Point<Fp> {
    crate::add(p, q)
}
pub fn double_concrete(p: Point<Fp>) -> Point<Fp> {
    crate::double(p)
}
pub fn negate_concrete(p: Point<Fp>) -> Point<Fp> {
    crate::negate(p)
}
pub fn mul_u64_concrete(p: Point<Fp>, k: u64) -> Point<Fp> {
    crate::mul_u64(p, k)
}
/// ark-bls12-381 projective scalar multiplication (reduction and source GLV schedule).
/// Its scalar-action contract requires an on-curve subgroup point.
pub fn mul_256_concrete(p: Point<Fp>, k: [u64; 4]) -> Point<Fp> {
    crate::glv::mul_projective(p, k)
}

fn exponent_bit(exponent: [u64; 6], index: u32) -> bool {
    ((exponent[(index / 64) as usize] >> (index % 64)) & 1) == 1
}

fn pow_loop(a: Fp, exponent: [u64; 6], bits: u32, started: bool, acc: Fp) -> Fp {
    if bits == 0 {
        return acc;
    }
    let bit = bits - 1;
    let set = exponent_bit(exponent, bit);
    if !started && !set {
        return pow_loop(a, exponent, bit, false, acc);
    }
    let squared = acc.square();
    let next = if set { squared.times(a) } else { squared };
    pow_loop(a, exponent, bit, true, next)
}

/// ark-ff's MSB-first power schedule, with the source leading-zero skip.
pub fn pow(a: Fp, exponent: [u64; 6]) -> Fp {
    pow_loop(a, exponent, 384, false, Fp::constant(1))
}

impl Fp {
    /// Arkworks binary-GCD inverse; returns zero on zero, as in EthLib.
    pub fn inverse(self) -> Self {
        match inversion::inverse(self) {
            Some(inverse) => inverse,
            None => Self { limbs: [0; 6] },
        }
    }

    pub fn sign_bit(self) -> bool {
        let negative = self.negative();
        let positive_limbs = self.to_limbs();
        let negative_limbs = negative.to_limbs();
        less(negative_limbs, positive_limbs)
    }

    pub fn to_bytes_be(self) -> [u8; 48] {
        let limbs = self.to_limbs();
        [
            (limbs[5] >> 56) as u8,
            (limbs[5] >> 48) as u8,
            (limbs[5] >> 40) as u8,
            (limbs[5] >> 32) as u8,
            (limbs[5] >> 24) as u8,
            (limbs[5] >> 16) as u8,
            (limbs[5] >> 8) as u8,
            (limbs[5] >> 0) as u8,
            (limbs[4] >> 56) as u8,
            (limbs[4] >> 48) as u8,
            (limbs[4] >> 40) as u8,
            (limbs[4] >> 32) as u8,
            (limbs[4] >> 24) as u8,
            (limbs[4] >> 16) as u8,
            (limbs[4] >> 8) as u8,
            (limbs[4] >> 0) as u8,
            (limbs[3] >> 56) as u8,
            (limbs[3] >> 48) as u8,
            (limbs[3] >> 40) as u8,
            (limbs[3] >> 32) as u8,
            (limbs[3] >> 24) as u8,
            (limbs[3] >> 16) as u8,
            (limbs[3] >> 8) as u8,
            (limbs[3] >> 0) as u8,
            (limbs[2] >> 56) as u8,
            (limbs[2] >> 48) as u8,
            (limbs[2] >> 40) as u8,
            (limbs[2] >> 32) as u8,
            (limbs[2] >> 24) as u8,
            (limbs[2] >> 16) as u8,
            (limbs[2] >> 8) as u8,
            (limbs[2] >> 0) as u8,
            (limbs[1] >> 56) as u8,
            (limbs[1] >> 48) as u8,
            (limbs[1] >> 40) as u8,
            (limbs[1] >> 32) as u8,
            (limbs[1] >> 24) as u8,
            (limbs[1] >> 16) as u8,
            (limbs[1] >> 8) as u8,
            (limbs[1] >> 0) as u8,
            (limbs[0] >> 56) as u8,
            (limbs[0] >> 48) as u8,
            (limbs[0] >> 40) as u8,
            (limbs[0] >> 32) as u8,
            (limbs[0] >> 24) as u8,
            (limbs[0] >> 16) as u8,
            (limbs[0] >> 8) as u8,
            (limbs[0] >> 0) as u8,
        ]
    }
}

pub fn to_affine(p: Point<Fp>) -> (Fp, Fp) {
    let normalized = crate::scalar::normalize(p);
    (normalized.x, normalized.y)
}

pub fn compress(p: Point<Fp>) -> [u8; 48] {
    let affine = crate::scalar::normalize(p);
    let largest = affine.y.sign_bit();
    let bytes = affine.x.to_bytes_be();
    minimal_g1::compress_g1(bytes, largest, affine.infinity)
}

/// Full-curve integer multiplication through the source affine path, then encoding.
pub fn mul_compressed(p: Point<Fp>, k: [u64; 4]) -> [u8; 48] {
    let base = crate::scalar::normalize(p);
    compress(crate::scalar::mul_affine(base, k))
}

/// Source endomorphism subgroup check. Caller must first establish the curve equation.
/// Infinity is accepted; this is not BLS public-key validation.
pub fn in_subgroup(p: Point<Fp>) -> bool {
    crate::scalar::in_subgroup(p)
}

/// Jacobian curve equation Y² = X³ + 4Z⁶; every Z=0 representation is infinity.
pub fn is_on_curve(p: Point<Fp>) -> bool {
    if p.z.is_zero() {
        return true;
    }
    let z2 = p.z.square();
    let z6 = z2.square().times(z2);
    p.y.square()
        .equal(p.x.square().times(p.x).plus(G1_COEFF_B.times(z6)))
}

/// Validate the curve equation before the order-r test; infinity is allowed.
pub fn is_valid_subgroup_point(p: Point<Fp>) -> bool {
    is_on_curve(p) && in_subgroup(p)
}

/// Validate an already represented public-key point, rejecting infinity.
/// This does not parse or validate a compressed byte encoding.
pub fn is_valid_public_key_point(p: Point<Fp>) -> bool {
    !p.z.is_zero() && is_valid_subgroup_point(p)
}

impl Fp {
    /// Return the Fermat square-root candidate only if its square equals the input.
    /// The selected root follows EthLib; it is not necessarily the larger root.
    pub fn sqrt(self) -> Option<Self> {
        let candidate = pow(
            self,
            [
                0xee7fbfffffffeaab,
                0x7aaffffac54ffff,
                0xd9cc34a83dac3d89,
                0xd91dd2e13ce144af,
                0x92c6e9ed90d2eb35,
                0x680447a8e5ff9a6,
            ],
        );
        if candidate.square().equal(self) {
            Some(candidate)
        } else {
            None
        }
    }
}

/// Construct a finite affine point after checking the curve equation.
/// Subgroup membership is a separate check; (0,0) is rejected, not treated as infinity.
pub fn from_affine(x: Fp, y: Fp) -> Option<Point<Fp>> {
    let p = Point {
        x,
        y,
        z: Fp::constant(1),
    };
    if is_on_curve(p) {
        Some(p)
    } else {
        None
    }
}

/// Normalize to z=1; all infinity representations become the canonical identity.
pub fn normalize(p: Point<Fp>) -> Point<Fp> {
    crate::scalar::normalize_projective(p)
}

/// Compare represented points without inversion. Caller supplies on-curve points.
pub fn points_equal(p: Point<Fp>, q: Point<Fp>) -> bool {
    crate::scalar::points_equal(p, q)
}

/// Serialize only on-curve, subgroup points; infinity is allowed.
pub fn compress_checked(p: Point<Fp>) -> Option<[u8; 48]> {
    if is_valid_subgroup_point(p) {
        Some(compress(p))
    } else {
        None
    }
}

/// Serialize a validated public-key point, rejecting infinity.
pub fn compress_public_key(p: Point<Fp>) -> Option<[u8; 48]> {
    if is_valid_public_key_point(p) {
        Some(compress(p))
    } else {
        None
    }
}

/// Recover a finite curve point from canonical x and the lexicographic y-sign.
/// This does not enforce subgroup membership or parse compressed bytes.
pub fn from_x(x: Fp, y_is_largest: bool) -> Option<Point<Fp>> {
    crate::decoder::point_from_x_unchecked(x, y_is_largest)
}

/// RFC 9380 BLS12-381 G1 effective-cofactor multiplication, h_eff = 1 - x.
/// Caller supplies an on-curve point. This is not generally identity on subgroup points.
pub fn clear_cofactor(p: Point<Fp>) -> Point<Fp> {
    crate::scalar::clear_cofactor_projective(p)
}

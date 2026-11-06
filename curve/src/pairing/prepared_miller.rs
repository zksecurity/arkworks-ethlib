//! Sequential ark-ec BLS12 multi-Miller schedule, specialized to four-pair chunks.
use super::{prepared, Fp12, G2};
use crate::{field::Fp, AffinePoint, Point};
use alloc::vec::Vec;

struct PreparedPair {
    p: AffinePoint<Fp>,
    q: prepared::PreparedG2,
}

fn collect(
    pairs: &[(Point<Fp>, G2)],
    index: usize,
    mut active: Vec<PreparedPair>,
) -> Vec<PreparedPair> {
    if index == pairs.len() {
        return active;
    }
    let (p, q) = pairs[index];
    let p = prepared::prepare_g1(p);
    let q = prepared::prepare_g2(q);
    if !p.infinity && !q.infinity {
        active.push(PreparedPair { p, q });
    }
    collect(pairs, index + 1, active)
}

fn eval_lines(pairs: &[PreparedPair], index: usize, end: usize, line: usize, f: Fp12) -> Fp12 {
    if index == end {
        return f;
    }
    let pair = &pairs[index];
    let coeff = pair.q.ell_coeffs[line];
    let f = prepared::ell(f, coeff, pair.p.x, pair.p.y);
    eval_lines(pairs, index + 1, end, line, f)
}

fn chunk_bits(
    pairs: &[PreparedPair],
    start: usize,
    end: usize,
    bits: u32,
    line: usize,
    f: Fp12,
) -> Fp12 {
    if bits == 0 {
        return f;
    }
    let bit = bits - 1;
    let f = f.square();
    let f = eval_lines(pairs, start, end, line, f);
    let line = line + 1;
    let (f, line) = if (super::BLS_X >> bit) & 1 == 1 {
        (eval_lines(pairs, start, end, line, f), line + 1)
    } else {
        (f, line)
    };
    chunk_bits(pairs, start, end, bit, line, f)
}

fn chunks(pairs: &[PreparedPair], start: usize, acc: Fp12) -> Fp12 {
    if start == pairs.len() {
        return acc;
    }
    let remaining = pairs.len() - start;
    let end = if remaining > 4 {
        start + 4
    } else {
        pairs.len()
    };
    let f = chunk_bits(pairs, start, end, 63, 0, Fp12::cyclotomic_one());
    chunks(pairs, end, acc.times(f))
}

/// Source preparation before filtering, four-pair chunks, then negative-X conjugation.
/// Iterator positions become one shared line index per chunk; every finite G2
/// preparation has the same 68 coefficients and consumes them in the same order.
pub fn multi_miller_loop(pairs: &[(Point<Fp>, G2)]) -> Fp12 {
    let active = collect(pairs, 0, Vec::new());
    chunks(&active, 0, Fp12::cyclotomic_one()).conjugate()
}

/// Complete source-scheduled arkworks pairing predicate, with the total zero adapter.
pub fn pairing_check(pairs: &[(Point<Fp>, G2)]) -> bool {
    let f = super::final_exponentiation(multi_miller_loop(pairs));
    f.equal(Fp12::cyclotomic_one())
}

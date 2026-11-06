# Pairing proof contracts

[`ConcretePreparedMiller.default_pairing_check_ethlib_spec`](../curve/PreparedPairingEquivalence.lean)
proves that the default extracted `pairing::pairing_check` terminates and
returns exactly unchanged EthLib `pairingCheck` on its declared input domain:

- Every stored coordinate is a canonical Montgomery residue.
- Each finite G2 input normalizes to a point on `y² = x³ + (4+4i)` killed by
  `Fr.modulus` in the proved curve group.
- Infinity pairs contribute the identity. Empty slices are included.

The proof does not require a G1 curve/subgroup assumption. It assumes the stated
G2 domain; it does not verify an external parser or arkworks validation routine.
The target is pinned by the [vendor manifest](../lean/vendor/ethlib/provenance.json),
whose source hashes are checked before every fresh proof run.

The proof connects these stages:

1. Extracted field/tower arithmetic and preparation refine unchanged EthLib fields.
2. The source homogeneous double/add formulas match Mathlib’s curve group law.
3. Kernel-checked fixed-prefix gcd facts exclude exceptional steps on r-torsion inputs.
4. Sparse prepared lines match EthLib’s exact untwist constants, slopes and line
   functions up to nonzero factors killed by final exponentiation.
5. Stored coefficients execute the proved walk; shared squaring and four-pair
   batching give exactly the raw product of independent pair values.
6. Infinity filtering, conjugation, product accumulation and the final Boolean
   agree with EthLib’s array loop.

The source hard chain computes the **cube** of EthLib’s final value for every
canonical field input, including zero. The proved identity-test bridge makes the
pairing Boolean exact. Actual arkworks final-exponent traces match at 51,729,360
Montgomery boundaries across 537 inputs; prepared raw Miller traces match at
5,179,803 boundaries across 30 batch/infinity cases.

The default entry point delegates directly to the prepared implementation; the
superseded affine Rust loop and its extraction proofs have been removed.
The explicit subgroup contract is necessary: a G1 generator paired with off-curve
G2 `(1,0,1)` gives `true` in EthLib’s unchecked loop, while arkworks yields a zero
Miller value and no final-exponent result. The default total adapter returns
`false`, which the native regression checks. No unchecked-input equivalence is claimed.

The default prepared endpoint is compared with arkworks and EthLib on all 15 published
EIP-2537 pairing fixtures and five examples. These comparisons are separate from
the universal Lean equivalence theorem.

This proves implementation equivalence, not bilinearity or cryptographic security.
Native compilation, allocation, stack/resource bounds, full precompile parsing and
gas are outside the proof. Run `make verify-curve` for fresh extraction and audits,
and `make pairing` for published-vector comparisons. Reports are under `build/`.

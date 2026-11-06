# How the subgroup check works

For an on-curve BLS12-381 G1 point, the check decides membership in the prime-order
subgroup. Infinity is accepted. The live implementation follows arkworks' fast
endomorphism algorithm; EthLib's integer order-r test remains the specification.

## Rust algorithm

[field.rs](../curve/src/field.rs) delegates to [scalar.rs](../curve/src/scalar.rs):

1. Normalize Jacobian coordinates to the source affine representation.
2. Compute `[X]P` with the source affine integer loop, where
   `X = 0xd201000000010000` is the absolute BLS parameter.
3. Reject when `[X]P = P` and P is finite.
4. Compute `-[X]([X]P)` with the source projective GLV loop and negation.
5. Compare that point with the affine endomorphism `(beta*x, y)`.

The caller must establish the curve equation. `is_valid_subgroup_point` checks
it first; `is_valid_public_key_point` also rejects infinity. The byte decoder
establishes the equation by checked square-root reconstruction before calling
the subgroup check.

Each field element stores six canonical Montgomery limbs. For nonzero Z,
Jacobian `(X,Y,Z)` represents `(X/Z²,Y/Z³)`; every Z=0 representation is infinity.
Normalization retains arkworks' infinity and Z=1 shortcuts. Equality uses the
source Jacobian cross-products, including their multiplication grouping.

## Rust → Lean → EthLib

Charon translates the Rust into LLBC, then Aeneas generates executable Lean.
Extraction includes the concrete limb arithmetic, inverse and scalar loops.

- [G1CurveProof.lean](../curve/G1CurveProof.lean) connects the coordinate formulas
  to an independent Mathlib elliptic-curve group.
- [G1FastSubgroupProof.lean](../curve/G1FastSubgroupProof.lean) proves the
  endomorphism criterion characterizes r-torsion on the full curve and proves
  the early-out safe.
- [G1ParameterMultiplicationProof.lean](../curve/G1ParameterMultiplicationProof.lean)
  proves the second GLV multiplication is valid before membership is known:
  this fixed scalar has decomposition `(X,0)`.
- [G1FastSubgroupModelProof.lean](../curve/G1FastSubgroupModelProof.lean) combines
  normalization, both scalar operations, equality, negation and the endomorphism
  into a Boolean model equivalent to EthLib's `G1.inSubgroup` on every on-curve input.
- [FastSubgroupProof.lean](../curve/FastSubgroupProof.lean) proves the extracted
  Rust computes that exact model on all canonical coordinate inputs.
- [DecoderCurveProof.lean](../curve/DecoderCurveProof.lean) proves successful
  decompression supplies the on-curve precondition used by the decoder proof.

The direct refinement theorem in [EncodingProof.lean](../curve/EncodingProof.lean)
requires both canonical stored coordinates and an on-curve decoded point.
Guarded point validators and byte decoding discharge the latter obligation.
`make verify-curve` freshly extracts the Rust, checks the complete proof graph,
and audits theorem dependencies against the standard Lean axioms.

## Independent comparisons and boundaries

The instrumented arkworks runner compares 14 subgroup executions at 93,882 Fq
boundaries and 1,522 inverse states, including rescaled points, infinity, torsion,
off-curve coordinates and sampled full-curve points. Source Fr scalar/decomposition
instructions are excluded from this Fq trace. Off-curve schedule comparisons do
not extend the mathematical subgroup theorem beyond its on-curve domain.

Native tests also compare validation, checked encodings and decoding against
arkworks and published vectors. Charon/Aeneas translation and native compilation
are outside the Lean proof. Public-key point validation does not establish proof
of possession or signature validity.

Cofactor clearing separately follows the source normalized affine multiplication
by RFC 9380's effective cofactor `0xd201000000010001`. Its full-curve point agreement
with EthLib is proved, and ten kernel-checked RFC equations connect published
input points through addition/cofactor multiplication to their final coordinates.
Full message-to-point hashing remains outside these checks.

See [proof coverage](proof-coverage.md) and [source alignment](arkworks-alignment.md)
for the remaining APIs, declared domains and migration work.

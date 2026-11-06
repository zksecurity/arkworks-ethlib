# A different algorithm with the same proved specification

The original MSB-first `field::pow` and the first optional optimization are
preserved. The new [alternative Rust](../curve/src/alternative/field_power.rs)
scans exponent bits from low to high, multiplying selected powers of the base
into an accumulator. It squares the running base rather than the accumulator,
and processes all 384 bits, including leading zeros.

For `a^17`, whose binary expansion is `10001`:

| Implementation | Evolution | Squares | Multiplications |
|---|---|---:|---:|
| Original | Accumulator: `1 → a → a² → a⁴ → a⁸ → a¹⁷` | 5 | 2 |
| First optimization | Accumulator: `a → a² → a⁴ → a⁸ → a¹⁷` | 4 | 1 |
| LSB-first alternative | Running base: `a, a², a⁴, a⁸, a¹⁶, …`; accumulator selects `a` and `a¹⁶` | 384 | 2 |

This is an algorithm-equivalence demonstration, not a performance improvement.
The final square is intentionally retained, and zero exponents still perform
384 squares while returning one, including `0^0`. All three implementations are
variable time; the alternative's conditional multiplications depend on exponent
bits even though its iteration count is fixed.

## Proof against EthLib

[AlternativeFieldPowerProof.lean](../curve/AlternativeFieldPowerProof.lean)
checks the actual freshly extracted Rust computation. Before processing bit `i`,
its invariant is:

```text
decode(power) = a^(2^i)
decode(acc)   = a^(exponent mod 2^i)
```

The optional multiplication adds the next bit's contribution, and squaring the
running base prepares `a^(2^(i+1))`. At bit 384, the consumed prefix is the entire
six-word exponent. The well-founded proof establishes successful termination,
canonical intermediate/output values and equality to EthLib `Fp.powNat` for
every canonical base and arbitrary 384-bit exponent. Neither nonzero bases nor
nonzero exponents are assumed.

The original and alternative have separate `pow_spec` theorems against that same
specification. `AlternativeFieldPower.equivalence_spec` additionally proves that
both terminate and return identical canonical Montgomery values. There are no
new axioms or proof holes; Charon/Aeneas translation remains trusted.

## Actual execution traces

The native suite compares 460 combinations against the original, the first
optimization, and pinned actual Arkworks. Thirty instrumented cases cover
zero/one/minus-one/general bases and zero, one, 17, cross-word, highest-bit and
maximum exponents. Each alternative call records exactly
`384 * 9 + popcount(exponent) * 6` boundaries: nine per field square and six per
Montgomery multiplication.

For `7^17`, Arkworks and the original have 57 identical snapshots; the alternative
has 3,468 snapshots, beginning with a different arithmetic operation, and the
same final raw Montgomery limbs. The runner exports the real snapshots to
`build/power-trace-example.json`. All limbs, reduction factors, product carries
and reduction carries match between Arkworks and the original. Snapshots are
arithmetic boundaries, not a complete Rust or CPU instruction trace. Matching
samples are executable evidence, separate from the universal Lean proof.

## Reproduce

```sh
make verify-curve
python3.11 scripts/offline_cargo.py test --release --config profile.release.overflow-checks=true --test optimization
make compare-intermediates
```

The first example remains documented in [optimization-example.md](optimization-example.md).

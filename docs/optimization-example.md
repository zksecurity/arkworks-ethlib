# Optimization with a different trace and the same proved result

The source-aligned original remains at `curve/src/field.rs::pow`. The optional
optimized function is in [optimized/field_power.rs](../curve/src/optimized/field_power.rs).
Nothing in the existing arithmetic, decoder or pairing paths switches to it.

Both functions accept a canonical BLS12-381 field element and an arbitrary
six-word unsigned exponent. The original MSB-first algorithm starts from one.
When it sees the first set bit, it computes `1² * a`. The optimized version
initializes the accumulator directly to `a` and continues with the remaining bits.
Zero exponents still return one, including `0^0`.

This saves one field square and one multiplication for every nonzero exponent.
For exponent 17 (`10001` in binary), the original performs five squares and two
multiplications; the optimized function performs four squares and one multiplication.
These are arithmetic-operation savings, not a claim about measured wall-clock speed.

## New Aeneas proof

[OptimizedFieldPowerProof.lean](../curve/OptimizedFieldPowerProof.lean) checks the
actual freshly generated function bodies. `pow_loop_spec` proves the original
loop model is preserved under an invariant: before the first set bit the
accumulator decodes to one. The direct initialization therefore replaces
`1 * 1 * a` with `a` without changing the represented result.

`pow_spec` proves successful termination, canonical output and

```text
decode(result) = EthLib.Fp.powNat(decode(a), exponentValue)
```

for every canonical base and every six-word exponent. This is the original
function's contract. `equivalence_spec` runs both extracted computations and
proves both terminate and return the same canonical Montgomery value.
`same_montgomery_value` also relates any successful outputs directly.
The standard Lean axiom audit includes all five new theorems; there are no
additional assumptions about the exponent or nonzero base.

## Deliberately different traces

The instrumented test runs actual arkworks, the original and the optimized
function on the same inputs. It still requires the original's trace to match
arkworks. For each nonzero exponent it instead requires the optimized trace to
contain exactly 15 fewer recorded boundaries: nine from a complete square and
six from a Montgomery multiplication. Both outputs must match the original and
actual arkworks raw Montgomery limbs.

For `7^17` the test checks:

| Observation | Original | Optimized |
|---|---:|---:|
| Recorded arithmetic boundaries | 57 | 42 |
| First field operation | Square of 1 | Square of 7 |
| Raw Montgomery output | Identical | Identical |

Thirty instrumented cases cover zero/one/minus-one/general bases and zero, one,
17, cross-word, highest-bit and maximum exponents. All 25 nonzero-exponent traces
are shorter. The independent native test compares another 460 combinations,
including seeded pseudorandom full-width bases and exponents.

This example demonstrates equivalence through a shared proved specification,
while allowing a different arithmetic schedule. The traces provide executable
evidence of the change; the universal correctness argument is the new Lean proof.

## Reproduce

```sh
make verify-curve
python3.11 scripts/offline_cargo.py test --release --config profile.release.overflow-checks=true --test optimization
make compare-intermediates
```

The report is `build/arkworks-intermediates.json`; the test prints the `7^17`
example and the number of deliberately different traces. Extraction/compiler trust
and the variable-time nature of the original implementation remain unchanged.

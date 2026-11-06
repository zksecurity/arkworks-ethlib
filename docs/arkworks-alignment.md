# Arkworks source alignment

This implementation specializes arkworks 0.5.0 source to BLS12-381, preserves its chosen
operation schedules, and proves the adapted implementation against unchanged
EthLib. [The migration audit](migration-audit.md) records final acceptance evidence.
The Rust adaptation and universal EthLib refinements are distinct from executable
comparisons with the original crate; universal equivalence to the whole arkworks
crate is not claimed.

## Source mapping and current differences

Source revisions and file hashes are recorded in
[the provenance manifest](../provenance/arkworks-0.5.0.json), using the metadata in
the published 0.5.0 crates. The library source is MIT/Apache-2.0 dual licensed;
this project's adaptations use the Apache-2.0 option.

| Primitive | Arkworks source | Specialization and proof contract |
|---|---|---|
| G1 doubling | `ark-ec`, `models/short_weierstrass/group.rs`, `double_in_place` | Adapted the `A=0`, base-field-degree-1 schedule: `D=4XY²`, `E=A+2A`, and `Z=2(ZY)`; the Z update precedes X/Y, and the Y product retains source operand order. Mutable temporaries become returned values. Multiplication/storage now use Montgomery form; dedicated squaring now uses the upstream schedule; fused products in addition now use the upstream schedule. |
| G1 projective addition | Same file, projective `AddAssign` | Adapted negative `J`, addition of `J`, and `Z=2Z1Z2H`. The wrapper now retains arkworks’ projective path when `z2=1`. `G1Alignment.add_projective` proves that removing EthLib’s mixed dispatch preserves the exact result for arbitrary coordinates. The fused `sum_of_products` uses the upstream two-product Montgomery schedule. |
| G1 mixed addition | Same file, affine `AddAssign` | Adapted `I=4H²`, negative `J`, and `Z=2(Z1H)`. `AffinePoint { x, y, infinity }` now retains the upstream affine representation. The separate `add_affine` entry point preserves the upstream infinity-first branch order and uses the fused Montgomery field product. Its exact EthLib contract preserves the original point when the affine input is infinity. |
| Identity, negation, generator | Same file; `ark-bls12-381`, `curves/g1.rs` | Generator constants now use Montgomery limbs; coordinate formulas agree. The generator refinement and raw Montgomery-coordinate comparisons pass. |
| Base-field arithmetic | `ark-ff`, `fields/models/fp/montgomery_backend.rs` | `montgomery.rs` now ports the actual macro-generated six-limb no-carry multiplication. It extracts, has universal arithmetic/carry proofs, and matches upstream round traces. `Fp` now stores Montgomery limbs and uses that multiplication and the source-adapted constructors/conversion. Native raw-limb tests and fresh extraction pass. Conversion and field-operation refinements use the Montgomery decoding map. The entire dependent proof graph passes fresh extraction and the complete audit, including decoding and pairing checks. The dedicated square now uses the actual upstream cross-product, doubling, diagonal and six-round reduction schedules. Its complete arithmetic/carry proof and Montgomery field refinement are checked, and G1 formulas, exponentiation, curve checks and decoder recovery use it. Actual upstream phase/reduction traces agree. The two-product fused operation now retains the derive macro’s interleaved accumulation/reduction schedule, has a complete arithmetic/carry proof, and is used by projective and mixed addition. The live binary-GCD inversion retains the upstream u/v normalization and b/c updates and matches complete upstream state traces. Both normalization loops and the outer loop have termination and coefficient-invariant proofs, yielding full agreement with unchanged EthLib. The total field API maps the upstream zero `None` result to zero. |
| Scalar multiplication | `ark-bls12-381`, `curves/g1.rs`, `mul_projective`; `ark-ec` GLV and affine scalar helpers | The live concrete projective API now uses source scalar reduction, bounded signed decomposition and the complete source GLV loop. Its scalar-action proof requires on-curve r-torsion inputs. Full-integer APIs normalize and use source affine multiplication with no scalar reduction; their full-curve scalar-action proofs require on-curve inputs. Both have exact source-coordinate models on all canonical inputs. The old EthLib-shaped Rust scalar recursions are removed. |
| Cofactor clearing and G1 normalization | `ark-bls12-381`, `curves/g1.rs`, `clear_cofactor`; `ark-ec` affine scalar helper and projective conversion | The live cofactor path now normalizes its input, runs source affine multiplication by the fixed canonical effective cofactor, and returns the source normalized representation. Shared normalization serves affine export, point normalization and G1 preparation, retaining infinity and Z=1 shortcuts. Exact source-coordinate and full-curve mathematical agreement with EthLib are proved. |
| Subgroup check | `ark-bls12-381`, `curves/g1.rs`, `is_in_correct_subgroup_assuming_on_curve` | The live Rust path now retains the source affine normalization, integer X multiplication, early-out, projective GLV X multiplication, negation, affine endomorphism conversion and source equality. Complete source-model and on-curve EthLib Boolean equivalence proofs connect the pipeline. Decompression proves its on-curve output before the check. |
| Encoding/decoding | `ark-bls12-381`, `curves/util.rs` and `curves/g1.rs` | The live compressed serializer retains affine normalization, sign comparison before x conversion, canonical infinity and the source flag stages. The source fixed-array reader, flag parsing/removal and sorted-root reconstruction are ported. Error details become `Option`; affine points use projective adapters; `Read`/`Write` become fixed arrays. The slice frontend deliberately requires exactly 48 bytes, whereas the upstream stream reader consumes a 48-byte prefix; tests record both contracts. All-byte EthLib decoder refinements and formatter/compressor proofs remain checked. |
| Extension fields | `ark-ff`, quadratic/cubic extension models | `Fp2` now uses the degree-two two-fused-product multiplication path, the dedicated `NONRESIDUE=-1` square, the source-order inverse norm and zero shortcut, and the `(1+i)` nonresidue schedule. Their unchanged EthLib refinements pass. Base inversion now uses the proved source-specialized binary-GCD algorithm, with the existing total zero result replacing upstream `Option`. `Fp6` now retains the upstream cubic Karatsuba temporary order, dedicated CH-SQR2 square, inverse temporary/norm order, zero shortcut and final multiplication orientation; these refine unchanged EthLib. `Fp12` now retains the quadratic Karatsuba temporary order, dedicated complex square, inverse norm order and zero shortcut. Pairing exponentiation uses the dedicated square, and all refinements to unchanged EthLib pass. The source sparse `mul_by_1`, `mul_by_01` and `mul_by_014` schedules are now implemented and proved. `Fp2::frobenius` now retains the precomputed coefficient table and the upstream coefficient multiplication; its complete refinement proves the result equals EthLib `Fp2.powNat(a, p^power)` for every canonical input and every power. `Fp6::frobenius` also retains all three quadratic maps and both coefficient-table products, with a complete modulus-power proof. `Fp12::frobenius` retains both cubic maps and the three Fp2 coefficient products, with a complete refinement to EthLib modulus powers. The live final exponentiation now uses this map for its p-squared stage. Granger–Scott squaring and the signed NAF parameter exponent have complete mathematical refinements on their zero-or-cyclotomic domain. The live parameter-specific hard chain is proved to compute the cubed EthLib hard power. The prepared source endpoint now consumes these operations; its exact original EthLib pairing bridge is proved on the declared finite-G2 subgroup domain. |
| Pairing | `ark-ec`, `models/bls12/mod.rs` and prepared G1/G2 code | the live final exponentiation retains arkworks’ easy stages, signed NAF helper, Granger–Scott squares, Frobenius calls and hard-chain temporary order. Its complete refinement proves the cube of unchanged EthLib’s final value on every canonical input; the executable `pairing_check` Boolean equals EthLib exactly. Affine G2 preparation, homogeneous double/add and sparse line evaluation are ported with source-polynomial refinements. G1 preparation and projective G2 normalization also retain source shortcuts and refine EthLib exactly. The default prepared endpoint retains source four-pair chunks and has a complete source-schedule refinement. Its exact original EthLib `pairingCheck` equivalence is proved on the finite-G2 subgroup domain. The default now delegates to the prepared path, and the superseded Rust loop is removed. |

The current G1 polynomial proofs remain statements about arbitrary canonical
coordinates, not just generated subgroup examples. They now need algebraic
identities instead of simply unfolding identical Rust/Lean instruction schedules.
This is still a proof against EthLib, not an extraction of the whole arkworks crate.

Affine addition deliberately preserves the original point when the affine input
is infinity, including a nonstandard Jacobian infinity representation. Its proof
therefore states `if q.infinity then p else EthLib.add p (q.x, q.y, 1)`.
Projective addition retains exact agreement with `EthLib.add` on all canonical
coordinate inputs. The formula bridge proves equality of coordinates, without
assuming curve membership, subgroup membership, or a unique infinity encoding.

`BasePrime.modulus_prime` now proves primality of EthLib's BLS12-381 base
modulus. Its 35-node Lucas certificate is explicit in
`provenance/bls12-381-base-prime.json`; `scripts/generate_base_prime.py`
renders ordinary Lean proofs, and fresh verification checks both reproducibility
and the kernel proof. PARI/GP was used only to discover candidate factors and
witnesses. Builds do not run or trust it. This establishes a foundation for the
binary-inverse proof, quadratic Frobenius proof and remaining tower Frobenius proofs.

## Rules for the remaining migration

1. Record the exact upstream function, revision and branch specialized away.
2. Preserve representations, constants, operation order and exceptional branches.
3. Identify every adaptation: trait specialization, fixed limb count, mutation
   elimination, iterator lowering, and allocation/I/O boundaries.
4. Compare raw field limbs or projective coordinates where meaningful, as well as
   normalized values. An affine-only check can hide a different formula schedule.
5. Keep existing EthLib refinement theorems and published-vector checks passing.
   When a contract must change, state that explicitly rather than silently adding
   a subgroup or nonzero-input assumption.

## Intermediate computation comparisons

`make compare-intermediates` copies the checksum-pinned `ark-ff`,
`ark-ff-macros` and `ark-ec` archives into an isolated `build/` directory. The only change to
the macro's multiplication schedule is an observer after each outer round; the
actual `Fq` multiplication executes that generated code. The observer records the
six limbs, Montgomery reduction factor and both carries. The source diff is saved
beside the generated test project for review.

537 products currently compare all 3,222 round boundaries and final raw limbs,
including zero, one, `R`, `R²`, `p-1` and deterministic random residues. The test
also checks the cancelled low limb and runs with overflow checks enabled.
Another 537 conversions compare all 3,222 cyclic conversion round boundaries,
and 537 constructors compare 3,192 multiplication rounds (zero takes the upstream
shortcut). Invalid canonical inputs are rejected by both implementations.
These are tests against actual instrumented upstream computation, not a second
hand-written reference algorithm. `MontgomeryProof.multiply_value` separately
proves the extracted arithmetic computes `a*b/R mod p` with a canonical result.

The dedicated square additionally compares 537 calls at 1,611 cross-product,
doubling and diagonal boundaries and 3,222 actual reduction rounds. Final raw
outputs and all reduction factors/carries match. `MontgomerySquareProof.lean`
proves the wide-product prefix exactly. `MontgomerySquareReductionProof.lean`
proves the six reduction rounds, telescoping identity, absence of final overflow,
canonical output and complete `a²/R mod p` result. `ConcreteField.square_spec`
connects the integrated `Fp::square` to EthLib multiplication of a field element
by itself. The proof factors the extracted body using monad associativity; it
preserves every extracted arithmetic call.

The fused two-product path compares 1,162 calls, including all 625 combinations
of the five raw edge residues and 537 deterministic mixed cases. All 20,916
pair-accumulation and reduction boundaries match the actual derive-macro path,
including both carry words, reduction factors, and final raw limbs.
`MontgomeryFusedProof.lean` proves the complete `(a*b+c*d)/R mod p` operation,
including no discarded overflow and the bound permitting one final subtraction.
`ConcreteField.sum_products_spec` connects it to EthLib `a*b+c*d`. Projective and
mixed G1 addition now call this fused operation at the upstream Y-coordinate site.

The `Fp2` comparisons exercise 537 products, 537 dedicated squares and 537
inverses, comparing 41,856 base-field boundaries inside actual upstream calls.
Multiplication compares both fused products; squaring compares both base products;
inversion compares the two norm squares and the final products, with separate
state observers covering the complete base-field inverse between them. All final stored
Montgomery coefficients match arkworks. `Fp2::inverse(0)` retains this project's
total zero result; upstream returns `None`.

The `Fp6` comparisons instrument **both actual implementations** in isolated
source copies. They compare 537 multiplications, squares and inverses at 383,028
Montgomery accumulation, reduction and square-phase boundaries, including exact
limbs, factors and carries. Observer callbacks retain the arithmetic statements;
the patch is saved beside the generated test project. The live base inverse now
uses binary GCD on both sides. Separate observers compare every `u/v/b/c` state
inside Fp2, Fp6 and Fp12 inversion as well as the surrounding Montgomery boundaries.
The square and inverse bridges are coefficient-level ring proofs in
`ExtensionAlignmentProof.lean`, with separate checks of the zero shortcut.

The `Fp12` comparisons likewise instrument both actual executions for 537
multiplications, squares and inverses, matching 1,136,328 boundaries and every
final Montgomery coefficient. Cases include zero, one, negative one, the tower
generator and deterministic mixed residues. The three tower-inverse comparisons
also check 1,292,104 actual binary-GCD state boundaries. `quadratic_square` proves the complex-square schedule
coefficient by coefficient; the zero predicate and inverse shortcut are proved
separately. The arithmetic uses the pinned generic quadratic backend with the
BLS12-381 `v` nonresidue wrapper, recorded in the provenance manifest.

The sparse helpers compare 537 cases each at 405,972 actual execution
boundaries, including exact factors and carries. Their final coefficients also
match ordinary multiplication by the corresponding sparse element. The Lean
bridges prove these identities for all canonical inputs. `mul_by_014` is the
M-twist line multiplier used by the default prepared pairing loop.

The live binary-GCD inverse compares 537 inputs and 423,634 actual `u/v/b/c`
state boundaries, recording initialization, each halving update, each subtraction
and the return state. Option results and every stored coefficient match arkworks;
nonzero results also match independently computed Fermat powers.
`BaseFieldProof.lean` connects EthLib's exponentiation to ordinary powers, proves
the nonzero inverse equation and uniqueness, and provides cancellation of two.
`BinaryInverseProof.lean` proves raw-one detection, modular halving, termination of
both normalization loops and the outer loop, coprimality and coefficient invariants,
and complete agreement with EthLib for every canonical input. The live `Fp::inverse`
uses this implementation, mapping the zero `None` result to zero. Fresh verification
sets `binary_inverse_refinement_proved=true` only after all dependent proofs pass.

`Fp2::frobenius` specializes the generic quadratic map: the two base-field
Frobenius calls are identities, while the coefficient lookup and multiplication
remain. The table stores arkworks' `1` and `-1` as Montgomery constants.
`Fp2FieldProof.lean` proves ring laws for unchanged EthLib coefficient operations,
connects its executable power to ring powers, and proves `a^p = conjugate(a)`
using prime characteristic and `p % 4 = 3`. Iteration proves the full `p^power`
contract; `ConcreteExtension.fp2_frobenius_spec` connects extracted Rust to it.
Native tests compare both final stored coefficients, and actual execution observers
compare 6,444 maps at 38,664 Montgomery round boundaries, including powers zero,
one, both parities and the largest machine-sized powers. The Fp12 map uses this
helper through Fp6, including in the live final exponentiation.

`Fp6::frobenius` keeps the upstream cubic schedule: map c0, c1 and c2, then
multiply c1 and c2 by their precomputed table entries. `Fp6FieldProof.lean`
proves ring laws for unchanged EthLib arithmetic and derives the symbolic modulus
power from characteristic p and `v³ = 1+i`. `Fp6FrobeniusProof.lean` verifies the
first nonresidue power using a kernel-checked modular power, proves the six-entry
coefficient recurrence including wraparound, and establishes the full `p^power`
formula. `Fp6FrobeniusRefinement.lean` connects the freshly extracted Rust code
to that formula for all canonical inputs and all machine-sized powers. The second
table is checked against the square of the first table coefficient.
Actual execution comparisons cover 6,444 maps and 579,960 Montgomery boundaries,
including both tables, all six residues, zero input and maximum-sized powers.
Fp12 uses the cubic map in the live final-exponentiation p-squared stage.
The prepared endpoint uses these maps, with its finite-G2 subgroup equivalence proof.

`Fp12::frobenius` keeps both cubic maps followed by three quadratic products with
the selected coefficient. `Fp12FieldProof.lean` proves ring laws and connects the
pinned executable `Fp12.powNat` to ring powers. `Fp12FrobeniusProof.lean` derives
the modulus-power formula from `w² = v` and `v³ = 1+i`, verifies the first table
coefficient's nonresidue power, and proves the twelve-entry recurrence including
wraparound. `Fp12FrobeniusRefinement.lean` proves the extracted Rust map agrees
with EthLib `Fp12.powNat(a, p^power)` for every canonical input and machine-sized
power. Actual execution observers compare 8,055 maps and 2,319,840 Montgomery
boundaries, including all twelve table entries and maximum-sized powers.
The live final exponentiation uses source-scheduled Frobenius in both the easy
and hard stages. Its optimized hard chain follows arkworks' cubed convention:
`ConcretePairing.final_exponentiation_cube_spec` proves its result is the cube of
unchanged EthLib's `finalExponentiation` for every canonical input. Zero maps to
zero instead of upstream's `None`.

`HardChainProof.lean` derives the actual operation chain's exponent, checks its
residue modulo `p⁴-p²+1`, and proves the cubed hard-power contract, including zero.
`HardChainRefinement.lean` connects every extracted temporary to that mathematical
chain. `HardExponent.final_cube_isOne` proves that cubing preserves the final
identity test. `ConcretePreparedMiller.default_pairing_check_ethlib_spec` gives
exact EthLib Boolean agreement on the declared finite-G2 subgroup domain.

Actual upstream and minimal live final-exponent executions compare **537 inputs
and 51,729,360 Montgomery boundaries**, including zero and exact raw output
coefficients. The native cube-convention test additionally compares both against
an ordinary EthLib hard power and requires a sample with differing uncubed value.
The prepared source endpoint now uses these stages; its finite-G2 subgroup EthLib bridge is proved.

`TowerInverseProof.lean` proves a zero-or-inverse alternative for the unchanged
Fp2, Fp6 and Fp12 inverse formulas: each result is zero or its product with the
input is one. These statements do not need a new nonzero-input precondition.
`CyclotomicProof.lean` proves that conjugation is the p-to-the-sixth power, that
the first easy stage is zero or unitary, and that the full easy result is zero or
has order dividing `p⁴-p²+1`. The live Rust easy stages now have their own
`final_exponentiation_easy` helper, with the same operation order.
`ConcreteCyclotomic.easy_spec` connects its freshly extracted result to unchanged
EthLib arithmetic and proves this subgroup precondition for every canonical
input, including zero. Native tests compare the prefix against arkworks field
operations and check unitary and Frobenius subgroup identities.
`CyclotomicSquareProof.lean` now proves the Granger–Scott polynomial equals
ordinary squaring on cyclotomic inputs and on zero, and preserves this domain.
It derives the relation `a^(p⁴)*a = a^(p²)` from subgroup membership, writes the
second and fourth Frobenius maps diagonally using the certified cubic root, and
proves six coordinate identities over a generic commutative ring. The concrete
instantiation uses unchanged EthLib operations; it adds no unproved algebraic
assumption. The BLS12-381 characteristic guard is checked by the kernel.
`CyclotomicSquareRefinement.lean` proves the extracted Rust schedule computes the
polynomial on every canonical input, and ordinary squaring with domain preservation
when the caller supplies the easy-stage precondition. The live hard chain uses
this square, with its domain invariant proved across all temporary operations.
The public final-value theorem states the cubed convention explicitly; the pairing
Boolean retains its previous all-canonical-input contract.
Actual arkworks and minimal executions compare 1,074 squares and 231,984 Montgomery
boundaries. Half the cases are arbitrary inputs; the other half use actual
arkworks final-exponentiation results (plus zero), where ordinary squaring is also
checked. The square, signed-parameter power and optimized hard-chain refinement
flags become true only after fresh extraction and the full theorem audit pass.

Reports: `build/arkworks-intermediates.json` and `.log`. The proof audit includes `curve/MontgomeryProof.lean` and
`curve/MontgomeryConversionProof.lean`. The verifier marks the field integration
complete only after fresh extraction and the entire dependent refinement audit pass.

Montgomery storage and its dependent EthLib refinements pass fresh extraction
and the complete audit. The live scalar, subgroup and pairing endpoints also use
their source adaptations; their contracts and final acceptance evidence are
recorded in the migration audit.

### Signed BLS parameter exponent

`Fp12::cyclotomic_exp_x_abs` now specializes ark-ff's fast-inverse NAF loop to
`BLS_X`, and `exp_by_x` applies ark-ec's negative-parameter conjugation. The fixed
65-entry signed table replaces allocation and iterator reversal; the descending
recursive loop retains the first `ONE*base` multiplication, all 64 squares, six
products, and the zero-input early return. `cyclotomic_one` uses the precomputed
Montgomery identity, avoiding a conversion absent from upstream's constant `ONE`.
The live optimized hard chain calls these helpers.

The trace test checks the fixed digits against actual ark-ff `find_naf`, then
compares 1,074 exponent calls at **18,987,264 Montgomery boundaries**. Half the
inputs are arbitrary and half are actual upstream final-exponent subgroup values
or zero. Raw output coefficients and all round states match; the signed wrapper
also matches upstream. On subgroup inputs an ordinary power/inverse checks the
mathematical exponent independently. Native tests additionally exercise the
minimal implementation's own easy-stage outputs.

`HardExponent.naf_value` proves that the extracted signed digits recombine to the
extracted `BLS_X`. `CyclotomicExponentRefinement` proves the source schedule's
termination and canonical output for every canonical input, including inputs
outside the optimized domain.

`CyclotomicParameterProof` proves the mathematical power contract on zero or
cyclotomic inputs. Conjugation is an inverse on the subgroup; representing a
negative digit by exponent `order−1` lets the loop invariant use ordinary natural
powers. A checked integer certificate removes the resulting multiple of the
subgroup order. `CyclotomicParameterRefinement` connects this proof to both public
Rust exponent helpers and proves domain preservation for the following hard-chain
operations. These results require no new field inverse or irreducibility premise.

### Prepared pairing schedule and equivalence

`curve/src/pairing/prepared.rs` specializes arkworks’ M-twist homogeneous
preparation formulas, source scalar products and normalization shortcuts. It uses
precomputed Montgomery constants and a recursive 63-bit producer with the exact
68-line finite / zero-line infinity result. Homogeneous operations and line
helpers match 537 upstream cases at 625,068 boundaries; full G2 preparation
matches at 9,229,920 boundaries. Projective preparation and normalization compare
537 cases at 9,386,775 boundaries.

`curve/src/pairing/prepared_miller.rs` prepares both inputs before filtering,
consumes double/add lines in source order with a shared line index, and processes
four active pairs per chunk. Its raw results match actual arkworks at 5,179,803
Montgomery boundaries across 30 batch/infinity cases, including 4/5 and 8/9 chunk
boundaries. The native endpoint uses this path directly.

The complete prepared endpoint now has an exact equivalence theorem to unchanged
EthLib `pairingCheck`:
`ConcretePreparedMiller.default_pairing_check_ethlib_spec` in
[`PreparedPairingEquivalence.lean`](../curve/PreparedPairingEquivalence.lean).
It requires canonical coordinates and that each finite G2 input normalize to an
on-curve point on the twist killed by `Fr.modulus` in the mathematical curve group.
Infinity inputs are skipped. No G1 curve/subgroup assumption is needed.

The checked proof chain is:

- Tower-domain and inverse proofs supply field structures without replacing
  EthLib operations or vendor code.
- `PreparedCurveGroupProof.lean` proves the twist nonsingular, identifies the
  homogeneous/normalized equations, and connects source double/add to the group law.
- `PreparedPrefixProof.lean` checks every forbidden fixed-prefix factor coprime
  to r. `PreparedSafetyProof.lean` uses the scalar-prefix group invariant to prove
  all walk safety conditions from the stated on-curve r-torsion contract.
- `PreparedLineGeometryProof.lean` matches exact EthLib untwist constants, slopes
  and line functions. `FinalScalingProof.lean` kills their nonzero scaling factors.
- Step and recursive-walk proofs identify the EthLib state and accumulator;
  coefficient-consumption and chunk-algebra proofs connect the stored producer,
  shared squaring and four-pair batching to those independent walks.
- Endpoint assembly handles infinity filtering, conjugation, products and the
  final identity test, then composes with the extracted Rust termination theorem.

The domain change is necessary. For a G1 generator and canonical off-curve G2
`(1,0,1)`, EthLib’s unchecked loop returns `true`; actual arkworks has a zero
Miller value and final exponentiation returns `None`, mapped to `false` by the total
adapter. The native regression records this difference. The new theorem therefore
does not assert all-canonical-input equivalence or add a legacy fallback.

The proof assumes the stated mathematical G2 contract; external validation and
native compilation remain outside its scope. The default prepared Rust endpoint is compared
against arkworks and EthLib on the published pairing fixtures.

The default `pairing::pairing_check` delegates directly to this prepared path.
The old affine Rust loop, duplicate G2 normalization helper, and superseded native
extraction proofs are removed. The remaining pure EthLib fold adapter is in
`EthLibPairingProduct.lean`; it describes the unchanged target, not a fallback.

**Remaining migration:** scalar/GLV, subgroup-endomorphism, encoding/framing and
full source-audit items in the ledger remain open.


## G1 endomorphism foundation

`curve/src/glv.rs` specializes the projective and affine endomorphisms in the
pinned `ark-bls12-381` G1 configuration. Both copy their input and multiply only
x by the precomputed Montgomery coefficient beta; y, z and the affine infinity
flag retain their stored values. No normalization or runtime coefficient conversion
is inserted. The scalar-decomposition implementation is also pinned in the source
manifest and has a complete extracted arithmetic refinement below.

`G1EndomorphismProof.lean` proves the coefficient's canonical representation and
value, beta cubed equals one, beta differs from one, applying the coordinate map
three times is identity, and preservation of the Jacobian curve equation. The
extracted projective and affine functions have complete termination and decoded
coordinate refinements on canonical inputs, including stored infinity coordinates.
`G1EigenvalueProof.lean` extends these coordinate statements to multiplication
by the GLV eigenvalue on every mathematical r-torsion point.

The intermediate runner compares 1,611 endomorphism calls against the actual
pinned arkworks implementation at 9,666 Montgomery round boundaries, including
raw output coordinates, arbitrary canonical inputs, projective infinity and both
affine infinity flags. Scalar decomposition and the GLV source schedule are proved
below. The subgroup eigenvalue relation is proved; replacement of the live
multiplication and order-r subgroup check remains open.


## GLV scalar decomposition contract

[`GLVDecompositionProof.lean`](../curve/GLVDecompositionProof.lean) models the
pinned `ark-ec::GLVConfig::scalar_decomposition` with signed integers, the basis
`(A,1),(-1,A-1)`, truncation toward zero, and the source strict `2*remainder > r`
rounding test. Here `A = 228988810152649578064853576960394133504`,
`r = A*(A-1)+1`, and the pinned eigenvalue is `r-A`.

For every canonical scalar, the proofs establish:

- The second rounded quotient is zero, including at zero. Using floor division
  for its negative numerator would give a different algorithm.
- Both signed component magnitudes are less than `2^128`, and therefore less
  than r. Conversion of their absolute values back to Fr does not reduce them.
- The source positive-sign flag is true exactly for a strictly positive value;
  zero has a false sign flag.
- `k1 + lambda*k2` equals k modulo r. In any additive commutative group killed
  by r, the corresponding signed scalar actions reconstruct `k*P`.

The fresh proof verifier also calls actual pinned arkworks to generate 215 scalar
outputs, compares both signs and magnitudes with the minimal Rust implementation,
and checks them against the executable Lean model using the kernel. Inputs include zero, r-1, word/128-bit boundaries,
rounding-transition neighbors, and deterministic sampled scalars. Expectations
come from `rust/src/bin/glv_decomposition_vectors.rs`; generated statements,
raw outputs, fingerprints and the audit are retained in the proof build directory.
These are newly generated arkworks comparisons, not published external vectors.

The bounded Rust adaptation is now in `curve/src/glv.rs` and
`curve/src/glv/arithmetic.rs`. `GLVArithmeticProof.lean` proves exact 256-by-128-bit
multiplication, terminating quotient/remainder division for inputs below 2^383,
and the strict source rounding rule. `GLVScalarProof.lean` composes those helpers,
proves the signed subtraction and four-word magnitude conversion, and establishes
`ConcreteGLV.scalar_decomposition_total_spec` on every four-word input. Canonical
inputs return exactly the signed source-model components; noncanonical inputs
return `None`. All helper range conditions follow from the canonical-input check.

The extraction adaptations are explicit: fixed-size integer storage replaces
num-bigint, its division is implemented by recursive binary long division, and
the universally zero second quotient and its zero products are eliminated using
`second_quotient_zero`. Fr storage round trips become canonical integer inputs
and outputs; `magnitude_bounds` proves the output conversions cannot reduce the
values. This is not a claim that the integer backend retains num-bigint's internal
instruction schedule. Existing field/pairing Montgomery trace comparisons are
separate from the decomposition sign/magnitude comparisons.

The separate `glv::mul_projective` path now performs scalar reduction and the
source GLV point loop. Its complete subgroup scalar-action proof is below.
The live multiplication and subgroup APIs retain their existing implementations.


## Source GLV point path

`glv::mul_projective` reduces every four-word scalar modulo r, decomposes its
canonical value, prepares the two signed bases and their sum, then consumes all
256 paired bits. It retains the pinned source skip-flag update, including the
unconditional sum of the two bases before iteration.

`GLVReductionProof.lean` proves canonical reduction on every scalar input.
`GLVBitProof.lean` identifies each array bit with the corresponding mathematical
integer bit. `GLVLoopProof.lean` proves loop termination, bounds on every bit read,
canonical output coordinates, and exact agreement with `GLVSchedule.mulProjective`
over unchanged EthLib field and G1 operations. `GLVCorrectnessProof.lean` proves
that this schedule and EthLib’s independent integer multiplication represent
the same mathematical point on on-curve r-torsion inputs.

Native tests compare 420 point/scalar combinations as raw Montgomery coordinates,
including rescaled and nonstandard infinity representations, off-curve points and
small-torsion points. The instrumented comparison checks 78 cases at 555,552
matching Fq execution boundaries, including the initial sum and all loop steps.
The 2,040 four/eight-word Fr trace boundaries are explicitly excluded: source Fr
storage/conversion is replaced by the proved integer backend. These are not
claims of an identical integer-backend instruction schedule.

The trace comparison also checks the source G1 doubling order and operand
orientation. Unit constants use the precomputed Montgomery ONE, avoiding runtime
conversions when constructing identities. Their complete field refinement is
preserved. The default integer multiplication API has not been redirected.

## Mathematical G1 group bridge

`G1CurveProof.lean` interprets EthLib Jacobian points in Mathlib’s BLS12-381
elliptic-curve group. Every Z=0 representation maps to infinity. On the
on-infinity branch, the existing curve predicate is exactly the mathematical
curve equation. Negation, doubling, addition (including equal and opposite
points), and integer multiplication preserve this domain and agree with the
group operations.

`G1GroupRefinementProof.lean` composes those theorems with the extracted Rust
refinements: the live integer multiplier computes `[k]P`, and the live order-r
subgroup check accepts exactly when `[r]P = 0`, assuming an on-curve input.
The separate GLV source path has a complete mathematical multiplication bridge
on on-curve r-torsion inputs. The live concrete projective API now uses this path.

## Signed GLV group action

`GLVGroupProof.lean` proves the source joint scan as an operation in the
mathematical G1 group. It splits each low-bit prefix at its highest bit, proves
the loop invariant after the skip flag clears, and uses the components’ 128-bit
bounds to establish the initial zero pair. The signed source decomposition
therefore computes `[k1]P + [k2]phi(P)` for every on-curve input and every scalar.

`GLVGroupRefinementProof.lean` connects this result to the extracted Rust path.
It also proves `[k]P` correctness when `[r]P = 0` and
`phi(P) = [lambda]P` are supplied explicitly. `G1EigenvalueProof.lean` discharges
the second hypothesis for every r-torsion input; `GLVCorrectnessProof.lean`
composes the complete result. The default multiplier and subgroup check remain unchanged.

`ScalarPrimeProof.lean` proves r is prime from an explicit recursive Lucas
certificate in `provenance/bls12-381-scalar-prime.json`. The existing certificate
renderer supports `--scalar`; its output and all modular-power obligations are
checked by Lean’s kernel. This supports the remaining subgroup argument.

## Mathematical subgroup foundation

`FiniteCurveProof.lean` bounds the mathematical point group by three times the
field cardinality, using x-coordinate fibers. `PrimeTorsionProof.lean` proves
that a prime-order point generates all r-torsion whenever the full finite group
has fewer than r² points.

`G1TorsionProof.lean` specializes these bounds to BLS12-381. Kernel-checked
fixed-base computations establish the standard generator’s order r and
`phi(G) = [lambda]G`. Every mathematical r-torsion point is therefore a signed
multiple of G. `CubicEndomorphismProof.lean` proves the geometric coordinate map
is a group homomorphism, and `G1EigenvalueProof.lean` extends the generator
relation to every subgroup point.

## Complete GLV subgroup bridge

`CubicEndomorphismProof.lean` proves the cube-root coordinate map preserves the
full affine group law, including infinity and vertical-line cases, over any
elliptic short Weierstrass curve. `G1EigenvalueProof.lean` connects that
homomorphism to the existing raw G1 map and uses the torsion generator theorem
to prove `phi(P) = [lambda]P` for every mathematical r-torsion input.

`GLVCorrectnessProof.lean` removes the eigenvalue hypothesis from the extracted
Rust GLV contract. For every canonical, on-curve r-torsion input and every
four-word scalar, the source multiplier terminates, preserves the curve, and
represents the same point as EthLib integer multiplication. This is equality
in the mathematical curve group; raw Jacobian coordinates retain the arkworks
schedule and need not equal EthLib’s integer-multiplication coordinates.
The live concrete projective API now uses the source GLV path. Full-integer APIs
use the source affine schedule, with their distinct full-curve contracts.

## Full-curve affine scalar path

`curve/src/scalar.rs` ports `ark-ec::sw_double_and_add_affine`: skip leading
zero bits, then double the accumulator and conditionally add the affine base.
A fixed four-word iterator replaces the source slice; no scalar reduction is
performed. `AffineScalarProof.lean` proves the exact extracted source schedule
and `AffineScalarGroupProof.lean` proves its full-curve integer action and
agreement with EthLib multiplication in the mathematical group.

Native tests compare 240 exact raw-coordinate outputs. The instrumented runner
compares 78 cases at 727,758 Fq execution boundaries, including zero, the BLS
parameter, effective cofactor, subgroup order, maximum and sampled scalars,
infinity with nonstandard stored coordinates, off-curve and torsion inputs.
The source manifest includes the scalar iterator and default affine multiplication.

`CubicRelationProof.lean` proves the geometric relation between a point and its
two endomorphism images. `G1FastSubgroupProof.lean` derives the source subgroup
criterion and proves its early-out safe. The live cofactor and subgroup paths now
use the affine helper, with complete pipelines described below.

## Shared normalization and live cofactor path

`scalar::normalize` now owns the source infinity and Z=1 shortcuts and inverse
product order. Pairing preparation, affine export and projective normalization
reuse it. `ScalarNormalizationProof.lean` proves the canonical source affine
data; `G1AffineInterpretationProof.lean` connects it to the mathematical curve
group. The shared pure affine-point model keeps field/encoding proofs independent
of the mathematical group layer.

The live `field::clear_cofactor` normalizes its input, runs the source affine
integer multiplier with h_eff, and normalizes its output. `CofactorProof.lean`
proves the exact source-coordinate model on all canonical inputs and agreement
with EthLib integer multiplication in the mathematical group on on-curve inputs.
The result uses the source normalized representation, rather than EthLib’s raw
recursive Jacobian coordinates.

Fourteen instrumented source executions match 46,089 Fq boundaries, 10,348
binary-inverse states, and raw outputs, including rescaled, infinity, off-curve,
torsion and sampled full-curve points. The source’s 56 Fr boundaries for constructing
h_eff are excluded: the extraction uses its fixed canonical integer value.

## Live fast subgroup check

The live `field::in_subgroup` now normalizes to the source affine representation,
uses the source affine integer loop for the first BLS-parameter multiplication,
retains the equality/non-infinity early-out, then uses source GLV multiplication,
negation, affine endomorphism conversion and projective equality. The second GLV
multiplication has decomposition `(X,0)`, so its correctness holds on the entire
curve before subgroup membership is known.

`G1FastSubgroupModelProof.lean` proves the complete Boolean model agrees with
EthLib's order-r test on every on-curve input. `FastSubgroupProof.lean` connects
the extracted Rust to that model. The direct API requires an on-curve input;
guarded validators establish the equation first. `DecoderCurveProof.lean` proves
that successful decompression supplies an on-curve point before subgroup checking.
The live projective equality also retains the pinned source's multiplication grouping.

Fourteen instrumented subgroup executions match 93,882 Fq boundaries and 1,522
inverse states, including rescaled, infinity, off-curve, torsion and sampled
full-curve inputs. Exact schedule comparison includes off-curve inputs, while
the mathematical subgroup equivalence requires on-curve inputs. The source's
336 Fr scalar-reduction/decomposition boundaries are excluded from the Fq trace.

## Live base-field exponentiation

`field::pow` retains ark-ff's MSB-first accumulator square/multiply order and
skips leading zero bits. A fixed six-word exponent iterator replaces its generic
slice. `FieldPowerModelProof.lean` proves the loop computes ordinary powers and
connects all 384 bits to the limb value; `FieldPowerProof.lean` proves arithmetic
safety, termination, canonical output and agreement with unchanged EthLib
`Fp.powNat` for every canonical base and every six-word exponent.

The live square-root helper consequently retains the source Case3Mod4 schedule:
power by `(p+1)/4`, square the candidate and test equality. Instrumented comparisons
check 91 powers at 146,016 boundaries and 13 square-root calls at 62,322 boundaries,
including zero, one, minus one, zero exponents, cross-word bits, maximum exponents,
the square-root exponent and sampled bases. Exact Montgomery outputs and optional
roots agree. The provenance manifest pins the source field trait and square-root
precomputation files as well as their arithmetic backends.

## Scalar API contracts and representation changes

`field::mul_256_concrete` is the specialized arkworks projective API: it reduces
the scalar and runs GLV. Its exact source-coordinate refinement holds on every
canonical input; its mathematical scalar-action theorem requires an on-curve
r-torsion point. `ScalarAPIProof.lean` owns both contracts.

The full-integer `mul_u64`, `mul_256` and `mul_compressed` APIs instead normalize
and run arkworks' affine integer loop. They preserve full unsigned integer action
on the entire curve, including non-subgroup torsion. The exported scalar functions
are specialized to this concrete field. The old generic EthLib-shaped recursive
scalar implementations and their unused halve/zero helpers are removed.

`ScalarEncodingProof.lean` proves the source affine output represents EthLib
`G1.mulNat` on on-curve inputs. `G1CompressionProof.lean` proves equal mathematical
curve points have identical affine exports and compressed bytes. This preserves
the encoded full-integer contract while allowing source Jacobian coordinates.
The source-coordinate contracts cover all canonical inputs; the EthLib group and
encoded-multiplication bridges require an on-curve input explicitly.

The three-way curve harness now checks raw Jacobian coordinates against actual
arkworks for every operation, and additionally against EthLib for non-scalar
operations. Scalar outputs retain source coordinates and compare encoded results
with EthLib. Separate intermediate tests cover 70 full-integer API calls at
765,855 Fq boundaries and 7,610 inverse states, including normalization, and call
the live projective API in the existing 78-case GLV trace suite.

## Compressed serialization and framing boundary

The live compressor normalizes to the source affine representation, computes
`y > -y`, converts x to bytes and writes the source flags in that order. The sign
is computed even for affine infinity, as in the pinned source. The formatter's
`encode_flags` is the fixed-array specialization of the three source flag stages;
its arguments flatten the source flag struct. Its totality theorem covers every
48-byte array and all eight Boolean combinations. The formatter also preserves
its documented adapter that replaces infinity's x bytes with zeros.

Actual upstream `serialize_compressed` calls match fourteen minimal executions
at 306 Fq boundaries and 1,522 inverse states, with identical output bytes. The
observer now includes native canonical-conversion rounds in whole executions,
as well as their existing dedicated round comparisons.

Arkworks' `read_g1_compressed` reads exactly 48 bytes from a stream and leaves the
suffix unread. Our source reader body takes that fixed-size array; `uncompress_g1`
and `decode_g1` add an explicit exact-length slice adapter to match EthLib's
framing. The native framing test verifies source prefix consumption and strict
slice rejection on both generator and infinity encodings with several suffixes.
The Lean decoder theorem covers arbitrary slices, including all rejected lengths;
stream I/O state is outside the fixed-array extraction boundary.

## Shared source point recovery

`field::from_x` delegates to the source `get_point_from_x_unchecked` adaptation
already used by the decoder. The source computes and sorts both roots before
selecting one; the duplicate sign-selection/equation-check implementation is
removed. `ConcretePoints.from_x_spec` now lives with that shared recovery proof.
`DecoderCurve.from_x_onCurve_spec` establishes every returned point's equation,
justifying removal of the repeated runtime curve check.

The source G1 coefficient B uses its precomputed Montgomery encoding, with
`ConcreteField.curve_b_canonical` proving the value is four. Recovery no longer
constructs that constant by runtime field conversion. Thirty-nine actual source
sorted-root and point-recovery executions match 187,695 Fq boundaries and exact
optional roots/coordinates. This includes both lexicographic root choices, zero,
one, minus one and sampled x values.

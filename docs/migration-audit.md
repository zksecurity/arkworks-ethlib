# Arkworks migration audit

The migration targets the primitives already implemented in `curve/` and
`minimal/`: BLS12-381 base/tower fields, G1 operations and scalar APIs, compressed
G1 serialization/decoding, subgroup checks, and the prepared pairing-product
endpoint. It specializes pinned arkworks 0.5.0 source and proves the adapted Rust
against unchanged EthLib. It does not extract or prove the entire arkworks crate.

Implementation and source mappings have been checked. The original migration
passed 747 curve audits; the first optional optimization adds five, and the
LSB-first alternative adds four, for 756 total.
The standalone formatter passes three audits and the published vectors pass 2,069.
Only standard Lean axioms occur.

The [CI workflow](../.github/workflows/verify.yml) runs fresh extraction,
proof audits, native comparisons and published-vector checks for code changes.

## Source and implementation checks

[The provenance manifest](../provenance/arkworks-0.5.0.json) binds 30 upstream files
to Cargo archive checksums and upstream revision metadata. Run
`python3.11 scripts/arkworks_sources.py` to check them. The detailed mapping is in
[arkworks-alignment.md](arkworks-alignment.md).

| Area | Source schedule retained | Adaptation or contract |
|---|---|---|
| Base field | Portable Montgomery multiply/square/fused products, conversion, binary inverse, MSB power and Case3Mod4 square root | Six limbs and BLS12-381 modulus fixed; canonical Montgomery inputs; inverse `None` becomes zero in the total API |
| G1 arithmetic | Projective/mixed addition, doubling, negation, normalization and cross-product equality | Mutable updates become returned values; field/curve configuration is specialized |
| Integer scalar APIs | Normalize, then source affine MSB multiplication | Four-word bound replaces slices; `mul_u64`, `mul_256` and `mul_compressed` retain full integer action on the full curve |
| Projective scalar API | Scalar reduction, signed GLV decomposition and joint source scan | `mul_256_concrete` follows the specialized BLS implementation; its scalar-action theorem requires an on-curve r-torsion input |
| GLV arithmetic | Source quotient/rounding/sign formulas and constants | Bounded integer arithmetic replaces Fr/big-integer storage. Rust refinement and mathematical reconstruction are proved; source Fr instruction traces are explicitly excluded |
| Subgroup check | Affine X multiplication, early-out, GLV X multiplication, negation and endomorphism equality | On-curve input required; the second multiplication's `(X,0)` decomposition avoids assuming subgroup membership during classification |
| Cofactor clearing | Source affine multiplication by `1-x`, then affine normalization | Effective cofactor supplied as its fixed integer; source Fr constant construction is excluded from traces |
| Serialization | Normalize, compare y with -y, convert x, write source flag stages | Fixed arrays replace writers; the flag struct becomes Boolean arguments; infinity's bytes are canonicalized |
| Recovery/decoding | Flag parsing/removal, canonical x parsing, checked square root, sorted roots and root selection | Source curve coefficient is precomputed; source recovery is shared by `from_x` and decoding; errors become `Option` |
| Framing | The source reader body consumes one 48-byte array | The slice frontend deliberately rejects lengths other than 48 to match EthLib; a native test checks upstream prefix consumption and strict suffix rejection |
| Tower fields | Source Fp2/Fp6/Fp12 dense/sparse formulas, inverse order and Frobenius tables | Fixed extension configuration; source optional inverse is adapted to the total zero convention |
| Final exponentiation | Source easy stages, Granger–Scott squares, signed NAF helper and hard chain | Source final values use the cube of EthLib's convention; the identity test is proved equivalent |
| Pairing endpoint | G1/G2 preparation, homogeneous lines, four-active-pair chunks and negative-X conjugation | Slices replace generic iterators; the EthLib Boolean bridge requires finite G2 inputs to normalize to on-curve r-torsion points; infinity inputs are handled by the endpoint |

The projective equation predicate, full-curve finite constructor, checked encoders
and public-key wrappers are project adapters with explicit validation contracts.
They are not presented as literal copies of arkworks' checked constructors.

## Proof contracts checked

- Canonical stored inputs have successful, terminating extracted computations and
  canonical outputs. Raw scalar coordinates refine source schedule models.
- Integer scalar multiplication agrees with EthLib in the mathematical curve
  group on on-curve inputs. Compression preserves that equality. Raw scalar
  coordinates need not match EthLib's different multiplication schedule.
- GLV scalar action additionally requires r-torsion. Its signed two-base action
  is proved on the entire curve, and its eigenvalue relation is proved on r-torsion.
- The fast subgroup Boolean agrees with EthLib on on-curve inputs. Guarded
  validators check the equation first; successful decoding/recovery is proved
  to establish it.
- Compressed byte decoding refines EthLib on arbitrary slices, including malformed
  inputs. Optional error variants are erased, not assumed successful.
- Prepared pairing has an exact source model on canonical slices and the original
  EthLib Boolean bridge on its declared G2 domain.

[The coverage table](proof-coverage.md) records individual functions and theorem
locations. Charon/Aeneas translation, native compilation and mathematical protocol
security remain outside the proof; executable comparisons do not replace it.

## Independent executable evidence

The runner instruments actual checksum-pinned arkworks source in an isolated
build and compares it with the minimal Rust. Observer patches are saved for
inspection. It checks operation boundaries, Montgomery limbs, carry/reduction
states and inverse states; Fr exclusions are stated separately.

The ten source-alignment instrumented tests include:

- 78 live projective GLV cases and 78 affine integer cases;
- 70 full-integer API calls: 765,855 Fq boundaries and 7,610 inverse states;
- 14 subgroup checks: 93,882 Fq boundaries and 1,522 inverse states;
- 14 cofactor calls: 46,089 Fq boundaries and 10,348 inverse states;
- 91 powers and 13 square roots: 146,016 and 62,322 boundaries;
- 14 serializations: 306 Fq boundaries and 1,522 inverse states;
- 39 sorted-root/recovery calls: 187,695 Fq boundaries;
- Montgomery, tower-field, Frobenius, cyclotomic, final-exponent and prepared
  Miller comparisons listed in the coverage table.

Two additional exponentiation tests retain the Arkworks/original trace match
while checking the first optimization and the LSB-first alternative against it.
The latter exports complete real `7^17` traces: 57 matching baseline boundaries
and 3,468 alternative boundaries with identical raw outputs.

The three-way curve harness checks 135 operations and exact arkworks Jacobian
coordinates; 64 nonscalar results additionally match EthLib coordinates. Native
tests cover invalid inputs, torsion, rescaling, infinity and framing. Published
checks include 2,069 Lean vector statements, 1,000 zkcrypto encodings and decodings,
RFC 9380 points/operations, 11 EIP-2537 multiplication vectors and 15 pairing vectors.

## Final acceptance evidence

- [x] Source mappings verify against the pinned archives.
- [x] Migrated public scalar, subgroup, serialization and recovery paths use the source routines.
- [x] Native suites, the original ten instrumented comparisons, both alternative exponentiation trace tests and three-way curve checks pass.
- [x] Current `make test` passes, including all 2,069 kernel-checked vector statements.
- [x] Standalone formatter proofs pass with implicit variables disabled and warnings treated as errors.
- [x] Final fresh curve proof rebuild passes on the complete current source snapshot (756 audits including both exponentiation examples).
- [x] Final source/proof hashes match the verified source snapshot.

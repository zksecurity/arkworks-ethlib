#!/usr/bin/env python3
"""Freshly extract and prove concrete BLS12-381 field and G1 operations against EthLib."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from differential import verify_vendor
from arkworks_sources import verify as verify_arkworks_sources
from glv_decomposition_vectors import generate as generate_glv_vectors

ROOT = Path(__file__).resolve().parents[1]
PROOF_MODULES = ('BasePrimeProof', 'ScalarPrimeProof', 'BaseFieldProof', 'LimbProof', 'MontgomeryProof', 'MontgomeryConversionProof', 'MontgomerySquareProof', 'MontgomerySquareReductionProof', 'MontgomeryFusedProof', 'FieldProof', 'FieldRefinement', 'BinaryInverseProof', 'G1AlignmentProof', 'Proof', 'ConcreteProof', 'AffinePointModel', 'ScalarNormalizationProof', 'G1EndomorphismProof', 'GLVDecompositionProof', 'GLVArithmeticProof', 'GLVScalarProof', 'GLVReductionProof', 'GLVBitProof', 'GLVLoopProof', 'CurvePredicates', 'G1CurveProof', 'GLVGroupProof', 'GLVGroupRefinementProof', 'FiniteCurveProof', 'PrimeTorsionProof', 'G1TorsionProof', 'CubicEndomorphismProof', 'G1EigenvalueProof', 'GLVCorrectnessProof', 'CubicRelationProof', 'G1FastSubgroupProof', 'AffineScalarProof', 'AffineScalarGroupProof', 'G1AffineInterpretationProof', 'CofactorProof', 'G1PointEqualityProof', 'G1ParameterMultiplicationProof', 'G1FastSubgroupModelProof', 'FastSubgroupProof', 'FieldPowerModelProof', 'FieldPowerProof', 'OptimizedFieldPowerProof', 'AlternativeFieldPowerProof', 'G1CompressionProof', 'ScalarEncodingProof', 'ScalarAPIProof', 'EncodingProof', 'G1GroupRefinementProof', 'PointProof', 'RecoveryProof', 'DecoderCurveProof', 'DecoderProof', 'ExtensionAlignmentProof', 'Fp2FieldProof', 'Fp2DomainProof', 'Fp6FieldProof', 'Fp6FrobeniusProof', 'CubicNonresidueProof', 'Fp6DomainProof', 'ExtensionProof', 'PreparedLineProof', 'PreparedG2Proof', 'PreparedGeometryProof', 'PreparedPrefixProof', 'PreparedProjectiveProof', 'Fp6FrobeniusRefinement', 'Fp12FieldProof', 'Fp12FrobeniusProof', 'DodecicNonresidueProof', 'Fp12DomainProof', 'Fp12FrobeniusRefinement', 'TowerInverseProof', 'TowerFieldInverseProof', 'CyclotomicProof', 'CyclotomicSquareProof', 'CyclotomicSquareRefinement', 'CyclotomicExponentRefinement', 'CyclotomicRefinement', 'HardExponentProof', 'FinalScalingProof', 'CyclotomicParameterProof', 'CyclotomicParameterRefinement', 'HardChainProof', 'HardChainRefinement', 'EthLibPairingProduct', 'PairingCheckProof', 'PreparedMillerProof', 'PreparedPairingProof', 'PreparedLineGeometryProof', 'PreparedMillerStepProof', 'PreparedReferenceWalkProof', 'PreparedChunkAlgebraProof', 'PreparedCoefficientWalkProof', 'PreparedCurveGroupProof', 'PreparedSafetyProof', 'PreparedPairingEquivalence')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    tool = Path(os.environ.get("AENEAS_DIR", ROOT / ".tools/aeneas")).resolve()
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="curve-", dir=build))
    rust = work / "rust"
    rust.mkdir()
    for name in ("Cargo.toml", "Cargo.lock"):
        shutil.copyfile(ROOT / "curve" / name, rust / name)
    shutil.copytree(ROOT / "curve/src", rust / "src")
    minimal = work / "minimal"
    minimal.mkdir()
    shutil.copyfile(ROOT / "minimal/Cargo.toml", minimal / "Cargo.toml")
    shutil.copytree(ROOT / "minimal/src", minimal / "src")
    for module in PROOF_MODULES:
        shutil.copyfile(ROOT / "curve" / f"{module}.lean", work / f"{module}.lean")
    report_path = build / "curve-proof.json"
    report = {
        "status": "running", "work_directory": str(work.relative_to(ROOT)),
        "scope": "concrete field/G1, compression, subgroup and pairing checks directly refine pinned EthLib",
        "pairing_proof_target": "EthLib.Cryptography.Bls.pairingCheck",
        "ethlib_manifest_sha256": digest(ROOT / "lean/vendor/ethlib/provenance.json"),
        "precondition": "each stored input coordinate is a Montgomery residue less than the BLS12-381 base-field modulus; decode multiplies by R inverse; the direct fast subgroup API additionally requires an on-curve input (guarded validators and byte decoding establish it); the default pairing additionally requires the declared finite-G2 subgroup domain",
        "postcondition": "termination, canonical intermediate results, exact field/G1 results, and pairing Boolean agreement with current EthLib on the declared finite-G2 subgroup domain",
        "concrete_backend_extracted": False,
        "concrete_field_arithmetic_proved": False,
        "full_arkworks_equivalence_proved": False,
        "g1_endomorphism_coordinate_refinement_proved": False,
        "g1_glv_eigenvalue_relation_proved": False,
        "g1_fast_subgroup_criterion_proved": False,
        "g1_live_fast_subgroup_refinement_proved": False,
        "base_field_source_power_refinement_proved": False,
        "optimized_field_power_refinement_proved": False,
        "alternative_field_power_refinement_proved": False,
        "affine_scalar_source_schedule_refinement_proved": False,
        "affine_scalar_full_curve_action_proved": False,
        "shared_g1_source_normalization_proved": False,
        "source_cofactor_refinement_proved": False,
        "source_cofactor_ethlib_group_bridge_proved": False,
        "g1_mathematical_group_bridge_proved": False,
        "g1_torsion_generator_characterization_proved": False,
        "g1_generator_eigenvalue_proved": False,
        "glv_decomposition_arithmetic_proved": False,
        "glv_decomposition_rust_refinement_proved": False,
        "glv_scalar_reduction_refinement_proved": False,
        "glv_point_source_schedule_refinement_proved": False,
        "glv_point_ethlib_multiplication_bridge_proved": False,
        "glv_point_signed_group_action_proved": False,
        "glv_point_correctness_under_eigenvalue_contract_proved": False,
        "glv_point_scope": "canonical G1 coordinates, all unsigned four-word scalar inputs: reduction modulo r, signed source decomposition, exact 256-bit source GLV schedule including skip flag and canonical output; signed two-base mathematical group action proved on on-curve inputs; scalar-action correctness and agreement with EthLib integer multiplication in the mathematical curve group proved on on-curve r-torsion inputs; Jacobian coordinates follow the source schedule; the concrete projective API now uses this path; full-integer APIs use the source affine schedule",
        "glv_decomposition_rust_scope": "all four-word inputs: canonical inputs terminate with exact source-model signs and magnitudes; noncanonical inputs return None; bounded division/multiplication, strict rounding, signed magnitude conversion and output truncation proved; the G1 group and signed source-loop bridges are proved; the subgroup eigenvalue relation is proved; the concrete projective API now uses the source GLV path; full-integer APIs normalize and use the source affine schedule",
        "glv_decomposition_arkworks_vectors_kernel_checked": False,
        "binary_inverse_refinement_proved": False,
        "fp2_frobenius_refinement_proved": False,
        "fp6_frobenius_refinement_proved": False,
        "fp12_frobenius_refinement_proved": False,
        "live_final_exponent_frobenius_p2_proved": False,
        "tower_inverse_zero_or_unit_proved": False,
        "tower_field_structures_proved": False,
        "tower_executable_field_inverse_agreement_proved": False,
        "live_easy_stage_cyclotomic_precondition_proved": False,
        "hard_chain_cube_identity_bridge_proved": False,
        "optimized_hard_chain_refinement_proved": False,
        "signed_parameter_source_refinement_proved": False,
        "prepared_line_source_refinement_proved": False,
        "prepared_g2_source_refinement_proved": False,
        "prepared_projective_refinement_proved": False,
        "prepared_miller_source_refinement_proved": False,
        "prepared_pairing_source_refinement_proved": False,
        "prepared_pairing_ethlib_bridge_proved": False,
        "prepared_subgroup_safety_proved": False,
        "default_pairing_uses_prepared_path": False,
        "prepared_pairing_ethlib_domain": "canonical coordinates; each finite G2 normalizes to an on-curve point on y^2=x^3+(4+4i) killed by Fr.modulus in the proved curve group; infinity pairs are skipped; external validation is not proved here",
        "prepared_local_ethlib_steps_proved": False,
        "prepared_conditional_reference_walk_proved": False,
        "prepared_chunk_product_proved": False,
        "prepared_coefficient_walk_proved": False,
        "prepared_local_geometry_proved": False,
        "prepared_prefix_coprime_factors_proved": False,
        "final_exponent_scaling_invariance_proved": False,
        "prepared_pairing_scope": "complete source-scheduled preparation, four-pair Miller loop and prepared pairing endpoint proved over unchanged EthLib field/final-exponent arithmetic; exact original EthLib pairingCheck agreement on the stated finite-G2 mathematical subgroup domain; the default Rust entry point delegates to the prepared source path; the superseded reference Rust loop is removed",
        "signed_parameter_power_refinement_proved": False,
        "cyclotomic_square_refinement_proved": False,
        "live_hard_chain_cyclotomic_squares_proved": False,
        "hard_chain_scope": "live source-scheduled arkworks signed-NAF hard chain; complete operation-to-exponent proof and cubed EthLib final-value contract; executable pairing Boolean unchanged",
        "binary_inverse_scope": "source-specialized arkworks binary-GCD inverse; normalization and outer-loop termination, coefficient invariants, and EthLib refinement; used by live Fp::inverse",
        "mul_256_refinement_proved": False,
        "compressed_decoder_refinement_proved": False,
        "decoder_contract": "all byte slices; Option point and rejection agreement, not EthLib error variants",
        "source_sha256": {str(p.relative_to(work)): digest(p) for p in
                          [rust / "src/alternative/mod.rs", rust / "src/alternative/field_power.rs", rust / "src/optimized/mod.rs", rust / "src/optimized/field_power.rs", rust / "src/scalar.rs", rust / "src/glv/arithmetic.rs", rust / "src/glv.rs", rust / "src/lib.rs", rust / "src/field.rs", rust / "src/field/inversion.rs", rust / "src/decoder.rs", rust / "src/montgomery.rs", rust / "src/pairing.rs", rust / "src/pairing/prepared.rs", rust / "src/pairing/prepared_miller.rs", minimal / "src/lib.rs",
                           rust / "Cargo.toml", rust / "Cargo.lock", minimal / "Cargo.toml"] +
                          [work / f"{module}.lean" for module in PROOF_MODULES]},
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    env = dict(os.environ, CARGO_HOME=str(ROOT / ".cache/cargo"),
               LEAN_PATH=os.pathsep.join((str(work), str(ROOT / "lean/.lake/build/lib/lean"))))
    generated = work / "Generated/CurveG1.lean"
    log_path = build / "curve-proof.log"
    try:
        report["ethlib_revision"] = verify_vendor()["revision"]
        report["arkworks_source_files_verified"] = verify_arkworks_sources()
        report["arkworks_source_manifest_sha256"] = digest(ROOT / "provenance/arkworks-0.5.0.json")
        report["base_prime_certificate_sha256"] = digest(ROOT / "provenance/bls12-381-base-prime.json")
        report["scalar_prime_certificate_sha256"] = digest(ROOT / "provenance/bls12-381-scalar-prime.json")
        with log_path.open("w") as log:
            def run(cwd, command):
                print("Running:", " ".join(map(str, command)), file=log, flush=True)
                subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                               stdout=log, stderr=subprocess.STDOUT, check=True, timeout=180)

            run(ROOT, [sys.executable, "scripts/generate_base_prime.py", "--check"])
            run(ROOT, [sys.executable, "scripts/generate_base_prime.py", "--scalar", "--check"])
            run(ROOT, [sys.executable, "scripts/extract.py", "--check"])
            run(ROOT / "lean", ["lake", "build"])
            run(rust, [tool / "charon/bin/charon", "cargo", "--preset=aeneas",
                       "--error-on-warnings", "--include", "minimal_g1", "--dest-file", work / "curve_g1.llbc",
                       "--", "--lib", "--offline", "--locked"])
            run(work, [tool / "bin/aeneas", "-backend", "lean", work / "curve_g1.llbc",
                       "-dest", work, "-subdir", "Generated", "-namespace", "CurveG1"])
            if list((work / "Generated").glob("*.lean")) != [generated]:
                raise RuntimeError("Unexpected generated modules or external templates")
            for source in [generated] + [work / f"{module}.lean" for module in PROOF_MODULES]:
                if re.search(r"\b(sorry|admit|axiom|native_decide)\b", source.read_text()):
                    raise RuntimeError(f"Unreviewed proof shortcut in {source}")
            run(tool / "backends/lean", ["lake", "env", "lean", f"--root={work}",
                                        "-o", generated.with_suffix(".olean"), generated])
            report["concrete_backend_extracted"] = True
            for module in PROOF_MODULES:
                flags = ["-DautoImplicit=false", "-DwarningAsError=true"] if module in ("BasePrimeProof", "ScalarPrimeProof", "BaseFieldProof", "BinaryInverseProof", "ExtensionAlignmentProof", "Fp2FieldProof", "Fp2DomainProof", "Fp6FieldProof", "Fp6FrobeniusProof", "CubicNonresidueProof", "Fp6DomainProof", "Fp6FrobeniusRefinement", "Fp12FieldProof", "Fp12FrobeniusProof", "DodecicNonresidueProof", "Fp12DomainProof", "Fp12FrobeniusRefinement", "TowerInverseProof", "TowerFieldInverseProof", "CyclotomicProof", "CyclotomicSquareProof", "CyclotomicSquareRefinement", "CyclotomicExponentRefinement", "CyclotomicRefinement", "HardExponentProof", "FinalScalingProof", "CyclotomicParameterProof", "CyclotomicParameterRefinement", "HardChainProof", "HardChainRefinement", "ExtensionProof", "PreparedLineProof", "PreparedG2Proof", "PreparedGeometryProof", "PreparedPrefixProof", "PreparedProjectiveProof", "G1AlignmentProof", "Proof", "DecoderCurveProof", "DecoderProof", "MontgomeryProof", "MontgomeryConversionProof", "MontgomerySquareProof", "MontgomerySquareReductionProof", "MontgomeryFusedProof", "FieldProof", "FieldRefinement", "ConcreteProof", "AffinePointModel", "ScalarNormalizationProof", "G1EndomorphismProof", "GLVDecompositionProof", "GLVArithmeticProof", "GLVScalarProof", "GLVReductionProof", "GLVBitProof", "GLVLoopProof", "CurvePredicates", "G1PointEqualityProof", "G1ParameterMultiplicationProof", "G1FastSubgroupModelProof", "FastSubgroupProof", "FieldPowerModelProof", "FieldPowerProof", "OptimizedFieldPowerProof", "AlternativeFieldPowerProof", "G1CompressionProof", "ScalarEncodingProof", "EncodingProof", "G1CurveProof", "G1GroupRefinementProof", "GLVGroupProof", "GLVGroupRefinementProof", "FiniteCurveProof", "PrimeTorsionProof", "G1TorsionProof", "CubicEndomorphismProof", "G1EigenvalueProof", "GLVCorrectnessProof", "ScalarAPIProof", "CubicRelationProof", "G1FastSubgroupProof", "AffineScalarProof", "AffineScalarGroupProof", "G1AffineInterpretationProof", "CofactorProof", "PointProof", "RecoveryProof", "EthLibPairingProduct", "PairingCheckProof", "PreparedMillerProof", "PreparedPairingProof", "PreparedLineGeometryProof", "PreparedMillerStepProof", "PreparedReferenceWalkProof", "PreparedChunkAlgebraProof", "PreparedCoefficientWalkProof", "PreparedCurveGroupProof", "PreparedSafetyProof", "PreparedPairingEquivalence") else []
                run(tool / "backends/lean", ["lake", "env", "lean", *flags, f"--root={work}",
                                            "-o", work / f"{module}.olean", work / f"{module}.lean"])
            run(ROOT, [sys.executable, "scripts/offline_cargo.py", "build", "--release",
                       "--config", "profile.release.overflow-checks=true", "--bin", "glv_decomposition_vectors"])
            glv_modules, glv_names, glv_report = generate_glv_vectors(work)
            report["glv_decomposition_vectors"] = glv_report
            for module in glv_modules:
                run(tool / "backends/lean", ["lake", "env", "lean", "-DautoImplicit=false",
                                            "-DwarningAsError=true", f"--root={work}", module])
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log_path.read_text())
        audits += [(name, "") for name in re.findall(
            r"'([^']+)' does not depend on any axioms", log_path.read_text())]
        if len(audits) != len({name for name, _ in audits}):
            raise RuntimeError("Duplicate theorem axiom audit")
        required = {f"CurveProof.{op}_refines" for op in ("identity", "negate", "double", "add_general", "add_mixed", "add", "mul_u64")}
        required |= {f"G1Endomorphism.{op}" for op in
                     ("beta_canonical", "beta_cube", "beta_ne_one", "map_three", "mapped_cube", "equation",
                      "projective_spec", "affine_spec")}
        required |= {f"G1Curve.{op}" for op in
                     ('inSubgroup_iff', 'onCurve_iff', 'interpret_eq_zero_iff', 'mulNat_correct', 'general_coords', 'interpret_eq_of_XY', 'general_correct', 'add_cases', 'add_onCurve', 'interpret_add', 'isZero_iff', 'double_coords', 'double_onCurve', 'interpret_double', 'equation_iff', 'nonsingular_finite', 'interpret_infinity', 'interpret_nonzero', 'interpret_zero', 'neg_coords', 'neg_onCurve', 'interpret_neg')}
        required |= {"G1GroupRefinement.mul_u64_spec", "G1GroupRefinement.mul_256_spec", "G1GroupRefinement.subgroup_spec"}
        required |= {f"GLVGroup.{op}" for op in
                     ("low_bits_succ", "loop_false", "joint_scan", "endomorphism_onCurve",
                      "mul_decomposed", "mul_projective_components", "mul_projective_correct")}
        required |= {"GLVGroupRefinement.mul_projective_components_spec",
                     "GLVGroupRefinement.mul_projective_spec"}
        required |= {f"FiniteCurve.{op}" for op in
                     ("finite_points", "fiber_card_le_three", "card_le_three_mul")}
        required.add("PrimeTorsion.mem_zmultiples_of_card_lt_sq")
        required |= {f"G1Torsion.{op}" for op in
                     ("point_card_bound", "point_card_lt_order_sq", "generator_onCurve", "generator_nonzero",
                      "generator_inSubgroup", "generator_killed", "generator_order", "torsion_mem_generator",
                      "generator_eigenvalue")}
        required |= {f"CubicEndomorphism.{op}" for op in
                     ("nonsingular_map", "slope_map", "addX_map", "addY_map", "map_add", "hom")}
        required |= {f"G1Eigenvalue.{op}" for op in ("hom_raw", "hom_generator", "hom_torsion", "eigenvalue")}
        required |= {f"GLVCorrectness.{op}" for op in
                     ("mul_projective_correct", "ethlib_mul_equiv", "mul_projective_spec")}
        required.add("CubicRelation.add_map")
        required |= {f"G1FastSubgroup.{op}" for op in
                     ("parameter_square", "quadratic_relation", "criterion_iff", "parameter_coprime", "early_out_safe")}
        required |= {f"ConcreteAffineScalar.{op}" for op in ("affine_loop_spec", "mul_affine_spec")}
        required |= {f"AffineScalarGroup.{op}" for op in
                     ("loop_started", "loop_initial", "mul_affine_correct", "ethlib_mul_equiv", "mul_affine_spec")}
        required |= {f"G1AffineInterpretation.{op}" for op in
                     ("toAffine_finite", "normalized_correct", "affine_data_onCurve", "baseAction_toAffine")}
        required |= {f"ConcreteNormalization.{op}" for op in
                     ("normalize_spec", "projective_from_affine_spec", "normalize_projective_spec", "normalize_projective_group_spec")}
        required |= {"SourceCofactor.model_correct", "ConcreteCofactor.clear_cofactor_projective_spec",
                     "ConcreteCofactor.clear_cofactor_group_spec"}
        required |= {f"G1PointEquality.{op}" for op in ("finite_iff", "model_iff")}
        required |= {f"G1ParameterMultiplication.{op}" for op in ("parameter_components", "glv_parameter_correct")}
        required |= {f"SourceFastSubgroup.{op}" for op in
                     ("first_correct", "negative_second_correct", "endomorphism_correct", "model_iff", "ethlib_equiv")}
        required |= {f"ConcreteFastSubgroup.{op}" for op in ("points_equal_spec", "source_spec", "ethlib_spec")}
        required |= {f"DecoderCurve.{op}" for op in ("recover_onCurve", "uncompress_onCurve", "from_x_onCurve_spec")}
        required |= {f"SourceFieldPower.{op}" for op in
                     ("loop_started", "loop_initial", "exponent_word", "exponent_testBit")}
        required |= {f"ConcreteFieldPower.{op}" for op in ("exponent_bit_spec", "pow_loop_spec", "pow_spec")}
        required |= {f"G1Compression.{op}" for op in ("infinity_eq", "affine_eq", "compress_eq")}
        required |= {f"ScalarEncoding.{op}" for op in ("integer_correct", "integer_compressed", "glv_compressed")}
        required.add("ConcreteEncoding.mul_compressed_source_spec")
        required.add("ConcreteEncoding.encode_flags_total")
        required.add("ConcreteCurve.mul_256_group_spec")
        required |= {f"OptimizedFieldPower.{op}" for op in
                     ("exponent_bit_spec", "pow_loop_spec", "pow_spec", "same_montgomery_value", "equivalence_spec")}
        required |= {f"AlternativeFieldPower.{op}" for op in
                     ("exponent_bit_spec", "pow_loop_spec", "pow_spec", "equivalence_spec")}
        required.add("ScalarPrime.modulus_prime")
        required |= set(glv_names)
        required |= {f"GLVDecomposition.{op}" for op in
                     ("lattice_determinant", "eigenvalue_eq", "order_pos", "reconstruction",
                      "second_quotient_zero", "canonical_components", "component_bounds",
                      "signed_magnitude_value", "magnitude_bounds", "group_reconstruction")}
        required |= {f"GLVArithmetic.{op}" for op in
                     ("order_value", "multiply_128_spec", "div_rem_spec", "rounded_quotient_spec")}
        required |= {f"ConcreteGLV.{op}" for op in
                     ("rounded_eq", "rounded_bounds", "signed_difference_spec",
                      "scalar_decomposition_nat_spec", "model_observation", "scalar_decomposition_spec",
                      "scalar_decomposition_reject", "scalar_decomposition_total_spec")}
        required |= {f"ConcreteGLV.{op}" for op in
                     ("scalar_bound", "reduce_scalar_spec", "scalar_word", "scalar_testBit",
                      "scalar_bit_spec", "loop_bits_spec", "mul_decomposed_spec", "mul_projective_spec")}
        required |= {f"BaseField.{op}" for op in
                     ("powNat_eq_pow", "inverse_mul", "inverse_unique", "inverse_zero", "double_cancel")}
        required |= {f"BinaryInverse.{op}" for op in
                     ("is_one_spec", "half_coefficient_spec", "half_coefficient_field_spec",
                      "normalize_spec", "normalize_second_spec", "inverse_body_spec", "inverse_loop_spec", "inverse_spec")}
        required |= {f"QuadraticField.{op}" for op in
                     ("ringStructure", "ofFpHom", "characteristic", "powNat_eq_pow", "pow_modulus", "pow_modulus_pow", "conjugate_mul", "power_step")}
        required |= {f"QuadraticDomain.{op}" for op in
                     ("fieldStructure", "norm_eq_zero", "norm_mul", "inverse_mul", "inverse_eq")}
        required |= {f"CubicField.{op}" for op in
                     ("ringStructure", "ofFp2Hom", "characteristic", "pow_modulus", "v_cube", "sub_eq_add_neg", "mulByV_eq", "mul_ofFp2")}
        required |= {f"CubicFrobenius.{op}" for op in
                     ("xi_power", "coefficient_step", "map_eq_power")}
        required |= {f"CubicDomain.{op}" for op in
                     ("fieldStructure", "quotientEquiv", "domainStructure")}
        required |= {f"CubicNonresidue.{op}" for op in
                     ("xi_character", "no_cube", "irreducible")}
        required |= {f"PreparedGeometry.{op}" for op in
                     ("double_z", "add_z", "double_onCurve", "double_x_cross", "source_half",
                      "double_z_nonzero", "double_affine_x", "double_y_cross", "double_affine_y",
                      "add_z_nonzero", "add_affine_x", "add_affine_y", "affine_x_ne", "add_slope")}
        required |= {f"PreparedPrefix.{op}" for op in
                     ("factors_coprime", "nsmul_nonzero", "factors_nonzero")}
        required |= {f"FinalScaling.{op}" for op in
                     ("easy_mul", "middle_mul", "final_mul", "middle_of_conjugate_eq_neg",
                      "final_of_conjugate_eq_neg", "final_scale", "final_one", "final_pow",
                      "final_conjugate", "lineFactor_nonzero", "lineFactor_conjugate", "final_lineFactor")}
        required.add("ConcreteFrobenius.fp6_frobenius_spec")
        required |= {f"DodecicField.{op}" for op in
                     ("ringStructure", "ofFp6Hom", "characteristic", "pow_modulus", "powNat_eq_pow")}
        required |= {f"DodecicFrobenius.{op}" for op in
                     ("xi_power", "coefficient_step", "map_eq_power")}
        required |= {f"DodecicNonresidue.{op}" for op in
                     ("v_character", "pow_card", "no_square", "irreducible")}
        required |= {f"DodecicDomain.{op}" for op in
                     ("fieldStructure", "quotientEquiv", "domainStructure")}
        required.add("ConcreteFrobenius.fp12_frobenius_spec")
        required |= {f"TowerFieldInverse.{op}" for op in
                     ("adjugate_nonzero", "fp6_determinant_nonzero", "fp6_inverse_mul",
                      "fp12_norm_nonzero", "fp12_inverse_mul", "fp6_inverse_eq", "fp12_inverse_eq")}
        required |= {f"TowerInverse.{op}" for op in
                     ("fp2_inverse_or_unit", "fp6_inverse_or_unit", "fp12_inverse_or_unit")}
        required |= {f"Cyclotomic.{op}" for op in
                     ("conjugate_mul", "conjugate_conjugate", "conjugate_one", "power_six",
                      "easy_zero_or_unitary", "middle_zero_or_cyclotomic")}
        required.add("ConcreteCyclotomic.easy_spec")
        required |= {f"HardExponent.{op}" for op in
                     ("naf_value", "chain_exponent", "hard_times_order", "final_eq_middle_power", "final_zero_or_order",
                      "cube_eq_one_iff", "final_cube_eq_one_iff", "isOne_iff", "final_cube_isOne")}
        required |= {f"CyclotomicSquare.{op}" for op in
                     ("power_two", "power_four", "square_correct", "characteristic_guard", "square_zero",
                      "square_correct_on_domain", "squared_admissible")}
        required |= {f"ConcreteCyclotomicSquare.{op}" for op in ("source_spec", "square_spec")}
        required |= {f"ConcreteCyclotomicExponent.{op}" for op in
                     ("one_spec", "digits_spec", "absolute_source_spec", "signed_source_spec")}
        required |= {f"CyclotomicParameter.{op}" for op in
                     ("unitary", "power_root", "conjugate_power", "exponent_certificate", "absolute_power",
                      "power_admissible", "conjugate_admissible", "product_admissible")}
        required |= {f"ConcreteCyclotomicParameter.{op}" for op in ("absolute_spec", "signed_spec")}
        required |= {f"HardChain.{op}" for op in ("exponent_residue", "chain_correct")}
        required |= {f"ConcreteHardChain.{op}" for op in ("source_spec", "hard_spec")}
        required |= {f"ConcretePreparedLine.{op}" for op in
                     ("coefficient_spec", "double_spec", "add_spec", "ell_spec")}
        required |= {f"PreparedLine.{op}" for op in ("remaining_step", "remaining_positive", "remaining_full", "lines_length", "prepared_length", "prepare_length")}
        required |= {f"ConcretePreparedG2.{op}" for op in ("bits_spec", "prepare_spec")}
        required |= {f"ConcretePreparedProjective.{op}" for op in
                     ("one_spec", "g1_spec", "normalize_g2_spec", "prepare_g2_spec")}
        required |= {f"ConcretePreparedMiller.{op}" for op in
                     ("eval_lines_spec", "chunk_bits_spec", "chunks_spec", "collect_spec", "multi_miller_loop_spec", "pairing_check_spec")}
        required.add("BasePrime.modulus_prime")
        required |= {f"G1Alignment.{op}" for op in ("general_eq_mixed", "add_projective")}
        required |= {f"ConcreteField.{op}_spec" for op in
                     ("constant", "plus", "minus", "times", "square", "sum_products", "negative", "equal", "is_zero")}
        required.add("ConcreteField.from_limbs_correct")
        required.add("ConcreteField.montgomery_one")
        required.add("ConcreteField.curve_b_canonical")
        required |= {f"ConcreteCurve.{op}_spec" for op in
                     ("identity", "negate", "double", "add_general", "add_mixed", "add", "add_affine", "mul_u64", "mul_256")}
        required |= {f"ConcreteCurve.{op}_correct" for op in
                     ("generator", "negate", "double", "add", "mul_u64", "mul_256")}
        required |= {f"ConcreteEncoding.{op}_spec" for op in
                     ("pow", "inverse", "sign", "affine", "bytes", "compress", "subgroup",
                      "on_curve", "valid_subgroup", "public_key")}
        required.add("ConcreteEncoding.mul_compressed_correct")
        required |= {f"ConcretePoints.{op}_spec" for op in
                     ("sqrt", "from_affine", "normalize", "points_equal", "compress_checked", "compress_public_key", "from_x", "clear_cofactor")}
        required |= {"ConcretePoints.sqrt_sound", "ConcretePoints.from_affine_on_curve"}
        required |= {f"MontgomeryProof.{op}" for op in
                     ("mac_spec", "round_equation", "round_spec", "reduce_spec", "multiply_spec", "multiply_value", "radix_inverse", "r_constant", "r2_constant")}
        required |= {f"MontgomerySquare.{op}" for op in
                     ("square_product_spec", "square_identity", "product_no_overflow", "square_diagonal_spec", "square_double_spec", "square_cross_spec", "wide_bound", "adc_word_spec")}
        required |= {f"MontgomerySquareReduction.{op}" for op in
                     ("square_value", "square_body", "square_tail_spec", "extract_high_spec",
                      "six_rounds_spec", "reduction_bounds", "reduction_telescope", "reduction_round_spec")}
        required |= {f"MontgomeryFused.{op}" for op in
                     ("sum_products_value", "telescope", "final_bound", "round_equation", "accumulate_spec")}
        required |= {f"FieldProof.{op}" for op in
                     ("from_limbs_spec", "to_limbs_spec", "constant_spec", "plus_spec", "minus_spec", "times_spec", "square_spec", "sum_products_spec", "negative_spec", "equal_spec", "is_zero_spec")}
        required |= {f"MontgomeryConversion.{op}" for op in
                     ("conversion_equation", "conversion_round_spec", "into_canonical_spec", "from_canonical_spec")}
        required |= {f"ConcreteRecovery.{op}" for op in
                     ("sign_inverse", "select_sorted", "ys_spec", "point_spec")}
        required |= {"ConcreteDecoder.flags_spec", "ConcreteDecoder.remove_flags_spec"}
        required |= {f"ConcreteDecoder.{op}_spec" for op in
                     ("field_from_bytes", "uncompress", "decode", "decode_public_key")}
        required |= {f"ExtensionAlignment.{op}" for op in
                     ("cubic_square", "cubic_product", "cubic_inverse_core", "cubic_inverse_zero", "cubic_is_zero", "quadratic_product", "quadratic_square", "quadratic_inverse_zero", "quadratic_is_zero", "cubic_sparse_one", "cubic_sparse_pair", "quadratic_sparse014")}
        required |= {f"ConcreteExtension.{op}" for op in
                     ('fp2_of_fp_spec', 'fp2_zero_spec', 'fp2_one_spec', 'fp2_plus_spec', 'fp2_minus_spec', 'fp2_negative_spec', 'fp2_times_spec', 'fp2_mul_by_fp_spec', 'fp2_square_spec', 'fp2_inverse_spec', 'fp2_frobenius_spec', 'fp2_mul_xi_spec', 'fp2_equal_spec', 'fp2_is_zero_spec', 'fp6_of_fp2_spec', 'fp6_zero_spec', 'fp6_one_spec', 'fp6_plus_spec', 'fp6_minus_spec', 'fp6_negative_spec', 'fp6_times_spec', 'fp6_square_spec', 'fp6_mul_by_1_spec', 'fp6_mul_by_01_spec', 'fp6_inverse_spec', 'fp6_mul_v_spec', 'fp6_equal_spec', 'fp6_is_zero_spec', 'fp12_of_fp2_spec', 'fp12_zero_spec', 'fp12_one_spec', 'fp12_plus_spec', 'fp12_minus_spec', 'fp12_negative_spec', 'fp12_times_spec', 'fp12_square_spec', 'fp12_mul_by_014_spec', 'fp12_is_zero_spec', 'fp12_inverse_spec', 'fp12_conjugate_spec', 'fp12_equal_spec', 'fp12_is_one_spec')}
        required |= {f"PreparedLineGeometry.{op}" for op in
                     ("sparse_eq", "factor_eq", "sparse_line", "add_line", "double_line", "w_square",
                      "wInv2_eq", "wInv3_eq", "add_line_final", "double_line_final", "eval_eq_evalAt",
                      "add_slope_eq", "double_slope_affine", "double_slope_eq", "add_line_ethlib", "double_line_ethlib")}
        required |= {f"PreparedMillerStep.{op}" for op in
                     ("double_state", "add_state", "double_value", "add_value")}
        required |= {f"PreparedReferenceWalk.{op}" for op in ("parameter_eq", "walk_refines")}
        required |= {f"PreparedChunkAlgebra.{op}" for op in
                     ("eval_append_product", "chunk_append_product", "chunk_product", "chunks_product")}
        required |= {f"PreparedCurve.{op}" for op in
                     ("ellipticStructure", "equation_iff", "onCurve_iff", "point_nonzero", "y_nonzero",
                      "point_double", "add_coordinates", "add_onCurve", "point_add")}
        required |= {f"PreparedSafety.{op}" for op in ("safe_of_factors", "safe_affine")}
        required |= {f"PreparedPairingEquivalence.{op}" for op in
                     ("bit_count", "finite_pair", "final_product", "check_eq_ethlib")}
        required.add("ConcretePreparedMiller.pairing_check_ethlib_spec")
        required |= {f"PreparedCoefficientWalk.{op}" for op in ("chunk_eq_walk", "chunk_refines_ethlib")}
        required |= {f"ConcretePairing.{op}" for op in
                     ("final_exponentiation_cube_spec", "pairing_check_fold")}
        required.add("ConcretePreparedMiller.default_pairing_check_ethlib_spec")
        audited = {name for name, _ in audits}
        if audited != required:
            raise RuntimeError(f"Theorem audit mismatch: missing={sorted(required - audited)}, "
                               f"unexpected={sorted(audited - required)}")
        for name, axioms in audits:
            used = set(axioms.split(", ")) if axioms else set()
            if not used.issubset({"propext", "Classical.choice", "Quot.sound"}):
                raise RuntimeError(f"Unexpected axioms in {name}: {axioms}")
        report.update(status="passed", generated_sha256=digest(generated),
                      g1_endomorphism_coordinate_refinement_proved=True, g1_glv_eigenvalue_relation_proved=True,
                      g1_fast_subgroup_criterion_proved=True, g1_live_fast_subgroup_refinement_proved=True,
                      base_field_source_power_refinement_proved=True, optimized_field_power_refinement_proved=True, alternative_field_power_refinement_proved=True, affine_scalar_source_schedule_refinement_proved=True,
                      affine_scalar_full_curve_action_proved=True, shared_g1_source_normalization_proved=True,
                      source_cofactor_refinement_proved=True, source_cofactor_ethlib_group_bridge_proved=True,
                      glv_point_ethlib_multiplication_bridge_proved=True,
                      glv_decomposition_arithmetic_proved=True,
                      glv_decomposition_rust_refinement_proved=True,
                      glv_scalar_reduction_refinement_proved=True,
                      glv_point_source_schedule_refinement_proved=True,
                      glv_decomposition_arkworks_vectors_kernel_checked=True,
                      base_field_modulus_prime_proved=True, fermat_inverse_mathematically_correct_proved=True,
                      binary_inverse_local_helpers_proved=True, binary_inverse_refinement_proved=True,
                      fp2_frobenius_refinement_proved=True, fp6_frobenius_refinement_proved=True, fp12_frobenius_refinement_proved=True,
                      live_final_exponent_frobenius_p2_proved=True, tower_inverse_zero_or_unit_proved=True,
                      tower_field_structures_proved=True, tower_executable_field_inverse_agreement_proved=True,
                      live_easy_stage_cyclotomic_precondition_proved=True, hard_chain_cube_identity_bridge_proved=True,
                      cyclotomic_square_refinement_proved=True, live_hard_chain_cyclotomic_squares_proved=True, signed_parameter_source_refinement_proved=True,
                      signed_parameter_power_refinement_proved=True, optimized_hard_chain_refinement_proved=True,
                      prepared_line_source_refinement_proved=True, prepared_g2_source_refinement_proved=True,
                      prepared_projective_refinement_proved=True, prepared_miller_source_refinement_proved=True,
                      prepared_pairing_source_refinement_proved=True, prepared_pairing_ethlib_bridge_proved=True,
                      prepared_subgroup_safety_proved=True, default_pairing_uses_prepared_path=True,
                      prepared_local_ethlib_steps_proved=True, prepared_conditional_reference_walk_proved=True,
                      prepared_chunk_product_proved=True, prepared_coefficient_walk_proved=True,
                      prepared_local_geometry_proved=True, prepared_prefix_coprime_factors_proved=True,
                      final_exponent_scaling_invariance_proved=True,
                      concrete_field_arithmetic_proved=True, concrete_curve_refinement_proved=True,
                      mul_256_refinement_proved=True, point_to_bytes_refinement_proved=True,
                      mul_to_bytes_refinement_proved=True, subgroup_refinement_proved=True, point_validation_refinement_proved=True, checked_point_operations_proved=True,
                      extension_field_refinement_proved=True, pairing_steps_refinement_proved=True,
                      full_pairing_refinement_proved=True, compressed_decoder_refinement_proved=True,
                      montgomery_multiplication_proved=True, montgomery_field_backend_integrated=True,
                      square_product_prefix_proved=True, montgomery_squaring_proved=True, montgomery_fused_products_proved=True,
                      mathematical_field_refinement_proved=True, g1_mathematical_group_bridge_proved=True,
                      g1_torsion_generator_characterization_proved=True, g1_generator_eigenvalue_proved=True,
                      glv_point_signed_group_action_proved=True,
                      glv_point_correctness_under_eigenvalue_contract_proved=True,
                      axiom_audit=dict(audits))
        print("PASS: concrete curve/field Rust extracted and compiled as Lean.")
        print("PASS: concrete field arithmetic and G1 operations, including full 256-bit multiplication, refine EthLib.")
        print("PASS: live final exponentiation computes the cubed EthLib value; the default prepared pairing check terminates and equals unchanged EthLib pairingCheck on the declared finite-G2 subgroup domain.")
        print("PASS: prepared Rust pairing terminates and equals unchanged EthLib pairingCheck on the declared finite-G2 subgroup domain.")
        print("PASS: prepared four-pair Miller loop and pairing endpoint terminate and refine the complete source field schedule.")
        print("PASS: G2 preparation and M-twist line steps terminate and refine their source field-polynomial schedules.")
        print("PASS: compressed decoding, subgroup decoding and public-key decoding refine EthLib on all byte inputs.")
        print(f"Audited {len(audits)} theorems: standard Lean axioms only. Full arkworks implementation equivalence remains outside this proof.")
    except Exception as error:
        report.update(status="failed", reason=str(error))
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()

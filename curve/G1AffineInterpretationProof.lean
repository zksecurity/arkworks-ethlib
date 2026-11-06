import AffineScalarGroupProof
import ScalarNormalizationProof

open EthLib.Cryptography.Bls
open WeierstrassCurve
open scoped WeierstrassCurve.Jacobian

namespace G1AffineInterpretation
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing
-- EthLib installs another division instance; these normal forms use the field operation.
local instance (priority := high + 1) : Div Fp := ⟨G1Curve.fieldStructure.div⟩

private theorem inverse_eq (z : Fp) (hz : z ≠ 0) : Fp.inverse z = z⁻¹ :=
  (BaseField.inverse_unique z z⁻¹ hz (mul_inv_cancel₀ hz)).symm

/-- EthLib's affine exporter uses the same normalization as the mathematical point group. -/
theorem toAffine_finite (p : G1) (hz : p.z ≠ 0) :
    G1.toAffine p = (p.x/p.z^2,p.y/p.z^3) := by
  have hi : p.z.isZero = false := by cases h : p.z.isZero <;> simp_all
  simp only [G1.toAffine, hi, Bool.false_eq_true, ↓reduceIte, inverse_eq p.z hz]
  apply Prod.ext <;> simp only [div_eq_mul_inv] <;> ring

/-- Normalizing the affine data preserves the curve and the represented point, including infinity. -/
theorem normalized_correct (p : G1) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (AffineScalarGroup.effectiveBase (G1.toAffine p).1 (G1.toAffine p).2 p.isInfinity) ∧
    G1Curve.interpret (AffineScalarGroup.effectiveBase (G1.toAffine p).1 (G1.toAffine p).2 p.isInfinity) =
      G1Curve.interpret p := by
  by_cases hz : p.z = 0
  · have hi : p.z.isZero = true := (G1Curve.isZero_iff p.z).mpr hz
    simp only [AffineScalarGroup.effectiveBase, G1.isInfinity, hi, ↓reduceIte]
    exact ⟨Or.inl rfl, G1Curve.interpret_zero.trans (G1Curve.interpret_infinity p hz).symm⟩
  · have hi : p.z.isZero = false := by cases h : p.z.isZero <;> simp_all
    simp only [AffineScalarGroup.effectiveBase, G1.isInfinity, hi, Bool.false_eq_true, ↓reduceIte]
    rw [toAffine_finite p hz]
    have he : G1Curve.coords p ≈ ![p.x/p.z^2,p.y/p.z^3,1] :=
      Jacobian.equiv_some_of_Z_ne_zero hz
    have hn := (Jacobian.nonsingular_of_equiv (W' := G1Curve.curve.toJacobian) he).mp
      (G1Curve.nonsingular_finite p hp hz)
    have hone : Fp.one = (1 : Fp) := by decide +kernel
    rw [hone]
    exact ⟨Or.inr hn.1, (Jacobian.Point.toAffine_of_equiv he).symm⟩

theorem affine_data_onCurve (p : G1) (hp : G1Curve.OnCurve p) :
    p.isInfinity = true ∨ G1Curve.OnCurve ⟨(G1.toAffine p).1,(G1.toAffine p).2,Fp.one⟩ := by
  by_cases hi : p.isInfinity = true
  · exact Or.inl hi
  · right
    simpa [AffineScalarGroup.effectiveBase, hi] using (normalized_correct p hp).1

theorem baseAction_toAffine (p : G1) (hp : G1Curve.OnCurve p) :
    AffineScalarGroup.baseAction ⟨(G1.toAffine p).1,(G1.toAffine p).2,Fp.one⟩ p.isInfinity =
      G1Curve.interpret p := by
  have he : G1Curve.interpret (AffineScalarGroup.effectiveBase (G1.toAffine p).1 (G1.toAffine p).2 p.isInfinity) =
      AffineScalarGroup.baseAction ⟨(G1.toAffine p).1,(G1.toAffine p).2,Fp.one⟩ p.isInfinity := by
    cases hi : p.isInfinity <;>
      simp [AffineScalarGroup.effectiveBase, AffineScalarGroup.baseAction, G1Curve.interpret_zero]
  exact he.symm.trans (normalized_correct p hp).2

#print axioms toAffine_finite
#print axioms normalized_correct
#print axioms affine_data_onCurve
#print axioms baseAction_toAffine
end
end G1AffineInterpretation

open Aeneas Aeneas.Std Aeneas.Std.WP ConcreteCurve

namespace ConcreteNormalization

/-- Shared normalization preserves the mathematical point and its curve membership. -/
theorem normalize_projective_group_spec (p : RawPoint) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.scalar.normalize_projective p ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) = G1Curve.interpret (decodePoint p) ⦄ := by
  apply spec_mono (normalize_projective_spec p hp)
  rintro out ⟨hv, he⟩
  refine ⟨hv, ?_⟩
  rw [he]
  exact G1AffineInterpretation.normalized_correct (decodePoint p) hc

#print axioms normalize_projective_group_spec
end ConcreteNormalization

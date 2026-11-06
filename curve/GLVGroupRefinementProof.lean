import GLVGroupProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls ConcreteCurve

namespace GLVGroupRefinement

/-- The extracted source multiplier computes the signed two-base group action. -/
theorem mul_projective_components_spec (p : RawPoint) (k : Scalar) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.glv.mul_projective p k ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) =
        (GLVDecomposition.components (scalarValue k % Fr.modulus : Int)).1 •
          G1Curve.interpret (decodePoint p) +
        (GLVDecomposition.components (scalarValue k % Fr.modulus : Int)).2 •
          G1Curve.interpret (G1Endomorphism.map (decodePoint p)) ⦄ := by
  apply spec_mono (ConcreteGLV.mul_projective_spec p k hp)
  rintro out ⟨hv, he⟩
  refine ⟨hv, ?_⟩
  rw [he]
  exact GLVGroup.mul_projective_components (decodePoint p) (scalarValue k) hc

/-- Scalar multiplication correctness, with the remaining eigenvalue fact explicit. -/
theorem mul_projective_spec (p : RawPoint) (k : Scalar) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p))
    (hr : Fr.modulus • G1Curve.interpret (decodePoint p) = 0)
    (he : G1Curve.interpret (G1Endomorphism.map (decodePoint p)) =
      GLVDecomposition.eigenvalue • G1Curve.interpret (decodePoint p)) :
    CurveG1.glv.mul_projective p k ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) = scalarValue k • G1Curve.interpret (decodePoint p) ⦄ := by
  apply spec_mono (ConcreteGLV.mul_projective_spec p k hp)
  rintro out ⟨hv, hout⟩
  refine ⟨hv, ?_⟩
  rw [hout]
  exact GLVGroup.mul_projective_correct (decodePoint p) (scalarValue k) hc hr he

#print axioms mul_projective_components_spec
#print axioms mul_projective_spec
end GLVGroupRefinement

import ScalarAPIProof
import EncodingProof
import G1CurveProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls ConcreteCurve

namespace G1GroupRefinement
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing

/-- The existing extracted integer multiplier computes the mathematical group action. -/
theorem mul_256_spec (p : RawPoint) (k : Scalar) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.mul_256 p k ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) = scalarValue k • G1Curve.interpret (decodePoint p) ⦄ := by
  apply spec_mono (ConcreteCurve.mul_256_spec p k hp)
  rintro out ⟨hv, he⟩
  refine ⟨hv, ?_⟩
  rw [he]
  apply ScalarEncoding.integer_correct _ _ hc
  simpa only [FieldProof.B, ← pow_mul] using ConcreteGLV.scalar_bound k

/-- The u64 full-curve API computes integer scalar action through the source affine path. -/
theorem mul_u64_spec (p : RawPoint) (k : U64) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.mul_u64 p k ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) = k.val • G1Curve.interpret (decodePoint p) ⦄ := by
  apply spec_mono (ConcreteCurve.mul_u64_spec p k hp)
  rintro out ⟨hv, he⟩
  refine ⟨hv, ?_⟩
  rw [he]
  apply ScalarEncoding.integer_correct _ _ hc
  scalar_tac

/-- The existing extracted order-r check classifies mathematical r-torsion. -/
theorem subgroup_spec (p : RawPoint) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.field.in_subgroup p ⦃ out =>
      out = true ↔ Fr.modulus • G1Curve.interpret (decodePoint p) = 0 ⦄ := by
  apply spec_mono (ConcreteEncoding.subgroup_spec p hp hc)
  intro out he
  rw [he]
  exact G1Curve.inSubgroup_iff (decodePoint p) hc

#print axioms mul_u64_spec
#print axioms mul_256_spec
#print axioms subgroup_spec
end
end G1GroupRefinement

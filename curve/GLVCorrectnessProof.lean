import G1EigenvalueProof
import GLVGroupRefinementProof

open EthLib.Cryptography.Bls

namespace GLVCorrectness

/-- Complete scalar-action correctness on the mathematical G1 subgroup. -/
theorem mul_projective_correct (p : G1) (k : Nat) (hp : G1Curve.OnCurve p)
    (hr : Fr.modulus • G1Curve.interpret p = 0) :
    G1Curve.OnCurve (GLVSchedule.mulProjective p k) ∧
    G1Curve.interpret (GLVSchedule.mulProjective p k) = k • G1Curve.interpret p :=
  GLVGroup.mul_projective_correct p k hp hr (G1Eigenvalue.eigenvalue p hp hr)

/-- The source schedule and EthLib integer multiplication represent the same subgroup point. -/
theorem ethlib_mul_equiv (p : G1) (k : Nat) (hp : G1Curve.OnCurve p)
    (hr : Fr.modulus • G1Curve.interpret p = 0) :
    G1Curve.interpret (GLVSchedule.mulProjective p k) = G1Curve.interpret (G1.mulNat p k) :=
  (mul_projective_correct p k hp hr).2.trans (G1Curve.mulNat_correct p k hp).2.symm

open Aeneas Aeneas.Std Aeneas.Std.WP ConcreteCurve

/-- The extracted source GLV multiplier needs only curve membership and r-torsion. -/
theorem mul_projective_spec (p : RawPoint) (k : Scalar) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p))
    (hr : Fr.modulus • G1Curve.interpret (decodePoint p) = 0) :
    CurveG1.glv.mul_projective p k ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) = scalarValue k • G1Curve.interpret (decodePoint p) ⦄ :=
  GLVGroupRefinement.mul_projective_spec p k hp hc hr (G1Eigenvalue.eigenvalue _ hc hr)

#print axioms mul_projective_correct
#print axioms ethlib_mul_equiv
#print axioms mul_projective_spec
end GLVCorrectness

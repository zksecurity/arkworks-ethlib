import ScalarEncodingProof
import GLVCorrectnessProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls ConcreteCurve

namespace ConcreteCurve

/-- Full integer API: exact source affine schedule on every canonical coordinate input. -/
@[step] theorem mul_256_spec (p : RawPoint) (s : Scalar) (hp : ValidPoint p) :
    CurveG1.mul_256 p s ⦃ out =>
      ValidPoint out ∧ decodePoint out = ScalarEncoding.mulInteger (decodePoint p) (scalarValue s) ⦄ := by
  unfold CurveG1.mul_256
  step as ⟨base, hx, hy, he, hi⟩
  have hxe := congrArg Prod.fst he
  have hye := congrArg Prod.snd he
  step*
  all_goals simp_all [ScalarEncoding.mulInteger]

@[step] theorem mul_u64_spec (p : RawPoint) (k : U64) (hp : ValidPoint p) :
    CurveG1.mul_u64 p k ⦃ out =>
      ValidPoint out ∧ decodePoint out = ScalarEncoding.mulInteger (decodePoint p) k.val ⦄ := by
  unfold CurveG1.mul_u64
  step as ⟨base, hx, hy, he, hi⟩
  have hxe := congrArg Prod.fst he
  have hye := congrArg Prod.snd he
  step*
  all_goals simp_all [ScalarEncoding.mulInteger, scalarValue]

theorem mul_u64_correct (p : RawPoint) (k : U64) (hp : ValidPoint p) :
    CurveG1.field.mul_u64_concrete p k ⦃ out =>
      ValidPoint out ∧ decodePoint out = ScalarEncoding.mulInteger (decodePoint p) k.val ⦄ := by
  simpa only [CurveG1.field.mul_u64_concrete] using mul_u64_spec p k hp

/-- The concrete projective API retains the specialized source GLV coordinates on every canonical input. -/
theorem mul_256_correct (p : RawPoint) (s : Scalar) (hp : ValidPoint p) :
    CurveG1.field.mul_256_concrete p s ⦃ out =>
      ValidPoint out ∧ decodePoint out = GLVSchedule.mulProjective (decodePoint p) (scalarValue s) ⦄ := by
  simpa only [CurveG1.field.mul_256_concrete] using ConcreteGLV.mul_projective_spec p s hp

/-- The source projective API computes the requested scalar action on subgroup inputs. -/
theorem mul_256_group_spec (p : RawPoint) (s : Scalar) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p))
    (hr : Fr.modulus • G1Curve.interpret (decodePoint p) = 0) :
    CurveG1.field.mul_256_concrete p s ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) = scalarValue s • G1Curve.interpret (decodePoint p) ⦄ := by
  simpa only [CurveG1.field.mul_256_concrete] using GLVCorrectness.mul_projective_spec p s hp hc hr

#print axioms mul_256_spec
#print axioms mul_u64_spec
#print axioms mul_u64_correct
#print axioms mul_256_correct
#print axioms mul_256_group_spec
end ConcreteCurve

namespace CurveProof

/-- Concrete u64 integer multiplication now refines the pinned source affine schedule. -/
theorem mul_u64_refines (p : RawPoint) (k : U64) (hp : ValidPoint p) :
    CurveG1.mul_u64 p k ⦃ out =>
      ValidPoint out ∧ decodePoint out = ScalarEncoding.mulInteger (decodePoint p) k.val ⦄ :=
  ConcreteCurve.mul_u64_spec p k hp

#print axioms mul_u64_refines
end CurveProof

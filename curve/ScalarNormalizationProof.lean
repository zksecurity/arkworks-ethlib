import ConcreteProof
import BaseFieldProof
import BinaryInverseProof
import AffinePointModel

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls ConcreteField ConcreteCurve

namespace ConcreteNormalization
local instance : CommRing Fp := Fin.instCommRing Fp.modulus

private theorem fp_beq_true (a b : Fp) : Fp.beq a b = true ↔ a = b := by
  simp only [Fp.beq, beq_iff_eq, ← Fin.ext_iff]

private theorem fp_one : Fp.one = (1 : Fp) := by decide +kernel

private theorem inverse_one : Fp.inverse (1 : Fp) = 1 := by
  have h := BaseField.inverse_mul (1 : Fp) (by decide +kernel)
  simpa only [one_mul] using h

/-- The shared source normalization returns EthLib's affine data on every canonical input. -/
@[step] theorem normalize_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.scalar.normalize p ⦃ out =>
      FieldProof.Valid out.x ∧ FieldProof.Valid out.y ∧
      (decode out.x,decode out.y) = G1.toAffine (decodePoint p) ∧
      out.infinity = (decodePoint p).isInfinity ⦄ := by
  rcases hp with ⟨hx,hy,hz⟩
  have ⟨ho,he⟩ := montgomery_one
  have hmod : Fp.modulus ≠ 1 := by decide +kernel
  unfold CurveG1.scalar.normalize
  step*
  all_goals simp_all [G1.toAffine, G1.isInfinity, decodePoint, fp_beq_true,
    fp_one, inverse_one, Fp.zero, Fp.ofNat]

@[step] theorem projective_from_affine_spec (p : CurveG1.AffinePoint CurveG1.field.Fp)
    (hx : FieldProof.Valid p.x) (hy : FieldProof.Valid p.y) :
    CurveG1.scalar.projective_from_affine p ⦃ out => ValidPoint out ∧ decodePoint out =
      AffineScalarGroup.effectiveBase (decode p.x) (decode p.y) p.infinity ⦄ := by
  unfold CurveG1.scalar.projective_from_affine
  step*
  all_goals simp_all [ValidPoint, decodePoint, AffineScalarGroup.effectiveBase, fp_one, Fp.ofNat]

@[step] theorem normalize_projective_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.scalar.normalize_projective p ⦃ out => ValidPoint out ∧ decodePoint out =
      AffineScalarGroup.effectiveBase (G1.toAffine (decodePoint p)).1
        (G1.toAffine (decodePoint p)).2 (decodePoint p).isInfinity ⦄ := by
  unfold CurveG1.scalar.normalize_projective
  step as ⟨affine, hx, hy, he, hi⟩
  have hxe := congrArg Prod.fst he
  have hye := congrArg Prod.snd he
  step*

#print axioms normalize_spec
#print axioms projective_from_affine_spec
#print axioms normalize_projective_spec
end ConcreteNormalization

import PreparedG2Proof
import ScalarNormalizationProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteField ConcreteCurve ConcreteExtension ConcretePreparedG2

namespace ConcretePreparedProjective

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
local instance : CommRing Fp2 := QuadraticField.ringStructure

private theorem fp_beq_true (a b : Fp) : Fp.beq a b = true ↔ a = b := by
  simp only [Fp.beq, beq_iff_eq, ←Fin.ext_iff]

private theorem fp2_beq_true (a b : Fp2) : Fp2.beq a b = true ↔ a = b := by
  cases a; cases b
  simp only [Fp2.beq, Bool.and_eq_true, fp_beq_true, Fp2.mk.injEq]

private theorem fp_one : Fp.one = (1 : Fp) := by decide +kernel

private theorem inverse_one : Fp.inverse (1 : Fp) = 1 := by
  have h := BaseField.inverse_mul (1 : Fp) (by decide +kernel)
  simpa only [one_mul] using h

private theorem inverse_two_one : Fp2.inverse (1 : Fp2) = 1 := by
  change Fp2.inverse Fp2.one = Fp2.one
  simp only [Fp2.inverse, Fp2.one, fp_one,
    show Fp.zero = (0 : Fp) from rfl, one_mul, zero_mul, add_zero,
    inverse_one, neg_zero]

@[step] theorem one_spec : CurveG1.pairing.prepared.one_fp2 ⦃ r =>
    Valid2 r ∧ decode2 r = Fp2.one ⦄ := by
  have ⟨hv,he⟩ := montgomery_one
  unfold CurveG1.pairing.prepared.one_fp2
  step*
  all_goals simp_all [Valid2, decode2, Fp2.one]

/-- The source G1 preparation retains exactly EthLib's affine coordinates and infinity flag. -/
@[step] theorem g1_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.pairing.prepared.prepare_g1 p ⦃ r =>
      FieldProof.Valid r.x ∧ FieldProof.Valid r.y ∧
      (decode r.x,decode r.y) = G1.toAffine (decodePoint p) ∧
      r.infinity = (decodePoint p).isInfinity ⦄ := by
  simpa only [CurveG1.pairing.prepared.prepare_g1] using ConcreteNormalization.normalize_spec p hp

/-- Source projective G2 normalization agrees with unchanged EthLib, including Z=1. -/
@[step] theorem normalize_g2_spec (p : RawG2) (hp : ValidG2 p) :
    CurveG1.pairing.prepared.normalize_g2 p ⦃ r =>
      Valid2 r.x ∧ Valid2 r.y ∧
      (decode2 r.x,decode2 r.y) = G2.toAffine (decodeG2 p) ∧
      r.infinity = (decodeG2 p).isInfinity ⦄ := by
  rcases hp with ⟨hx,hy,hz⟩
  unfold CurveG1.pairing.prepared.normalize_g2
  step*
  all_goals simp_all [G2.toAffine, G2.isInfinity, decodeG2, fp2_beq_true,
    inverse_two_one, show Fp2.one = (1 : Fp2) from rfl]

/-- Projective preparation composes normalization with the complete source coefficient producer. -/
@[step] theorem prepare_g2_spec (p : RawG2) (hp : ValidG2 p) :
    CurveG1.pairing.prepared.prepare_g2 p ⦃ r =>
      r.infinity = (decodeG2 p).isInfinity ∧ ValidCoeffs r.ell_coeffs.val ∧
      decodeCoeffs r.ell_coeffs.val = PreparedLine.prepare
        (G2.toAffine (decodeG2 p)).1 (G2.toAffine (decodeG2 p)).2 (decodeG2 p).isInfinity ∧
      r.ell_coeffs.val.length = if (decodeG2 p).isInfinity then 0 else 68 ⦄ := by
  unfold CurveG1.pairing.prepared.prepare_g2
  step*
  all_goals
    have hx := congrArg Prod.fst q_post2
    have hy := congrArg Prod.snd q_post2
    simp_all

#print axioms one_spec
#print axioms g1_spec
#print axioms normalize_g2_spec
#print axioms prepare_g2_spec
end ConcretePreparedProjective

import Mathlib.Data.ZMod.Defs
import FieldRefinement
import G1AlignmentProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteField

namespace ConcreteCurve

@[simp] private theorem one_constant : Fp.ofNat 1 = Fp.one := by decide

abbrev RawPoint := CurveG1.Point CurveG1.field.Fp
abbrev implementation := CurveG1.field.Fp.Insts.Curve_g1Field

def ValidPoint (p : RawPoint) : Prop := Valid p.x ∧ Valid p.y ∧ Valid p.z
def decodePoint (p : RawPoint) : G1 := ⟨decode p.x, decode p.y, decode p.z⟩

@[step] theorem identity_spec :
    CurveG1.identity implementation ⦃ r => ValidPoint r ∧ decodePoint r = G1.zero ⦄ := by
  unfold CurveG1.identity
  step*
  all_goals simp_all [ValidPoint, decodePoint, G1.zero, Fp.one, Fp.zero, Fp.ofNat]
  decide

@[step] theorem negate_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.negate implementation p ⦃ r => ValidPoint r ∧ decodePoint r = G1.neg (decodePoint p) ⦄ := by
  rcases hp with ⟨hx, hy, hz⟩
  unfold CurveG1.negate
  step*
  all_goals simp_all [ValidPoint, decodePoint, G1.neg]

@[step] theorem double_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.double implementation p ⦃ r => ValidPoint r ∧ decodePoint r = G1.double (decodePoint p) ⦄ := by
  rcases hp with ⟨hx, hy, hz⟩
  unfold CurveG1.double
  step*
  all_goals simp_all [ValidPoint, decodePoint, G1.double]
  all_goals let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  all_goals ring_nf
  all_goals simp_all

@[step] theorem add_general_spec (p q : RawPoint) (hp : ValidPoint p) (hq : ValidPoint q) :
    CurveG1.add_general implementation p q ⦃ r => ValidPoint r ∧
      decodePoint r = G1.addGeneral (decodePoint p) (decodePoint q) ⦄ := by
  rcases hp with ⟨hx, hy, hz⟩
  rcases hq with ⟨hqx, hqy, hqz⟩
  unfold CurveG1.add_general
  simp only [implementation, CurveG1.field.Fp.Insts.Curve_g1Field]
  step*
  all_goals simp_all [ValidPoint, decodePoint, G1.addGeneral]
  all_goals let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  all_goals ring_nf
  all_goals simp_all

@[step] theorem add_mixed_spec (p : RawPoint) (q : CurveG1.AffinePoint CurveG1.field.Fp)
    (hp : ValidPoint p) (hqx : Valid q.x) (hqy : Valid q.y) :
    CurveG1.add_mixed implementation p q ⦃ r => ValidPoint r ∧
      decodePoint r = G1.addMixed (decodePoint p) ⟨decode q.x, decode q.y, Fp.one⟩ ⦄ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hs : decode p.z * decode q.y = decode q.y * decode p.z := mul_comm _ _
  rcases hp with ⟨hx, hy, hz⟩
  unfold CurveG1.add_mixed
  simp only [implementation, CurveG1.field.Fp.Insts.Curve_g1Field]
  step*
  all_goals simp_all [ValidPoint, decodePoint, G1.addMixed]
  all_goals let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  all_goals ring_nf
  all_goals simp_all

@[step] theorem add_spec (p q : RawPoint) (hp : ValidPoint p) (hq : ValidPoint q) :
    CurveG1.add implementation p q ⦃ r => ValidPoint r ∧ decodePoint r = G1.add (decodePoint p) (decodePoint q) ⦄ := by
  rcases hp with ⟨hx, hy, hz⟩
  rcases hq with ⟨hqx, hqy, hqz⟩
  unfold CurveG1.add
  simp only [implementation, CurveG1.field.Fp.Insts.Curve_g1Field]
  step*
  all_goals simp_all [ValidPoint, decodePoint, G1Alignment.add_projective]

/-- Affine infinity preserves the original identity representation, as in arkworks. -/
@[step] theorem add_affine_spec (p : RawPoint) (q : CurveG1.AffinePoint CurveG1.field.Fp)
    (hp : ValidPoint p) (hqx : Valid q.x) (hqy : Valid q.y) :
    CurveG1.add_affine implementation p q ⦃ r => ValidPoint r ∧ decodePoint r =
      if q.infinity then decodePoint p else
        G1.add (decodePoint p) ⟨decode q.x, decode q.y, Fp.one⟩ ⦄ := by
  have hz : Fp.one.isZero = false := by decide
  have he : Fp.one.beq Fp.one = true := by decide
  rcases hp with ⟨hx, hy, hpz⟩
  unfold CurveG1.add_affine
  simp only [implementation, CurveG1.field.Fp.Insts.Curve_g1Field]
  step*
  all_goals simp_all [ValidPoint, decodePoint, G1.add]

abbrev Scalar := Aeneas.Std.Array U64 4#usize

def scalarValue (s : Scalar) : Nat :=
  s[0]!.val + B * s[1]!.val + B^2 * s[2]!.val + B^3 * s[3]!.val

theorem generator_correct :
    CurveG1.field.generator ⦃ r => ValidPoint r ∧ decodePoint r = G1.generator ⦄ := by
  unfold CurveG1.field.generator
  step*
  all_goals simp_all [ValidPoint, Valid, decodePoint, decode, value, B, G1.generator, Fp.modulus, Fp.ofNat, Fp.one, MontgomeryProof.rInverse]

/-- The exported concrete entry points, including the actual field implementation. -/
theorem add_correct (p q : RawPoint) (hp : ValidPoint p) (hq : ValidPoint q) :
    CurveG1.field.add_concrete p q ⦃ r =>
      ValidPoint r ∧ decodePoint r = G1.add (decodePoint p) (decodePoint q) ⦄ := by
  exact add_spec p q hp hq

theorem double_correct (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.double_concrete p ⦃ r =>
      ValidPoint r ∧ decodePoint r = G1.double (decodePoint p) ⦄ := by
  exact double_spec p hp

theorem negate_correct (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.negate_concrete p ⦃ r =>
      ValidPoint r ∧ decodePoint r = G1.neg (decodePoint p) ⦄ := by
  exact negate_spec p hp

#print axioms identity_spec
#print axioms negate_spec
#print axioms double_spec
#print axioms add_spec
#print axioms add_affine_spec
#print axioms generator_correct
#print axioms add_correct
#print axioms double_correct
#print axioms negate_correct

#print axioms add_general_spec
#print axioms add_mixed_spec

end ConcreteCurve

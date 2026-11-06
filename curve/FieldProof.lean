import MontgomerySquareReductionProof
import MontgomeryFusedProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls

namespace FieldProof

@[step] theorem from_limbs_spec (a : Limbs) :
    CurveG1.field.Fp.from_limbs a ⦃ out =>
      (∀ r, out = some r → Valid r) ∧
      out.map (fun r => value r.limbs) =
        if value a < Fp.modulus then some ((value a * B^6) % Fp.modulus) else none ⦄ := by
  unfold CurveG1.field.Fp.from_limbs
  step*
  all_goals simp_all [Valid]

@[step] theorem to_limbs_spec (a : CurveG1.field.Fp) (ha : Valid a) :
    CurveG1.field.Fp.to_limbs a ⦃ out =>
      value out < Fp.modulus ∧
      value out = (value a.limbs * MontgomeryProof.rInverse) % Fp.modulus ⦄ := by
  unfold Valid at ha
  unfold CurveG1.field.Fp.to_limbs
  step*

@[step] theorem constant_spec (n : U32) :
    CurveG1.field.Fp.Insts.Curve_g1Field.constant n ⦃ r =>
      Valid r ∧ value r.limbs = (n.val * B^6) % Fp.modulus ⦄ := by
  have hn : n.val < Fp.modulus := by unfold Fp.modulus; scalar_tac
  by_cases h : n = 1#u32
  · subst n
    unfold CurveG1.field.Fp.Insts.Curve_g1Field.constant
    step*
    all_goals simp_all [Valid, value, CurveG1.field.FROBENIUS_FP2_C1, CurveG1.montgomery.R, B, Fp.modulus]
  · unfold CurveG1.field.Fp.Insts.Curve_g1Field.constant
    step*
    all_goals simp_all [value]
    all_goals cases o <;> simp_all [Valid]


@[step] theorem plus_spec (a b : CurveG1.field.Fp) (ha : Valid a) (hb : Valid b) :
    CurveG1.field.Fp.Insts.Curve_g1Field.plus a b ⦃ r =>
      Valid r ∧ value r.limbs = (value a.limbs + value b.limbs) % Fp.modulus ⦄ := by
  have hp : 2 * Fp.modulus < B^6 := by decide
  unfold Valid at *
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.plus
  step*
  all_goals (simp_all [Fp.modulus, B]; omega)

@[step] theorem minus_spec (a b : CurveG1.field.Fp) (ha : Valid a) (hb : Valid b) :
    CurveG1.field.Fp.Insts.Curve_g1Field.minus a b ⦃ r =>
      Valid r ∧ value r.limbs = (value a.limbs + Fp.modulus - value b.limbs) % Fp.modulus ⦄ := by
  have hp : 2 * Fp.modulus < B^6 := by decide
  unfold Valid at *
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.minus
  step*
  split <;> step*
  all_goals (simp_all [Fp.modulus, B]; omega)

@[step] theorem equal_spec (a b : CurveG1.field.Fp) :
    CurveG1.field.Fp.Insts.Curve_g1Field.equal a b ⦃ r =>
      r = decide (value a.limbs = value b.limbs) ⦄ := by
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.equal
  step*
  all_goals simp_all [value, B, UScalar.eq_equiv]
  all_goals scalar_tac

@[step] theorem is_zero_spec (a : CurveG1.field.Fp) :
    CurveG1.field.Fp.Insts.Curve_g1Field.is_zero a ⦃ r =>
      r = decide (value a.limbs = 0) ⦄ := by
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.is_zero
  step*
  all_goals simp_all [value, B, UScalar.eq_equiv]

@[step] theorem negative_spec (a : CurveG1.field.Fp) (ha : Valid a) :
    CurveG1.field.Fp.Insts.Curve_g1Field.negative a ⦃ r =>
      Valid r ∧ value r.limbs = (Fp.modulus - value a.limbs) % Fp.modulus ⦄ := by
  unfold Valid at *
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.negative
  step*
  all_goals simp_all [Fp.modulus]
  all_goals omega

@[simp] theorem value_parity (a : Limbs) : value a % 2 = a[0]!.val % 2 := by
  simp [value, B, Nat.add_mod, Nat.mul_mod]

@[simp] theorem low_bit (a : U64) : (a &&& 1#u64 = 1#u64) ↔ a.val % 2 = 1 := by
  simp [UScalar.eq_equiv]

@[step] private theorem montgomery_multiply (a b : Limbs) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.multiply a b ⦃ out =>
      value out < Fp.modulus ∧ value out = (value a * value b * MontgomeryProof.rInverse) % Fp.modulus ⦄ :=
  MontgomeryProof.multiply_value a b ha

@[step] theorem times_spec (a b : CurveG1.field.Fp) (ha : Valid a) :
    CurveG1.field.Fp.Insts.Curve_g1Field.times a b ⦃ r =>
      Valid r ∧ value r.limbs = (value a.limbs * value b.limbs * MontgomeryProof.rInverse) % Fp.modulus ⦄ := by
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.times
  unfold Valid at ha
  step*
  all_goals simp_all [Valid]

@[step] private theorem montgomery_square (a : Limbs) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.square a ⦃ out => value out < Fp.modulus ∧
      value out = ((value a)^2 * MontgomeryProof.rInverse) % Fp.modulus ⦄ :=
  MontgomerySquareReduction.square_value a ha

@[step] theorem square_spec (a : CurveG1.field.Fp) (ha : Valid a) :
    CurveG1.field.Fp.Insts.Curve_g1Field.square a ⦃ r =>
      Valid r ∧ value r.limbs = ((value a.limbs)^2 * MontgomeryProof.rInverse) % Fp.modulus ⦄ := by
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.square
  unfold Valid at ha
  step*
  all_goals simp_all [Valid]

@[step] private theorem montgomery_sum_products (a b c d : Limbs)
    (ha : value a < Fp.modulus) (hb : value b < Fp.modulus)
    (hc : value c < Fp.modulus) (hd : value d < Fp.modulus) :
    CurveG1.montgomery.sum_products a b c d ⦃ out => value out < Fp.modulus ∧
      value out = ((value a*value b+value c*value d)*MontgomeryProof.rInverse) % Fp.modulus ⦄ :=
  MontgomeryFused.sum_products_value a b c d ha hb hc hd

@[step] theorem sum_products_spec (a b c d : CurveG1.field.Fp)
    (ha : Valid a) (hb : Valid b) (hc : Valid c) (hd : Valid d) :
    CurveG1.field.Fp.Insts.Curve_g1Field.sum_products a b c d ⦃ r => Valid r ∧
      value r.limbs = ((value a.limbs*value b.limbs+value c.limbs*value d.limbs)*MontgomeryProof.rInverse) % Fp.modulus ⦄ := by
  unfold CurveG1.field.Fp.Insts.Curve_g1Field.sum_products
  unfold Valid at ha hb hc hd
  step*
  all_goals simp_all [Valid]

#print axioms sum_products_spec
#print axioms square_spec
#print axioms from_limbs_spec
#print axioms to_limbs_spec
#print axioms constant_spec
#print axioms plus_spec
#print axioms minus_spec
#print axioms times_spec
#print axioms negative_spec
#print axioms equal_spec
#print axioms is_zero_spec

end FieldProof

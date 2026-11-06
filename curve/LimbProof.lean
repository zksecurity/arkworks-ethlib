import Generated.CurveG1
import EthLib.Cryptography.Bls.Fp

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls

namespace FieldProof

abbrev B : Nat := 2^64
abbrev Limbs := Aeneas.Std.Array U64 6#usize

def value (a : Limbs) : Nat :=
  a[0]!.val + B * a[1]!.val + B^2 * a[2]!.val +
  B^3 * a[3]!.val + B^4 * a[4]!.val + B^5 * a[5]!.val

def Valid (a : CurveG1.field.Fp) : Prop := value a.limbs < Fp.modulus

@[step] theorem adc_spec (a b c : U64) (hc : c.val ≤ 1) :
    CurveG1.field.adc a b c ⦃ r =>
      r.1.val + B * r.2.val = a.val + b.val + c.val ∧ r.2.val ≤ 1 ⦄ := by
  unfold CurveG1.field.adc
  step*
  all_goals (simp only [B, Nat.shiftRight_eq_div_pow] at *; scalar_tac)

@[step] theorem sbb_spec (a b c : U64) (hc : c.val ≤ 1) :
    CurveG1.field.sbb a b c ⦃ r =>
      r.1.val + b.val + c.val = a.val + B * r.2.val ∧ r.2.val ≤ 1 ⦄ := by
  unfold CurveG1.field.sbb
  step*
  all_goals (simp only [B, Nat.shiftRight_eq_div_pow] at *; scalar_tac)

theorem value_bound (a : Limbs) : value a < B^6 := by
  unfold value B
  scalar_tac

@[step] theorem less_spec (a b : Limbs) :
    CurveG1.field.less a b ⦃ r => r = decide (value a < value b) ⦄ := by
  unfold CurveG1.field.less
  step*
  all_goals (simp_all [value, B] <;> scalar_tac)

@[step] theorem add_raw_spec (a b : Limbs) (h : value a + value b < B^6) :
    CurveG1.field.add_raw a b ⦃ r => value r = value a + value b ⦄ := by
  unfold CurveG1.field.add_raw
  step*
  all_goals (simp_all [value, B]; scalar_tac)

@[step] theorem subtract_spec (a b : Limbs) (h : value b ≤ value a) :
    CurveG1.field.subtract a b ⦃ r => value r = value a - value b ⦄ := by
  have ha := value_bound a
  have hb := value_bound b
  unfold CurveG1.field.subtract
  step*
  all_goals (simp_all [value, B]; scalar_tac)

theorem join_bits (a b : U64) :
    ((a.bv >>> 1) ||| (b.bv <<< 63)).toNat = a.val / 2 + 2^63 * (b.val % 2) := by
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]
  have hlow : a.val / 2 < 2^63 := by scalar_tac
  have hhigh : b.val * 2^63 % 2^64 = 2^63 * (b.val % 2) := by omega
  change (a.val / 2) ||| (b.val * 2^63 % 2^64) = _
  rw [hhigh, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hlow]
  omega

@[simp] theorem join_values (a b : U64) :
    (a.val / 2) ||| (b.val <<< 63 % U64.size) = a.val / 2 + 2^63 * (b.val % 2) := by
  simpa only [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    U64.size_eq, UScalar.bv_toNat, Nat.reducePow, Nat.shiftRight_eq_div_pow] using join_bits a b

@[step] theorem halve_spec (a : Limbs) :
    CurveG1.field.halve a ⦃ r => value r = value a / 2 ⦄ := by
  unfold CurveG1.field.halve
  step*
  all_goals (simp_all [value, B, Nat.shiftRight_eq_div_pow]; scalar_tac)

@[simp] theorem modulus_value : value CurveG1.field.MODULUS = Fp.modulus := by
  simp [value, CurveG1.field.MODULUS, Fp.modulus, B]

@[simp] theorem zero_value : value (Aeneas.Std.Array.repeat 6#usize 0#u64) = 0 := by
  simp [value, B]

end FieldProof

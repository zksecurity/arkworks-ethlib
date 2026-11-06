import GLVDecompositionProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteCurve

namespace GLVArithmetic

def roundDivNat (n d : Nat) : Nat :=
  n / d + if d < 2 * (n % d) then 1 else 0

@[simp] theorem order_value : value CurveG1.glv.arithmetic.ORDER = Fr.modulus := by
  decide +kernel

@[step] theorem multiply_128_spec (n : Scalar) (m : Aeneas.Std.Array U64 2#usize) :
    CurveG1.glv.arithmetic.multiply_128 n m ⦃ out =>
      value out = scalarValue n * (m[0]!.val + B * m[1]!.val) ⦄ := by
  unfold CurveG1.glv.arithmetic.multiply_128
  step*
  all_goals simp_all [value, scalarValue, B]
  all_goals linear_combination o0_post + 2^64 * o1_post + 2^128 * o2_post +
    2^192 * o3_post + 2^64 * o11_post + 2^128 * o21_post +
    2^192 * o31_post + 2^256 * o4_post

@[simp] theorem parity (n : Limbs) : value n % 2 = n[0]!.val % 2 := by
  simp [value, B, Nat.add_mod, Nat.mul_mod]

@[simp] private theorem single_value (w : U64) :
    value (Aeneas.Std.Array.make 6#usize [w,0#u64,0#u64,0#u64,0#u64,0#u64]) = w.val := by
  simp [value]

@[simp] private theorem and_one (w : U64) : (w &&& 1#u64).val = w.val % 2 := by
  simp [UScalar.val_and]

private theorem division_step (n d : Nat) (hd : 0 < d) :
    let q := n / 2 / d + n / 2 / d
    let r := n / 2 % d + n / 2 % d + n % 2
    if r < d then q = n / d ∧ r = n % d
    else q + 1 = n / d ∧ r - d = n % d := by
  have hrep := Nat.mod_add_div (n / 2) d
  have hbit := Nat.mod_add_div n 2
  have hr := Nat.mod_lt (n / 2) hd
  have hb := Nat.mod_lt n (by decide : 0 < 2)
  dsimp only
  split_ifs with h
  · have he := (Nat.div_mod_unique (a := n) (b := d)
      (d := n / 2 / d + n / 2 / d)
      (c := n / 2 % d + n / 2 % d + n % 2) hd).mpr
      ⟨by nlinarith only [hrep, hbit], h⟩
    exact ⟨he.1.symm, he.2.symm⟩
  · have hc : n / 2 % d + n / 2 % d + n % 2 - d + d =
        n / 2 % d + n / 2 % d + n % 2 := Nat.sub_add_cancel (by omega)
    have he := (Nat.div_mod_unique (a := n) (b := d)
      (d := n / 2 / d + n / 2 / d + 1)
      (c := n / 2 % d + n / 2 % d + n % 2 - d) hd).mpr
      ⟨by nlinarith only [hrep, hbit, hc], by omega⟩
    exact ⟨he.1.symm, he.2.symm⟩

@[step] theorem div_rem_spec (n d : Limbs) (hn : value n < B^6 / 2)
    (hd : 0 < value d) (hdlim : value d < B^6 / 2) :
    CurveG1.glv.arithmetic.div_rem n d ⦃ out =>
      value out.1 = value n / value d ∧ value out.2 = value n % value d ⦄ := by
  have hmod := Nat.mod_lt (value n / 2) hd
  have hdiv := Nat.div_le_self (value n / 2) (value d)
  have hp := parity n
  have hs := division_step (value n) (value d) hd
  rw [CurveG1.glv.arithmetic.div_rem]
  step*
  all_goals simp_all [single_value, zero_value]
  all_goals first | omega | (split_ifs at hs <;> omega)
termination_by value n
decreasing_by all_goals simp_all; omega

@[step] theorem rounded_quotient_spec (n : Limbs) (hn : value n < B^6 / 2) :
    CurveG1.glv.arithmetic.rounded_quotient n ⦃ out =>
      value out = roundDivNat (value n) Fr.modulus ⦄ := by
  have hr : 0 < Fr.modulus := by decide +kernel
  have hrbound : Fr.modulus < B^6 / 2 := by decide +kernel
  have hmod := Nat.mod_lt (value n) hr
  have hdiv := Nat.div_le_self (value n) Fr.modulus
  unfold CurveG1.glv.arithmetic.rounded_quotient
  step*
  all_goals simp_all [roundDivNat]
  all_goals omega

#print axioms order_value
#print axioms multiply_128_spec
#print axioms rounded_quotient_spec
#print axioms div_rem_spec

end GLVArithmetic

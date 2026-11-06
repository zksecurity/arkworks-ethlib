import TowerInverseProof
import Fp12FrobeniusProof

open EthLib.Cryptography.Bls

namespace Cyclotomic

local instance : CommRing Fp2 := QuadraticField.ringStructure
local instance : CommRing Fp6 := CubicField.ringStructure
local instance : CommRing Fp12 := DodecicField.ringStructure

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem ext6 (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl

private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- Conjugation preserves products under the unchanged coefficient arithmetic. -/
theorem conjugate_mul (a b : Fp12) : (a*b).conjugate = a.conjugate*b.conjugate := by
  apply ext12
  all_goals simp [Fp12.conjugate]
  all_goals ring

theorem conjugate_conjugate (a : Fp12) : a.conjugate.conjugate = a := by
  apply ext12
  · rfl
  · change -(-a.c1) = a.c1
    ring

theorem conjugate_one : Fp12.conjugate 1 = 1 := by
  apply ext12
  all_goals simp [Fp12.conjugate]

private theorem cubic_power_six (a : Fp6) : a^(Fp.modulus^6) = a := by
  rw [←CubicFrobenius.map_eq_power a 6]
  have hc : CubicFrobenius.coefficient 6 = (1 : Fp2) := rfl
  apply ext6
  all_goals simp [CubicFrobenius.map, hc, QuadraticField.pow_modulus_pow]

/-- Conjugation is the p-to-the-sixth power for every degree-twelve input. -/
theorem power_six (a : Fp12) : a^(Fp.modulus^6) = a.conjugate := by
  rw [←DodecicField.powNat_eq_pow (Fp.modulus^6) a,
    ←DodecicFrobenius.map_eq_power a 6]
  have hc : DodecicFrobenius.coefficient 6 = (-1 : Fp2) := by
    apply ext2 <;> decide +kernel
  unfold DodecicFrobenius.map
  rw [cubic_power_six, cubic_power_six, hc, map_neg, map_one, mul_neg_one]
  rfl

/-- The first easy-exponent stage, matching the live Rust and EthLib definitions. -/
def easy (a : Fp12) : Fp12 := a.conjugate*a.inverse

/-- The p-squared stage now implemented by source-scheduled Frobenius. -/
def middle (a : Fp12) : Fp12 := (easy a)^(Fp.modulus^2)*easy a

/-- The easy stage is zero or has conjugation as its multiplicative inverse. -/
theorem easy_zero_or_unitary (a : Fp12) : easy a = 0 ∨ easy a*(easy a).conjugate = 1 := by
  rcases TowerInverse.fp12_inverse_or_unit a with hi | hi
  · left
    simp [easy, hi]
  · right
    have hc : a.conjugate*a.inverse.conjugate = 1 := by
      rw [←conjugate_mul, hi, conjugate_one]
    simp only [easy, conjugate_mul, conjugate_conjugate]
    calc
      a.conjugate*a.inverse*(a*a.inverse.conjugate) =
          (a*a.inverse)*(a.conjugate*a.inverse.conjugate) := by ring
      _ = 1 := by rw [hi,hc,mul_one]

/-- The live middle stage is zero or belongs to the cyclotomic subgroup. -/
theorem middle_zero_or_cyclotomic (a : Fp12) :
    middle a = 0 ∨ (middle a)^(Fp.modulus^4-Fp.modulus^2+1) = 1 := by
  rcases easy_zero_or_unitary a with he | he
  · left
    simp [middle, he]
  · right
    have hn : (easy a)^(Fp.modulus^6+1) = 1 := by
      rw [pow_succ, power_six, mul_comm]
      exact he
    have hfactor : (Fp.modulus^2+1)*(Fp.modulus^4-Fp.modulus^2+1) = Fp.modulus^6+1 := by
      decide +kernel
    rw [middle, ←pow_succ, ←pow_mul, hfactor]
    exact hn

#print axioms conjugate_mul
#print axioms conjugate_conjugate
#print axioms conjugate_one
#print axioms power_six
#print axioms easy_zero_or_unitary
#print axioms middle_zero_or_cyclotomic
end Cyclotomic

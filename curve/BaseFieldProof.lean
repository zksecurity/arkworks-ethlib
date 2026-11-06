import BasePrimeProof
import Mathlib.FieldTheory.Finite.Basic

open EthLib.Cryptography.Bls

namespace BaseField

/-- EthLib's executable halving recurrence computes the usual ring power. -/
theorem powNat_eq_pow (n : Nat) (a : Fp) : Fp.powNat a n = a^n := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rw [Fp.powNat.eq_1]
    split
    · subst n
      rfl
    · have hn : 0 < n := by omega
      rw [ih (n/2) (Nat.div_lt_self hn (by decide))]
      have hpow : (a*a)^(n/2) = a^(2*(n/2)) := by rw [pow_mul, pow_two]
      rw [hpow]
      split
      · rw [←pow_succ']
        congr 1
        omega
      · change a^(2*(n/2)) = a^n
        congr 1
        omega

/-- Fermat inversion in the pinned executable specification is a right inverse. -/
theorem inverse_mul (a : Fp) (ha : a ≠ 0) : a*Fp.inverse a = 1 := by
  let _ : Fact Fp.modulus.Prime := ⟨BasePrime.modulus_prime⟩
  rw [Fp.inverse, powNat_eq_pow, ←pow_succ']
  have he : Fp.modulus-2+1 = Fp.modulus-1 := by decide +kernel
  rw [he]
  have hzero : (a : ZMod Fp.modulus) ≠ 0 := by exact ha
  exact ZMod.pow_card_sub_one_eq_one hzero

/-- A binary-GCD implementation need only establish this product equation. -/
theorem inverse_unique (a b : Fp) (ha : a ≠ 0) (hab : a*b = 1) : b = Fp.inverse a := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hi : Fp.inverse a*a = 1 := by rw [mul_comm]; exact inverse_mul a ha
  calc
    b = 1*b := (one_mul b).symm
    _ = (Fp.inverse a*a)*b := by rw [hi]
    _ = Fp.inverse a*(a*b) := mul_assoc _ _ _
    _ = Fp.inverse a := by rw [hab, mul_one]

theorem inverse_zero : Fp.inverse (0 : Fp) = 0 := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  rw [Fp.inverse, powNat_eq_pow]
  exact zero_pow (by decide +kernel : Fp.modulus-2 ≠ 0)

/-- Halving an invariant may cancel two because the base modulus is odd and prime. -/
theorem double_cancel (x y : Fp) (h : (2 : Fp)*x = 2*y) : x = y := by
  let _ : Fact Fp.modulus.Prime := ⟨BasePrime.modulus_prime⟩
  have htwo : (2 : ZMod Fp.modulus) ≠ 0 := by decide +kernel
  exact mul_left_cancel₀ (M₀ := ZMod Fp.modulus) htwo h

#print axioms double_cancel
#print axioms powNat_eq_pow
#print axioms inverse_mul
#print axioms inverse_unique
#print axioms inverse_zero
end BaseField

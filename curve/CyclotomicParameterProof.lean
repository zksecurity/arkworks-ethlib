import CyclotomicExponentRefinement
import HardExponentProof

open Aeneas.Std
open EthLib.Cryptography.Bls
open ConcreteCyclotomicExponent

namespace CyclotomicParameter

local instance : CommRing Fp12 := DodecicField.ringStructure

def order : Nat := Fp.modulus^4-Fp.modulus^2+1

private theorem factor : order*(Fp.modulus^2+1) = Fp.modulus^6+1 := by decide +kernel

/-- On this subgroup, conjugation supplies an inverse without a field-structure assumption. -/
theorem unitary (a : Fp12) (ha : a^order = 1) : a*a.conjugate = 1 := by
  have h : a^(Fp.modulus^6+1) = 1 := by
    rw [←factor, pow_mul, ha, one_pow]
  rw [pow_succ, Cyclotomic.power_six, mul_comm] at h
  exact h

theorem power_root (a : Fp12) (ha : a^order = 1) (e : Nat) : (a^e)^order = 1 := by
  rw [←pow_mul, Nat.mul_comm, pow_mul, ha, one_pow]

/-- Negative NAF digits can be represented by an ordinary nonnegative exponent. -/
theorem conjugate_power (a : Fp12) (ha : a^order = 1) : a.conjugate = a^(order-1) := by
  have he : order-1+1 = order := by unfold order; decide +kernel
  have h : a^(order-1)*a = 1 := by rw [←pow_succ, he, ha]
  calc
    a.conjugate = (a^(order-1)*a)*a.conjugate := by rw [h, one_mul]
    _ = a^(order-1)*(a*a.conjugate) := by rw [mul_assoc]
    _ = a^(order-1) := by rw [unitary a ha, mul_one]

private def weight (bit : Nat) : Nat :=
  if (digitAt bit).val > 0 then 1
  else if (digitAt bit).val < 0 then order-1 else 0

private def tailExponent : Nat → Nat
  | 0 => 0
  | bit+1 => weight bit*2^bit + tailExponent bit

/-- The complete NAF exponent differs from BLS_X by a multiple of the subgroup order. -/
theorem exponent_certificate :
    2^64 + tailExponent 64 = CurveG1.pairing.BLS_X.val + order*2^62 := by decide +kernel

private theorem square_power (a : Fp12) (ha : a^order = 1) (e : Nat) :
    CyclotomicSquare.square (a^e) = a^(e*2) := by
  rw [CyclotomicSquare.square_correct_on_domain _ (Or.inr (power_root a ha e)), pow_mul, pow_two]

/-- Each remaining source digit advances the accumulator's ordinary exponent. -/
private theorem digits_power (a : Fp12) (ha : a^order = 1) (e n : Nat) :
    digits a a.conjugate (a^e) n true = a^(e*2^n+tailExponent n) := by
  induction n generalizing e with
  | zero => simp [digits, tailExponent]
  | succ n ih =>
    rw [digits]
    simp only [Bool.true_or, ↓reduceIte]
    rw [square_power a ha]
    split_ifs with hp hn
    · rw [←pow_succ, ih]
      congr 1
      simp only [tailExponent, weight, ite_eq_left hp, pow_succ]
      ring
    · have hprod : a^(e*2)*a.conjugate = a^(e*2+(order-1)) := by
        rw [conjugate_power a ha, pow_add]
      rw [hprod, ih]
      congr 1
      simp only [tailExponent, weight, ite_eq_right hp, ite_eq_left hn, pow_succ]
      ring
    · rw [ih]
      congr 1
      simp only [tailExponent, weight, ite_eq_right hp, ite_eq_right hn, pow_succ]
      ring

private theorem digits_complete (a : Fp12) (ha : a^order = 1) :
    digits a a.conjugate Fp12.one 65 false = a^CurveG1.pairing.BLS_X.val := by
  have hd : digitAt 64 = 1#i8 := by decide +kernel
  calc
    digits a a.conjugate Fp12.one 65 false = a^(2^64+tailExponent 64) := by
      rw [digits, hd]
      change digits a a.conjugate (1*a) 64 true = _
      rw [one_mul]
      simpa only [pow_one, one_mul] using digits_power a ha 1 64
    _ = a^CurveG1.pairing.BLS_X.val := by
      rw [exponent_certificate, pow_add, pow_mul, ha, one_pow, mul_one]

private theorem zero_test (a : Fp12) :
    (a.c0.isZero && a.c1.isZero) = true ↔ a = 0 := by
  cases a
  simp only [Bool.and_eq_true, ExtensionAlignment.cubic_is_zero]
  change (_ = Fp6.zero ∧ _ = Fp6.zero) ↔ _ = Fp12.zero
  simp only [Fp12.zero, Fp12.mk.injEq]

/-- The full source NAF schedule computes the absolute parameter power on its domain. -/
theorem absolute_power (a : Fp12) (ha : CyclotomicSquare.Admissible a) :
    sourceAbs a = a^CurveG1.pairing.BLS_X.val := by
  unfold sourceAbs
  split_ifs with hz
  · have he := (zero_test a).mp hz
    rw [he, zero_pow (by decide +kernel : CurveG1.pairing.BLS_X.val ≠ 0)]
  · rcases ha with he | he
    · exact False.elim (hz ((zero_test a).mpr he))
    · exact digits_complete a he

/-- Ordinary powers preserve the domain, including zero and exponent zero. -/
theorem power_admissible (a : Fp12) (ha : CyclotomicSquare.Admissible a) (e : Nat) :
    CyclotomicSquare.Admissible (a^e) := by
  rcases ha with hz | hr
  · by_cases he : e = 0
    · right; simp [he]
    · left; rw [hz, zero_pow he]
  · exact Or.inr (power_root a hr e)

theorem conjugate_admissible (a : Fp12) (ha : CyclotomicSquare.Admissible a) :
    CyclotomicSquare.Admissible a.conjugate := by
  rw [←Cyclotomic.power_six]
  exact power_admissible a ha _

theorem product_admissible (a b : Fp12)
    (ha : CyclotomicSquare.Admissible a) (hb : CyclotomicSquare.Admissible b) :
    CyclotomicSquare.Admissible (a*b) := by
  rcases ha with hz | hr
  · left; rw [hz, zero_mul]
  · rcases hb with hz | hs
    · left; rw [hz, mul_zero]
    · right; rw [mul_pow, hr, hs, mul_one]

#print axioms unitary
#print axioms power_root
#print axioms conjugate_power
#print axioms exponent_certificate
#print axioms absolute_power
#print axioms power_admissible
#print axioms conjugate_admissible
#print axioms product_admissible
end CyclotomicParameter

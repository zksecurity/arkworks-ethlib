import HardExponentProof
import TowerFieldInverseProof

open EthLib.Cryptography.Bls

namespace FinalScaling

local instance : CommRing Fp6 := CubicField.ringStructure
noncomputable local instance : Field Fp12 := DodecicDomain.fieldStructure

private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- The easy stage is multiplicative, including at zero. -/
theorem easy_mul (a b : Fp12) : Cyclotomic.easy (a*b) = Cyclotomic.easy a*Cyclotomic.easy b := by
  simp only [Cyclotomic.easy, Cyclotomic.conjugate_mul,
    TowerFieldInverse.fp12_inverse_eq, mul_inv]
  ring

/-- The middle stage is multiplicative, including at zero. -/
theorem middle_mul (a b : Fp12) :
    Cyclotomic.middle (a*b) = Cyclotomic.middle a*Cyclotomic.middle b := by
  simp only [Cyclotomic.middle, easy_mul, mul_pow]
  ring

/-- Final exponentiation preserves multiplication on every executable field value. -/
theorem final_mul (a b : Fp12) :
    finalExponentiation (a*b) = finalExponentiation a*finalExponentiation b := by
  simp only [HardExponent.final_eq_middle_power, middle_mul, mul_pow]

/-- A unitary sign from an anti-conjugate factor disappears in the middle stage. -/
theorem middle_of_conjugate_eq_neg (a : Fp12) (ha : a ≠ 0)
    (hc : a.conjugate = -a) : Cyclotomic.middle a = 1 := by
  have he : Cyclotomic.easy a = -1 := by
    rw [Cyclotomic.easy, hc, TowerFieldInverse.fp12_inverse_eq, neg_mul, mul_inv_cancel₀ ha]
  have hp : (-1 : Fp12)^(Fp.modulus^2) = -1 := by
    have ho : Odd (Fp.modulus^2) := by decide +kernel
    exact ho.neg_one_pow
  rw [Cyclotomic.middle, he, hp]
  ring

/-- Every nonzero anti-conjugate scaling factor is killed by final exponentiation. -/
theorem final_of_conjugate_eq_neg (a : Fp12) (ha : a ≠ 0)
    (hc : a.conjugate = -a) : finalExponentiation a = 1 := by
  rw [HardExponent.final_eq_middle_power, middle_of_conjugate_eq_neg a ha hc, one_pow]

/-- Multiplying any Miller value by a nonzero anti-conjugate factor preserves its final value. -/
theorem final_scale (f a : Fp12) (ha : a ≠ 0) (hc : a.conjugate = -a) :
    finalExponentiation (f*a) = finalExponentiation f := by
  rw [final_mul, final_of_conjugate_eq_neg a ha hc, mul_one]

/-- Final exponentiation preserves the multiplicative identity. -/
theorem final_one : finalExponentiation (1 : Fp12) = 1 := by
  simp only [HardExponent.final_eq_middle_power, Cyclotomic.middle, Cyclotomic.easy,
    Cyclotomic.conjugate_one, TowerFieldInverse.fp12_inverse_eq, inv_one, mul_one, one_pow]

/-- Final exponentiation preserves arbitrary natural powers. -/
theorem final_pow (a : Fp12) (n : Nat) : finalExponentiation (a^n) = (finalExponentiation a)^n := by
  induction n with
  | zero => simp only [pow_zero, final_one]
  | succ n ih => rw [pow_succ, final_mul, ih, pow_succ]

/-- The negative-parameter conjugation preserves equality of final values. -/
theorem final_conjugate (a : Fp12) :
    finalExponentiation a.conjugate = (finalExponentiation a).conjugate := by
  rw [←Cyclotomic.power_six, final_pow, Cyclotomic.power_six]

/-- The sparse scaling shape a·v·w used to relate prepared and affine lines. -/
def lineFactor (a : Fp2) : Fp12 := ⟨Fp6.zero, ⟨Fp2.zero, a, Fp2.zero⟩⟩

theorem lineFactor_nonzero (a : Fp2) (ha : a ≠ Fp2.zero) : lineFactor a ≠ 0 := by
  intro h
  exact ha (congrArg (fun b : Fp12 => b.c1.c1) h)

theorem lineFactor_conjugate (a : Fp2) : (lineFactor a).conjugate = -lineFactor a := by
  apply ext12
  · change Fp6.zero = -Fp6.zero
    simp
  · rfl

/-- Every nonzero factor of the prepared line's sparse shape disappears in the final value. -/
theorem final_lineFactor (f : Fp12) (a : Fp2) (ha : a ≠ Fp2.zero) :
    finalExponentiation (f*lineFactor a) = finalExponentiation f :=
  final_scale f (lineFactor a) (lineFactor_nonzero a ha) (lineFactor_conjugate a)

#print axioms lineFactor_nonzero
#print axioms lineFactor_conjugate
#print axioms final_lineFactor
#print axioms final_one
#print axioms final_pow
#print axioms final_conjugate
#print axioms easy_mul
#print axioms middle_mul
#print axioms final_mul
#print axioms middle_of_conjugate_eq_neg
#print axioms final_of_conjugate_eq_neg
#print axioms final_scale
end FinalScaling

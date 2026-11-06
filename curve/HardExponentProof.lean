import CyclotomicProof
import Generated.CurveG1
import EthLib.Cryptography.Bls.Pairing

open EthLib.Cryptography.Bls

namespace HardExponent

/-- Value of the extracted little-endian signed digits, independently of the exponent loop. -/
def nafValue : Int :=
  ((CurveG1.pairing.BLS_X_NAF.val.zipIdx).map
    (fun (digit, bit) => digit.val * (2 : Int)^bit)).sum

/-- The fixed NAF table recombines to the parameter used by the extracted Rust. -/
theorem naf_value : nafValue = (CurveG1.pairing.BLS_X.val : Int) := by decide +kernel

/-- The exponent obtained by symbolic execution of the pinned arkworks hard chain. -/
def chainExponent : Int :=
  let p := (Fp.modulus : Int)
  let x := -(CurveG1.pairing.BLS_X.val : Int)
  3+(p^2+x^2-1)*(p+x)*(x-1)^2

/-- Arkworks' chain uses the cubed convention relative to EthLib's hard exponent. -/
theorem chain_exponent : chainExponent = 3*(finalExpHard : Int) := by decide +kernel

/-- Exact divisibility needed to put the hard result in the scalar-order subgroup. -/
theorem hard_times_order :
    finalExpHard*Fr.modulus = Fp.modulus^4-Fp.modulus^2+1 := by decide +kernel

local instance : CommRing Fp12 := DodecicField.ringStructure

/-- EthLib factors final exponentiation into its middle stage and ordinary hard power. -/
theorem final_eq_middle_power (a : Fp12) :
    finalExponentiation a = (Cyclotomic.middle a)^finalExpHard := by
  simp only [finalExponentiation, Cyclotomic.middle, Cyclotomic.easy,
    DodecicField.powNat_eq_pow]

/-- Every final value is zero or has order dividing the scalar-field modulus. -/
theorem final_zero_or_order (a : Fp12) :
    finalExponentiation a = 0 ∨ (finalExponentiation a)^Fr.modulus = 1 := by
  rw [final_eq_middle_power]
  rcases Cyclotomic.middle_zero_or_cyclotomic a with h | h
  · left
    rw [h]
    exact zero_pow (by decide +kernel : finalExpHard ≠ 0)
  · right
    rw [←pow_mul, hard_times_order]
    exact h

/-- Since the scalar order is one modulo three, cubing preserves the identity test. -/
theorem cube_eq_one_iff (a : Fp12) (ha : a^Fr.modulus = 1) : a^3 = 1 ↔ a = 1 := by
  constructor
  · intro h
    have he : Fr.modulus = 3*(Fr.modulus/3)+1 := by decide +kernel
    calc
      a = (a^3)^(Fr.modulus/3)*a := by rw [h, one_pow, one_mul]
      _ = a^Fr.modulus := by rw [←pow_mul, ←pow_succ, ←he]
      _ = 1 := ha
  · intro h
    rw [h, one_pow]

/-- The cubed hard-chain convention preserves the final identity predicate, including zero. -/
theorem final_cube_eq_one_iff (a : Fp12) :
    (finalExponentiation a)^3 = 1 ↔ finalExponentiation a = 1 := by
  rcases final_zero_or_order a with h | h
  · have hzero : (0 : Fp12) ≠ 1 := by
      intro hz
      have hv := congrArg (fun x : Fp12 => x.c0.c0.c0.val) hz
      change (0 : Nat) = 1 at hv
      omega
    simp [h,hzero]
  · exact cube_eq_one_iff _ h

private theorem fp_beq_true (a b : Fp) : Fp.beq a b = true ↔ a = b := by
  simp only [Fp.beq, beq_iff_eq, ←Fin.ext_iff]

private theorem fp_zero_true (a : Fp) : Fp.isZero a = true ↔ a = Fp.zero := by
  change (a.val == 0) = true ↔ a = Fp.zero
  rw [beq_iff_eq]
  constructor
  · intro h
    exact Fin.ext h
  · intro h
    exact congrArg Fin.val h

private theorem fp2_beq_true (a b : Fp2) : Fp2.beq a b = true ↔ a = b := by
  cases a; cases b
  simp only [Fp2.beq, Bool.and_eq_true, fp_beq_true, Fp2.mk.injEq]

private theorem fp2_zero_true (a : Fp2) : Fp2.isZero a = true ↔ a = Fp2.zero := by
  cases a
  simp only [Fp2.isZero, Bool.and_eq_true, fp_zero_true, Fp2.zero, Fp2.mk.injEq]

private theorem fp6_beq_true (a b : Fp6) : Fp6.beq a b = true ↔ a = b := by
  cases a; cases b
  simp only [Fp6.beq, Bool.and_eq_true, fp2_beq_true, Fp6.mk.injEq, and_assoc]

private theorem fp6_zero_true (a : Fp6) : Fp6.isZero a = true ↔ a = Fp6.zero := by
  cases a
  simp only [Fp6.isZero, Bool.and_eq_true, fp2_zero_true, Fp6.zero, Fp6.mk.injEq, and_assoc]

/-- EthLib's executable identity check reflects equality with the ring identity. -/
theorem isOne_iff (a : Fp12) : a.isOne = true ↔ a = 1 := by
  rw [show (1 : Fp12) = Fp12.one from rfl]
  cases a
  simp only [Fp12.isOne, Bool.and_eq_true, fp6_beq_true, fp6_zero_true, Fp12.one, Fp12.mk.injEq]

/-- The executable pairing predicate also ignores the hard-chain cube convention. -/
theorem final_cube_isOne (a : Fp12) :
    ((finalExponentiation a)^3).isOne = (finalExponentiation a).isOne := by
  apply Bool.eq_iff_iff.mpr
  rw [isOne_iff, isOne_iff]
  exact final_cube_eq_one_iff a

#print axioms isOne_iff
#print axioms final_cube_isOne
#print axioms naf_value
#print axioms chain_exponent
#print axioms hard_times_order
#print axioms final_eq_middle_power
#print axioms final_zero_or_order
#print axioms cube_eq_one_iff
#print axioms final_cube_eq_one_iff
end HardExponent

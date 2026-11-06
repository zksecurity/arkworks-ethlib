import Fp2DomainProof
import Fp6FrobeniusProof
import Mathlib.Algebra.Polynomial.SpecificDegree

open EthLib.Cryptography.Bls

namespace CubicNonresidue

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

noncomputable local instance : Field Fp2 := QuadraticDomain.fieldStructure

/-- The cubic nonresidue has a nontrivial cubic character in the quadratic field. -/
theorem xi_character :
    CubicField.xi ^ ((Fp.modulus^2-1)/3) = CubicFrobenius.coefficient 2 := by
  have he : (Fp.modulus^2-1)/3 = ((Fp.modulus-1)/3)*(Fp.modulus+1) := by
    decide +kernel
  rw [he, pow_mul, ←QuadraticField.powNat_eq_pow ((Fp.modulus-1)/3) CubicField.xi,
    CubicFrobenius.xi_power, pow_succ, ←QuadraticField.powNat_eq_pow,
    QuadraticField.pow_modulus]
  apply ext2 <;> decide +kernel

/-- No quadratic-field element cubes to the tower's chosen nonresidue. -/
theorem no_cube (a : Fp2) : a^3 ≠ CubicField.xi := by
  intro h
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (3 : Nat) ≠ 0)] at h
    have hc := congrArg Fp2.c0 h
    have hx : (0 : Fp) ≠ 1 := by decide +kernel
    exact hx hc
  have hp : a^(Fp.modulus^2) = a := by
    have hpower := QuadraticField.pow_modulus_pow a 2
    simpa only [QuadraticField.powNat_eq_pow, show (2 : Nat)%2 = 0 from rfl, ite_true] using hpower
  have hone : a^(Fp.modulus^2-1) = 1 := by
    apply mul_right_cancel₀ ha
    rw [one_mul, ←pow_succ]
    have he : Fp.modulus^2-1+1 = Fp.modulus^2 := by decide +kernel
    rw [he, hp]
  have he : 3*((Fp.modulus^2-1)/3) = Fp.modulus^2-1 := by decide +kernel
  have hc : CubicFrobenius.coefficient 2 = (1 : Fp2) := by
    rw [←xi_character, ←h, ←pow_mul, he, hone]
  have hn : (CubicFrobenius.coefficient 2).c0 ≠ (1 : Fp2).c0 := by decide +kernel
  exact hn (congrArg Fp2.c0 hc)

/-- The polynomial defining the cubic tower is irreducible over the quadratic field. -/
theorem irreducible :
    Irreducible ((Polynomial.X : Polynomial Fp2)^3 - Polynomial.C CubicField.xi) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp only [Polynomial.natDegree_X_pow_sub_C,
      Finset.mem_Icc]
    omega
  · intro a ha
    apply no_cube a
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using ha

#print axioms irreducible
#print axioms xi_character
#print axioms no_cube
end CubicNonresidue

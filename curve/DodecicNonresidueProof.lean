import Fp6DomainProof
import Fp12FrobeniusProof

open EthLib.Cryptography.Bls

namespace DodecicNonresidue

local instance : CommRing Fp2 := QuadraticField.ringStructure
noncomputable local instance : Field Fp6 := CubicDomain.fieldStructure
local instance : CommRing Fp12 := DodecicField.ringStructure

private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem embed_mul_w (a : Fp6) :
    (DodecicField.ofFp6Hom a * DodecicField.w).c1 = a := by
  simp [DodecicField.w]

private theorem neg_w : (-DodecicField.w).c1 = (-1 : Fp6) := rfl

/-- The tower generator has quadratic character minus one in the cubic field. -/
theorem v_character : Fp6.v ^ ((Fp.modulus^6-1)/2) = (-1 : Fp6) := by
  have hw : DodecicField.w^2 = DodecicField.ofFp6Hom Fp6.v := by
    apply ext12 <;> simp [DodecicField.w, pow_succ]
  have hf : DodecicField.w^(Fp.modulus^6) = -DodecicField.w := by
    rw [←DodecicField.powNat_eq_pow, ←DodecicFrobenius.map_eq_power]
    apply ext12
    all_goals simp [DodecicFrobenius.map, DodecicField.w,
      DodecicFrobenius.coefficient]
    all_goals first | rfl | decide +kernel
  have he : Fp.modulus^6 = 2*((Fp.modulus^6-1)/2)+1 := by decide +kernel
  rw [he, pow_succ, pow_mul, hw, ←map_pow] at hf
  have hc := congrArg Fp12.c1 hf
  simpa only [embed_mul_w, neg_w] using hc

/-- Every cubic-field element is fixed by the sixth base-field Frobenius. -/
theorem pow_card (a : Fp6) : a^(Fp.modulus^6) = a := by
  rw [←CubicFrobenius.map_eq_power]
  have hbase (b : Fp2) : Fp2.powNat b (Fp.modulus^6) = b := by
    simpa only [show (6 : Nat)%2 = 0 from rfl, ite_true] using
      QuadraticField.pow_modulus_pow b 6
  have hc : CubicFrobenius.coefficient 6 = (1 : Fp2) := rfl
  simp only [CubicFrobenius.map, hbase, hc, mul_one]

/-- No cubic-field element squares to the degree-twelve tower's nonresidue. -/
theorem no_square (a : Fp6) : a^2 ≠ Fp6.v := by
  intro h
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : Nat) ≠ 0)] at h
    have hc := congrArg (fun b : Fp6 => b.c1.c0) h
    have hn : Fp.zero ≠ Fp.one := by decide +kernel
    exact hn hc
  have hone : a^(Fp.modulus^6-1) = 1 := by
    apply mul_right_cancel₀ ha
    rw [one_mul, ←pow_succ]
    have he : Fp.modulus^6-1+1 = Fp.modulus^6 := by decide +kernel
    rw [he, pow_card]
  have he : 2*((Fp.modulus^6-1)/2) = Fp.modulus^6-1 := by decide +kernel
  have hc : (-1 : Fp6) = 1 := by rw [←v_character, ←h, ←pow_mul, he, hone]
  have hn : (-1 : Fp6).c0.c0 ≠ (1 : Fp6).c0.c0 := by decide +kernel
  exact hn (congrArg (fun b : Fp6 => b.c0.c0) hc)

/-- The degree-twelve tower polynomial is irreducible over the cubic field. -/
theorem irreducible :
    Irreducible ((Polynomial.X : Polynomial Fp6)^2 - Polynomial.C Fp6.v) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp only [Polynomial.natDegree_X_pow_sub_C, Finset.mem_Icc]
    omega
  · intro a ha
    apply no_square a
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using ha

#print axioms irreducible
#print axioms v_character
#print axioms pow_card
#print axioms no_square
end DodecicNonresidue

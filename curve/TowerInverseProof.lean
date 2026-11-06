import Fp12FieldProof

open EthLib.Cryptography.Bls

namespace TowerInverse

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
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

@[simp] private theorem sub2 (a b : Fp2) : Fp2.sub a b = a + -b := by
  apply ext2
  · change a.c0-b.c0 = a.c0 + -b.c0
    ring
  · change a.c1-b.c1 = a.c1 + -b.c1
    ring

@[simp] private theorem xi_mul (a : Fp2) : a.mulByOnePlusI = CubicField.xi*a := by
  apply ext2
  · change a.c0-a.c1 = 1*a.c0-1*a.c1
    ring
  · change a.c0+a.c1 = 1*a.c1+1*a.c0
    ring

/-- The executable quadratic inverse is either zero or a multiplicative inverse. -/
theorem fp2_inverse_or_unit (a : Fp2) : a.inverse = 0 ∨ a*a.inverse = 1 := by
  let n : Fp := a.c0*a.c0+a.c1*a.c1
  by_cases hn : n = 0
  · left
    have hi : Fp.inverse n = 0 := by rw [hn, BaseField.inverse_zero]
    apply ext2
    · change a.c0*Fp.inverse n = 0
      rw [hi, mul_zero]
    · change -(a.c1*Fp.inverse n) = 0
      rw [hi, mul_zero, neg_zero]
  · right
    have hi := BaseField.inverse_mul n hn
    apply ext2
    · change a.c0*(a.c0*Fp.inverse n)-a.c1*(-(a.c1*Fp.inverse n)) = 1
      dsimp [n] at hi
      linear_combination hi
    · change a.c0*(-(a.c1*Fp.inverse n))+a.c1*(a.c0*Fp.inverse n) = 0
      ring

/-- The executable cubic inverse satisfies the same zero-or-inverse alternative. -/
theorem fp6_inverse_or_unit (a : Fp6) : a.inverse = 0 ∨ a*a.inverse = 1 := by
  let t0 := Fp2.sub (a.c0*a.c0) (a.c1*a.c2).mulByOnePlusI
  let t1 := Fp2.sub (a.c2*a.c2).mulByOnePlusI (a.c0*a.c1)
  let t2 := Fp2.sub (a.c1*a.c1) (a.c0*a.c2)
  let det := a.c0*t0+(a.c2*t1).mulByOnePlusI+(a.c1*t2).mulByOnePlusI
  change (⟨t0*det.inverse,t1*det.inverse,t2*det.inverse⟩ : Fp6) = 0 ∨
    a*⟨t0*det.inverse,t1*det.inverse,t2*det.inverse⟩ = 1
  rcases fp2_inverse_or_unit det with hi | hi
  · left
    apply ext6
    all_goals change _*det.inverse = 0
    all_goals rw [hi, mul_zero]
  · right
    apply ext6
    all_goals simp [t0,t1,t2,det] at hi ⊢
    · linear_combination hi
    all_goals ring

/-- The executable degree-twelve inverse returns zero or an actual inverse. -/
theorem fp12_inverse_or_unit (a : Fp12) : a.inverse = 0 ∨ a*a.inverse = 1 := by
  let norm := Fp6.sub (a.c0*a.c0) (a.c1*a.c1).mulByV
  change (⟨a.c0*norm.inverse,-(a.c1*norm.inverse)⟩ : Fp12) = 0 ∨
    a*⟨a.c0*norm.inverse,-(a.c1*norm.inverse)⟩ = 1
  rcases fp6_inverse_or_unit norm with hi | hi
  · left
    apply ext12
    · change a.c0*norm.inverse = 0
      rw [hi, mul_zero]
    · change -(a.c1*norm.inverse) = 0
      rw [hi, mul_zero, neg_zero]
  · right
    apply ext12
    all_goals simp [norm, CubicField.sub_eq_add_neg, CubicField.mulByV_eq] at hi ⊢
    · linear_combination hi
    all_goals ring

#print axioms fp2_inverse_or_unit
#print axioms fp6_inverse_or_unit
#print axioms fp12_inverse_or_unit
end TowerInverse

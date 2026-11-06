import Fp12DomainProof
import TowerInverseProof

open EthLib.Cryptography.Bls

namespace TowerFieldInverse

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
noncomputable local instance : Field Fp2 := QuadraticDomain.fieldStructure
noncomputable local instance : Field Fp6 := CubicDomain.fieldStructure
noncomputable local instance : Field Fp12 := DodecicDomain.fieldStructure

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem ext6 (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl

private theorem sub2 (a b : Fp2) : Fp2.sub a b = a + -b := by
  apply ext2
  · change a.c0-b.c0 = a.c0 + -b.c0
    ring
  · change a.c1-b.c1 = a.c1 + -b.c1
    ring

private theorem xi_mul (a : Fp2) : a.mulByOnePlusI = CubicField.xi*a := by
  apply ext2
  · change a.c0-a.c1 = 1*a.c0-1*a.c1
    ring
  · change a.c0+a.c1 = 1*a.c1+1*a.c0
    ring

/-- The adjugate of a nonzero cubic element cannot vanish. -/
theorem adjugate_nonzero (a : Fp6) (ha : a ≠ 0) :
    (⟨a.c0*a.c0 + -(CubicField.xi*(a.c1*a.c2)),
      CubicField.xi*(a.c2*a.c2) + -(a.c0*a.c1),
      a.c1*a.c1 + -(a.c0*a.c2)⟩ : Fp6) ≠ 0 := by
  intro h
  have h0 := congrArg Fp6.c0 h
  have h1 := congrArg Fp6.c1 h
  have h2 := congrArg Fp6.c2 h
  change a.c0*a.c0 + -(CubicField.xi*(a.c1*a.c2)) = 0 at h0
  change CubicField.xi*(a.c2*a.c2) + -(a.c0*a.c1) = 0 at h1
  change a.c1*a.c1 + -(a.c0*a.c2) = 0 at h2
  by_cases hz : a.c2 = 0
  · have hx : a.c0 = 0 := by
      simp only [hz, mul_zero, neg_zero, add_zero] at h0
      exact (mul_self_eq_zero.mp h0)
    have hy : a.c1 = 0 := by
      simp only [hz, mul_zero, neg_zero, add_zero] at h2
      exact (mul_self_eq_zero.mp h2)
    exact ha (ext6 a 0 hx hy hz)
  · apply CubicNonresidue.no_cube (a.c1*a.c2⁻¹)
    have hc : a.c1^3 = CubicField.xi*a.c2^3 := by
      linear_combination a.c1*h2 + (-a.c2)*h1
    field_simp
    simpa only [mul_comm] using hc

/-- The determinant in the executable cubic inverse is nonzero on nonzero input. -/
theorem fp6_determinant_nonzero (a : Fp6) (ha : a ≠ 0) :
    a.c0*(a.c0*a.c0 + -(CubicField.xi*(a.c1*a.c2))) +
      CubicField.xi*(a.c2*(CubicField.xi*(a.c2*a.c2) + -(a.c0*a.c1))) +
      CubicField.xi*(a.c1*(a.c1*a.c1 + -(a.c0*a.c2))) ≠ 0 := by
  intro hd
  let adj : Fp6 := ⟨a.c0*a.c0 + -(CubicField.xi*(a.c1*a.c2)),
    CubicField.xi*(a.c2*a.c2) + -(a.c0*a.c1), a.c1*a.c1 + -(a.c0*a.c2)⟩
  have hprod : a*adj = 0 := by
    apply ext6
    · simp [adj]
      linear_combination hd
    · simp [adj]
      ring
    · simp [adj]
      ring
  exact adjugate_nonzero a ha ((mul_eq_zero.mp hprod).resolve_left ha)

/-- EthLib's cubic inverse inverts every nonzero cubic element. -/
theorem fp6_inverse_mul (a : Fp6) (ha : a ≠ 0) : a*a.inverse = 1 := by
  let t0 := a.c0*a.c0 + -(CubicField.xi*(a.c1*a.c2))
  let t1 := CubicField.xi*(a.c2*a.c2) + -(a.c0*a.c1)
  let t2 := a.c1*a.c1 + -(a.c0*a.c2)
  let det := a.c0*t0 + CubicField.xi*(a.c2*t1) + CubicField.xi*(a.c1*t2)
  have hd : det ≠ 0 := fp6_determinant_nonzero a ha
  have hi := QuadraticDomain.inverse_mul det hd
  have hexpr : a.inverse = (⟨t0*det.inverse, t1*det.inverse, t2*det.inverse⟩ : Fp6) := by
    simp only [Fp6.inverse, HSub.hSub, Sub.sub, sub2, xi_mul]
    rfl
  rw [hexpr]
  generalize det.inverse = d at hi ⊢
  change (a.c0*t0 + CubicField.xi*(a.c2*t1) + CubicField.xi*(a.c1*t2))*d = 1 at hi
  dsimp only [t0, t1, t2] at hi
  apply ext6
  all_goals simp [t0, t1, t2]
  · linear_combination hi
  all_goals ring

private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- The norm in the executable degree-twelve inverse is nonzero on nonzero input. -/
theorem fp12_norm_nonzero (a : Fp12) (ha : a ≠ 0) :
    a.c0*a.c0 + -(Fp6.v*(a.c1*a.c1)) ≠ 0 := by
  intro hn
  by_cases hz : a.c1 = 0
  · have hx : a.c0 = 0 := by
      simp only [hz, mul_zero, neg_zero, add_zero] at hn
      exact mul_self_eq_zero.mp hn
    exact ha (ext12 a 0 hx hz)
  · apply DodecicNonresidue.no_square (a.c0*a.c1⁻¹)
    field_simp
    linear_combination hn

private theorem sub6 (a b : Fp6) : Fp6.sub a b = a + -b :=
  CubicField.sub_eq_add_neg a b

/-- EthLib's degree-twelve inverse inverts every nonzero input. -/
theorem fp12_inverse_mul (a : Fp12) (ha : a ≠ 0) : a*a.inverse = 1 := by
  let n := a.c0*a.c0 + -(Fp6.v*(a.c1*a.c1))
  have hn : n ≠ 0 := fp12_norm_nonzero a ha
  have hi := fp6_inverse_mul n hn
  have hexpr : a.inverse = (⟨a.c0*n.inverse, -(a.c1*n.inverse)⟩ : Fp12) := by
    simp only [Fp12.inverse, HSub.hSub, Sub.sub, sub6, CubicField.mulByV_eq]
    rfl
  rw [hexpr]
  generalize n.inverse = d at hi ⊢
  change (a.c0*a.c0 + -(Fp6.v*(a.c1*a.c1)))*d = 1 at hi
  apply ext12
  · simp
    linear_combination hi
  · simp
    ring

/-- The executable cubic inverse is the mathematical field inverse, including at zero. -/
theorem fp6_inverse_eq (a : Fp6) : a.inverse = a⁻¹ := by
  by_cases ha : a = 0
  · subst a
    rw [inv_zero]
    apply ext6 <;> simp [Fp6.inverse, HSub.hSub, Sub.sub]
  · exact mul_left_cancel₀ ha ((fp6_inverse_mul a ha).trans (mul_inv_cancel₀ ha).symm)

/-- The executable degree-twelve inverse is the mathematical field inverse. -/
theorem fp12_inverse_eq (a : Fp12) : a.inverse = a⁻¹ := by
  by_cases ha : a = 0
  · subst a
    rw [inv_zero]
    apply ext12 <;> simp [Fp12.inverse]
  · exact mul_left_cancel₀ ha ((fp12_inverse_mul a ha).trans (mul_inv_cancel₀ ha).symm)

#print axioms fp12_norm_nonzero
#print axioms fp12_inverse_mul
#print axioms fp6_inverse_eq
#print axioms fp12_inverse_eq
#print axioms fp6_inverse_mul
#print axioms adjugate_nonzero
#print axioms fp6_determinant_nonzero
end TowerFieldInverse

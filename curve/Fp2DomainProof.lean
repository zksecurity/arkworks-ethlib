import Fp2FieldProof
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.IntegralDomain

open EthLib.Cryptography.Bls

namespace QuadraticDomain

local instance : Fact Fp.modulus.Prime := ⟨BasePrime.modulus_prime⟩
local instance : Field Fp := inferInstanceAs (Field (ZMod Fp.modulus))
local instance : CommRing Fp2 := QuadraticField.ringStructure

/-- The quadratic norm is anisotropic because −1 is not a square in the base field. -/
def norm (a : Fp2) : Fp := a.c0*a.c0+a.c1*a.c1

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- A zero norm forces both coefficients to vanish. -/
theorem norm_eq_zero (a : Fp2) (h : norm a = 0) : a = 0 := by
  have hxy : a.c0^2 = -a.c1^2 := by
    unfold norm at h
    linear_combination h
  have hy : a.c1 = 0 := by
    by_contra hn
    have hns : ¬ IsSquare (-1 : Fp) := by
      rw [FiniteField.isSquare_neg_one_iff]
      simp only [Fintype.card_fin]
      decide +kernel
    have hr : (a.c0*a.c1⁻¹)^2 = -1 := by
      field_simp
      exact hxy
    exact hns ⟨a.c0*a.c1⁻¹, by rw [←pow_two, hr]⟩
  have hx : a.c0 = 0 := by
    rw [hy, zero_pow (by decide : (2 : Nat) ≠ 0), neg_zero] at hxy
    exact (pow_eq_zero_iff (by decide : (2 : Nat) ≠ 0)).mp hxy
  exact ext2 a 0 hx hy

/-- The norm preserves multiplication in the unchanged executable ring. -/
theorem norm_mul (a b : Fp2) : norm (a*b) = norm a*norm b := by
  change (a.c0*b.c0-a.c1*b.c1)*(a.c0*b.c0-a.c1*b.c1)+
      (a.c0*b.c1+a.c1*b.c0)*(a.c0*b.c1+a.c1*b.c0) =
    (a.c0*a.c0+a.c1*a.c1)*(b.c0*b.c0+b.c1*b.c1)
  ring

local instance : Nontrivial Fp2 := ⟨⟨0, 1, by
  intro h
  have he := congrArg Fp2.c0 h
  have hn : Fp.zero ≠ Fp.one := by decide +kernel
  exact hn he⟩⟩

local instance : NoZeroDivisors Fp2 := ⟨by
  intro a b hab
  have h : norm a*norm b = 0 := by
    rw [←norm_mul, hab]
    decide +kernel
  rcases mul_eq_zero.mp h with ha | hb
  · exact Or.inl (norm_eq_zero a ha)
  · exact Or.inr (norm_eq_zero b hb)⟩

local instance domainStructure : IsDomain Fp2 :=
  (isDomain_iff_noZeroDivisors_and_nontrivial Fp2).mpr ⟨inferInstance, inferInstance⟩

private def pairEquiv : (Fp × Fp) ≃ Fp2 where
  toFun p := ⟨p.1, p.2⟩
  invFun p := (p.c0, p.c1)
  left_inv := by rintro ⟨x,y⟩; rfl
  right_inv := by intro p; cases p; rfl

noncomputable local instance : Fintype Fp2 := Fintype.ofEquiv (Fp × Fp) pairEquiv

/-- A field structure on EthLib’s unchanged addition and multiplication. -/
@[instance_reducible] noncomputable def fieldStructure : Field Fp2 := by
  classical
  exact Fintype.fieldOfDomain Fp2

attribute [local instance] fieldStructure

/-- The norm formula used by EthLib inverts every nonzero quadratic element. -/
theorem inverse_mul (a : Fp2) (ha : a ≠ 0) : a * a.inverse = 1 := by
  have hn : norm a ≠ 0 := fun h => ha (norm_eq_zero a h)
  have hi := BaseField.inverse_mul (norm a) hn
  apply ext2
  · change a.c0*(a.c0*Fp.inverse (norm a))-
      a.c1*(-(a.c1*Fp.inverse (norm a))) = Fp.one
    have hone : Fp.one = (1 : Fp) := by decide +kernel
    rw [hone]
    dsimp [norm] at hi ⊢
    linear_combination hi
  · change a.c0*(-(a.c1*Fp.inverse (norm a)))+
      a.c1*(a.c0*Fp.inverse (norm a)) = Fp.zero
    have hzero : Fp.zero = (0 : Fp) := by decide +kernel
    rw [hzero]
    ring

/-- EthLib's executable inverse agrees with the mathematical field inverse. -/
theorem inverse_eq (a : Fp2) : a.inverse = a⁻¹ := by
  by_cases ha : a = 0
  · subst a
    rw [inv_zero]
    apply ext2
    · change (0 : Fp)*Fp.inverse _ = 0
      exact zero_mul _
    · change -((0 : Fp)*Fp.inverse _) = 0
      rw [zero_mul, neg_zero]
  · exact (mul_left_cancel₀ ha ((inverse_mul a ha).trans (mul_inv_cancel₀ ha).symm))

#print axioms fieldStructure
#print axioms norm_eq_zero
#print axioms norm_mul
#print axioms inverse_mul
#print axioms inverse_eq
end QuadraticDomain

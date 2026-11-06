import BaseFieldProof
import EthLib.Cryptography.Bls.Fp2
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra

open EthLib.Cryptography.Bls

namespace QuadraticField

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
local instance : Zero Fp2 := ⟨Fp2.zero⟩
local instance : One Fp2 := ⟨Fp2.one⟩

private theorem ext (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a
  cases b
  cases h0
  cases h1
  rfl

@[simp] private theorem add_c0 (a b : Fp2) : (a+b).c0 = a.c0+b.c0 := rfl
@[simp] private theorem add_c1 (a b : Fp2) : (a+b).c1 = a.c1+b.c1 := rfl
@[simp] private theorem mul_c0 (a b : Fp2) : (a*b).c0 = a.c0*b.c0-a.c1*b.c1 := rfl
@[simp] private theorem mul_c1 (a b : Fp2) : (a*b).c1 = a.c0*b.c1+a.c1*b.c0 := rfl
@[simp] private theorem neg_c0 (a : Fp2) : (-a).c0 = -a.c0 := rfl
@[simp] private theorem neg_c1 (a : Fp2) : (-a).c1 = -a.c1 := rfl
@[simp] private theorem zero_c0 : (0 : Fp2).c0 = 0 := rfl
@[simp] private theorem zero_c1 : (0 : Fp2).c1 = 0 := rfl
@[simp] private theorem one_c0 : (1 : Fp2).c0 = 1 := rfl
@[simp] private theorem one_c1 : (1 : Fp2).c1 = 0 := rfl

/-- Ring laws for the unchanged executable coefficient operations. -/
abbrev ringStructure : CommRing Fp2 := by
  apply CommRing.ofMinimalAxioms
  all_goals intros
  all_goals apply ext
  all_goals simp only [add_c0, add_c1, mul_c0, mul_c1, neg_c0, neg_c1,
    zero_c0, zero_c1, one_c0, one_c1]
  all_goals ring

attribute [local instance] ringStructure

/-- The executable halving recurrence agrees with ordinary ring exponentiation. -/
theorem powNat_eq_pow (n : Nat) (a : Fp2) : Fp2.powNat a n = a^n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rw [Fp2.powNat.eq_1]
    split
    · subst n; rfl
    · have hn : 0 < n := by omega
      rw [ih (n/2) (Nat.div_lt_self hn (by decide))]
      have hp : (a*a)^(n/2) = a^(2*(n/2)) := by rw [pow_mul, pow_two]
      rw [hp]
      split
      · change a*a^(2*(n/2)) = a^n
        rw [←pow_succ']; congr 1; omega
      · change a^(2*(n/2)) = a^n
        congr 1
        omega

/-- The coefficient embedding preserves the executable ring operations. -/
def ofFpHom : Fp →+* Fp2 where
  toFun := Fp2.ofFp
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := by
    apply ext
    · change a+b = a+b
      rfl
    · change (0 : Fp) = 0+0
      ring
  map_mul' a b := by
    apply ext
    · change a*b = a*b-0*0
      ring
    · change (0 : Fp) = a*0+0*b
      ring

local instance : Fact Fp.modulus.Prime := ⟨BasePrime.modulus_prime⟩
local instance : CharP Fp Fp.modulus := by
  exact (inferInstance : CharP (ZMod Fp.modulus) Fp.modulus)

local instance : CharP Fp2 Fp.modulus :=
  charP_of_injective_ringHom (f := ofFpHom)
    (fun _ _ h => congrArg Fp2.c0 h) Fp.modulus

/-- The quadratic ring has the base field's prime characteristic. -/
abbrev characteristic : CharP Fp2 Fp.modulus := inferInstance

private theorem i_pow_modulus : (Fp2.i : Fp2)^Fp.modulus = -Fp2.i := by
  have hfour : (Fp2.i : Fp2)^4 = 1 := by
    apply ext <;> decide +kernel
  have hthree : (Fp2.i : Fp2)^3 = -Fp2.i := by
    apply ext <;> decide +kernel
  have he : Fp.modulus = 4*(Fp.modulus/4)+3 := by decide +kernel
  rw [he, pow_add, pow_mul, hfour, one_pow, one_mul]
  exact hthree

/-- The executable quadratic Frobenius is the modulus power on every input. -/
theorem pow_modulus (a : Fp2) : Fp2.powNat a Fp.modulus = Fp2.conjugate a := by
  rw [powNat_eq_pow]
  have hbase (x : Fp) : x^Fp.modulus = x := by
    exact ZMod.pow_card (p := Fp.modulus) x
  have hre : a = ofFpHom a.c0 + ofFpHom a.c1*Fp2.i := by
    apply ext
    · change a.c0 = a.c0 + (a.c1*0-0*1)
      ring
    · change a.c1 = 0+(a.c1*1+0*0)
      ring
  calc
    a^Fp.modulus = (ofFpHom a.c0 + ofFpHom a.c1*Fp2.i)^Fp.modulus := by rw [←hre]
    _ = ofFpHom a.c0 + ofFpHom a.c1*(-Fp2.i) := by
      rw [add_pow_char, mul_pow, i_pow_modulus, ←map_pow, ←map_pow,
        hbase, hbase]
    _ = Fp2.conjugate a := by
      apply ext
      · change a.c0+(a.c1*(-0)-0*(-1)) = a.c0
        ring
      · change 0+(a.c1*(-1)+0*(-0)) = -a.c1
        ring

/-- Frobenius powers alternate between the identity and conjugation. -/
theorem pow_modulus_pow (a : Fp2) (k : Nat) :
    Fp2.powNat a (Fp.modulus^k) = if k%2 = 0 then a else Fp2.conjugate a := by
  rw [powNat_eq_pow]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ←powNat_eq_pow, pow_modulus, ih]
    have hconj : Fp2.conjugate (Fp2.conjugate a) = a := by
      apply ext
      · rfl
      · change -(-a.c1) = a.c1
        ring
    by_cases he : k%2 = 0
    · have hn : (k+1)%2 ≠ 0 := by omega
      simp only [he, hn, ite_true, ite_false]
    · have hn : (k+1)%2 = 0 := by omega
      simp only [he, hn, ite_true, ite_false, hconj]

/-- The modulus-power view makes conjugation multiplicative. -/
theorem conjugate_mul (a b : Fp2) : (a*b).conjugate = a.conjugate*b.conjugate := by
  rw [←pow_modulus, powNat_eq_pow, mul_pow,
    ←powNat_eq_pow Fp.modulus a, ←powNat_eq_pow Fp.modulus b, pow_modulus, pow_modulus]

theorem power_step (a : Fp2) (k : Nat) :
    Fp2.powNat a (Fp.modulus^(k+1)) = (Fp2.powNat a (Fp.modulus^k)).conjugate := by
  rw [powNat_eq_pow, pow_succ, pow_mul, ←powNat_eq_pow, pow_modulus, powNat_eq_pow]

#print axioms conjugate_mul
#print axioms power_step
#print axioms characteristic
#print axioms ofFpHom
#print axioms pow_modulus_pow
#print axioms pow_modulus
#print axioms ringStructure
#print axioms powNat_eq_pow
end QuadraticField

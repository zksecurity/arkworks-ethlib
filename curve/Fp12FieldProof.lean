import Fp6FieldProof
import EthLib.Cryptography.Bls.Fp12

open EthLib.Cryptography.Bls

namespace DodecicField

local instance : CommRing Fp2 := QuadraticField.ringStructure
local instance : CommRing Fp6 := CubicField.ringStructure
local instance : Zero Fp12 := ⟨Fp12.zero⟩
local instance : One Fp12 := ⟨Fp12.one⟩

private theorem ext (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

@[simp] private theorem fp6_one : Fp6.one = (1 : Fp6) := rfl
@[simp] private theorem fp6_zero : Fp6.zero = (0 : Fp6) := rfl
@[simp] private theorem add_c0 (a b : Fp12) : (a+b).c0 = a.c0+b.c0 := rfl
@[simp] private theorem add_c1 (a b : Fp12) : (a+b).c1 = a.c1+b.c1 := rfl
@[simp] private theorem neg_c0 (a : Fp12) : (-a).c0 = -a.c0 := rfl
@[simp] private theorem neg_c1 (a : Fp12) : (-a).c1 = -a.c1 := rfl
@[simp] private theorem zero_c0 : (0 : Fp12).c0 = 0 := rfl
@[simp] private theorem zero_c1 : (0 : Fp12).c1 = 0 := rfl
@[simp] private theorem one_c0 : (1 : Fp12).c0 = 1 := rfl
@[simp] private theorem one_c1 : (1 : Fp12).c1 = 0 := rfl
@[simp] private theorem mul_c0 (a b : Fp12) :
    (a*b).c0 = a.c0*b.c0+Fp6.v*(a.c1*b.c1) := by
  change a.c0*b.c0+(a.c1*b.c1).mulByV = _
  rw [CubicField.mulByV_eq]

@[simp] private theorem mul_c1 (a b : Fp12) :
    (a*b).c1 = a.c0*b.c1+a.c1*b.c0 := by
  change Fp6.sub (Fp6.sub ((a.c0+a.c1)*(b.c0+b.c1)) (a.c0*b.c0)) (a.c1*b.c1) = _
  rw [CubicField.sub_eq_add_neg, CubicField.sub_eq_add_neg]
  ring

/-- Ring laws for the unchanged executable degree-twelve coefficient formulas. -/
abbrev ringStructure : CommRing Fp12 := by
  apply CommRing.ofMinimalAxioms
  all_goals intros
  all_goals apply ext
  all_goals simp only [add_c0, add_c1, mul_c0, mul_c1, neg_c0, neg_c1,
    zero_c0, zero_c1, one_c0, one_c1]
  all_goals ring

attribute [local instance] ringStructure

/-- The cubic coefficient embedding preserves the executable ring operations. -/
def ofFp6Hom : Fp6 →+* Fp12 where
  toFun x := ⟨x,0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := by apply ext <;> simp
  map_mul' a b := by apply ext <;> simp

@[simp] private theorem hom_c0 (a : Fp6) : (ofFp6Hom a).c0 = a := rfl
@[simp] private theorem hom_c1 (a : Fp6) : (ofFp6Hom a).c1 = 0 := rfl

local instance : Fact Fp.modulus.Prime := ⟨BasePrime.modulus_prime⟩
local instance : CharP Fp6 Fp.modulus := CubicField.characteristic

/-- Prime characteristic is inherited through the cubic coefficient embedding. -/
abbrev characteristic : CharP Fp12 Fp.modulus :=
  charP_of_injective_ringHom (f := ofFp6Hom)
    (fun _ _ h => congrArg Fp12.c0 h) Fp.modulus

attribute [local instance] characteristic

/-- The degree-twelve tower generator satisfies w squared equals v. -/
def w : Fp12 := ⟨0,1⟩

private theorem w_square : w^2 = ofFp6Hom Fp6.v := by
  apply ext
  all_goals simp [w, pow_succ]

private theorem decomposition (a : Fp12) : a = ofFp6Hom a.c0 + ofFp6Hom a.c1*w := by
  apply ext
  all_goals simp [w]

/-- The symbolic modulus-power map before replacing the nonresidue power by a table entry. -/
def frobenius (a : Fp12) : Fp12 :=
  ⟨a.c0^Fp.modulus, a.c1^Fp.modulus*CubicField.ofFp2Hom
    (Fp2.powNat CubicField.xi ((Fp.modulus-1)/6))⟩

/-- Characteristic p and the two tower relations determine the full modulus-power map. -/
theorem pow_modulus (a : Fp12) : a^Fp.modulus = frobenius a := by
  have hw : w^Fp.modulus = ofFp6Hom (CubicField.ofFp2Hom
      (Fp2.powNat CubicField.xi ((Fp.modulus-1)/6)))*w := by
    have he : Fp.modulus = 2*(3*((Fp.modulus-1)/6))+1 := by decide +kernel
    calc
      w^Fp.modulus = w^(2*(3*((Fp.modulus-1)/6))+1) := by rw [←he]
      _ = _ := by
        rw [pow_add, pow_mul, w_square, pow_one, ←map_pow, pow_mul,
          CubicField.v_cube, ←map_pow, ←QuadraticField.powNat_eq_pow]
  calc
    a^Fp.modulus = (ofFp6Hom a.c0+ofFp6Hom a.c1*w)^Fp.modulus := by rw [←decomposition a]
    _ = ofFp6Hom (a.c0^Fp.modulus)+ofFp6Hom (a.c1^Fp.modulus)*
        (ofFp6Hom (CubicField.ofFp2Hom (Fp2.powNat CubicField.xi ((Fp.modulus-1)/6)))*w) := by
      rw [add_pow_char, mul_pow, hw, ←map_pow, ←map_pow]
    _ = frobenius a := by
      apply ext
      all_goals simp [frobenius, w, -map_pow]

/-- The pinned executable power recurrence agrees with the proved ring power. -/
theorem powNat_eq_pow (n : Nat) (a : Fp12) : Fp12.powNat a n = a^n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rw [Fp12.powNat.eq_1]
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

#print axioms ringStructure
#print axioms ofFp6Hom
#print axioms characteristic
#print axioms pow_modulus
#print axioms powNat_eq_pow
end DodecicField

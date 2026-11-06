import Fp2FieldProof
import EthLib.Cryptography.Bls.Fp6

open EthLib.Cryptography.Bls

namespace CubicField

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
local instance : CommRing Fp2 := QuadraticField.ringStructure
local instance : Zero Fp6 := ⟨Fp6.zero⟩
local instance : One Fp6 := ⟨Fp6.one⟩

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem ext (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl

@[simp] private theorem fp2_one : Fp2.one = (1 : Fp2) := rfl

@[simp] private theorem fp2_zero : Fp2.zero = (0 : Fp2) := rfl

/-- The cubic tower's nonresidue, unchanged from EthLib. -/
def xi : Fp2 := ⟨1,1⟩

private theorem sub_fold (a b : Fp2) : Fp2.sub a b = a + -b := by
  apply ext2
  · change a.c0-b.c0 = a.c0 + -b.c0
    ring
  · change a.c1-b.c1 = a.c1 + -b.c1
    ring

private theorem xi_mul (a : Fp2) : a.mulByOnePlusI = xi*a := by
  apply ext2
  · change a.c0-a.c1 = 1*a.c0-1*a.c1
    ring
  · change a.c0+a.c1 = 1*a.c1+1*a.c0
    ring

@[simp] private theorem add_c0 (a b : Fp6) : (a+b).c0 = a.c0+b.c0 := rfl
@[simp] private theorem add_c1 (a b : Fp6) : (a+b).c1 = a.c1+b.c1 := rfl
@[simp] private theorem add_c2 (a b : Fp6) : (a+b).c2 = a.c2+b.c2 := rfl
@[simp] private theorem neg_c0 (a : Fp6) : (-a).c0 = -a.c0 := rfl
@[simp] private theorem neg_c1 (a : Fp6) : (-a).c1 = -a.c1 := rfl
@[simp] private theorem neg_c2 (a : Fp6) : (-a).c2 = -a.c2 := rfl
@[simp] private theorem zero_c0 : (0 : Fp6).c0 = 0 := rfl
@[simp] private theorem zero_c1 : (0 : Fp6).c1 = 0 := rfl
@[simp] private theorem zero_c2 : (0 : Fp6).c2 = 0 := rfl
@[simp] private theorem one_c0 : (1 : Fp6).c0 = 1 := rfl
@[simp] private theorem one_c1 : (1 : Fp6).c1 = 0 := rfl
@[simp] private theorem one_c2 : (1 : Fp6).c2 = 0 := rfl

@[simp] private theorem mul_c0 (a b : Fp6) :
    (a*b).c0 = a.c0*b.c0+xi*(a.c1*b.c2+a.c2*b.c1) := by
  change (Fp2.sub (Fp2.sub ((a.c1+a.c2)*(b.c1+b.c2)) (a.c1*b.c1))
    (a.c2*b.c2)).mulByOnePlusI+a.c0*b.c0 = _
  rw [xi_mul, sub_fold, sub_fold]
  ring

@[simp] private theorem mul_c1 (a b : Fp6) :
    (a*b).c1 = a.c0*b.c1+a.c1*b.c0+xi*(a.c2*b.c2) := by
  change Fp2.sub (Fp2.sub ((a.c0+a.c1)*(b.c0+b.c1)) (a.c0*b.c0))
    (a.c1*b.c1)+(a.c2*b.c2).mulByOnePlusI = _
  rw [xi_mul, sub_fold, sub_fold]
  ring

@[simp] private theorem mul_c2 (a b : Fp6) :
    (a*b).c2 = a.c0*b.c2+a.c1*b.c1+a.c2*b.c0 := by
  change Fp2.sub (Fp2.sub ((a.c0+a.c2)*(b.c0+b.c2)) (a.c0*b.c0))
    (a.c2*b.c2)+a.c1*b.c1 = _
  rw [sub_fold, sub_fold]
  ring

/-- Ring laws for EthLib's existing cubic coefficient formulas. -/
abbrev ringStructure : CommRing Fp6 := by
  apply CommRing.ofMinimalAxioms
  all_goals intros
  all_goals apply ext
  all_goals simp only [add_c0, add_c1, add_c2, mul_c0, mul_c1, mul_c2,
    neg_c0, neg_c1, neg_c2, zero_c0, zero_c1, zero_c2, one_c0, one_c1, one_c2]
  all_goals ring

attribute [local instance] ringStructure

/-- The coefficient embedding preserves the executable cubic ring operations. -/
def ofFp2Hom : Fp2 →+* Fp6 where
  toFun := Fp6.ofFp2
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := by
    apply ext
    all_goals simp [Fp6.ofFp2]
  map_mul' a b := by
    apply ext
    all_goals simp [Fp6.ofFp2]

@[simp] private theorem hom_c0 (a : Fp2) : (ofFp2Hom a).c0 = a := rfl
@[simp] private theorem hom_c1 (a : Fp2) : (ofFp2Hom a).c1 = 0 := rfl
@[simp] private theorem hom_c2 (a : Fp2) : (ofFp2Hom a).c2 = 0 := rfl

local instance : Fact Fp.modulus.Prime := ⟨BasePrime.modulus_prime⟩
local instance : CharP Fp2 Fp.modulus := QuadraticField.characteristic

/-- The cubic ring inherits the base field's characteristic through its coefficient embedding. -/
abbrev characteristic : CharP Fp6 Fp.modulus :=
  charP_of_injective_ringHom (f := ofFp2Hom)
    (fun _ _ h => congrArg Fp6.c0 h) Fp.modulus

attribute [local instance] characteristic

theorem v_cube : (Fp6.v : Fp6)^3 = ofFp2Hom xi := by
  apply ext
  all_goals norm_num [pow_succ, Fp6.v]

private theorem decomposition (a : Fp6) :
    a = ofFp2Hom a.c0 + ofFp2Hom a.c1*Fp6.v + ofFp2Hom a.c2*Fp6.v^2 := by
  apply ext
  all_goals norm_num [pow_succ, Fp6.v]

/-- A symbolic Frobenius formula, before replacing the nonresidue power with its table entry. -/
def frobenius (a : Fp6) : Fp6 :=
  let coefficient := Fp2.powNat xi ((Fp.modulus-1)/3)
  ⟨a.c0.conjugate, a.c1.conjugate*coefficient,
    a.c2.conjugate*(coefficient*coefficient)⟩

/-- The cubic modulus power follows from characteristic p and the relation v cubed equals xi. -/
theorem pow_modulus (a : Fp6) : a^Fp.modulus = frobenius a := by
  have hv : (Fp6.v : Fp6)^Fp.modulus =
      ofFp2Hom (Fp2.powNat xi ((Fp.modulus-1)/3))*Fp6.v := by
    have he : Fp.modulus = 3*((Fp.modulus-1)/3)+1 := by decide +kernel
    calc
      Fp6.v^Fp.modulus = Fp6.v^(3*((Fp.modulus-1)/3)+1) := by rw [←he]
      _ = _ := by
        rw [pow_add, pow_mul, v_cube, pow_one, ←map_pow, ←QuadraticField.powNat_eq_pow]
  have hc (x : Fp2) : (ofFp2Hom x)^Fp.modulus = ofFp2Hom x.conjugate := by
    rw [←map_pow, ←QuadraticField.powNat_eq_pow, QuadraticField.pow_modulus]
  calc
    a^Fp.modulus =
      (ofFp2Hom a.c0+ofFp2Hom a.c1*Fp6.v+ofFp2Hom a.c2*Fp6.v^2)^Fp.modulus := by
        rw [←decomposition a]
    _ = ofFp2Hom a.c0.conjugate +
        ofFp2Hom a.c1.conjugate*(ofFp2Hom (Fp2.powNat xi ((Fp.modulus-1)/3))*Fp6.v) +
        ofFp2Hom a.c2.conjugate*(ofFp2Hom (Fp2.powNat xi ((Fp.modulus-1)/3))*Fp6.v)^2 := by
      rw [add_pow_char, add_pow_char, mul_pow, mul_pow, hc, hc, hc, hv,
        ←pow_mul, Nat.mul_comm 2 Fp.modulus, pow_mul, hv]
    _ = frobenius a := by
      apply ext
      all_goals simp [frobenius, pow_succ, Fp6.v]

/-- The executable subtraction agrees with additive inverse in the cubic ring. -/
theorem sub_eq_add_neg (a b : Fp6) : Fp6.sub a b = a + -b := by
  apply ext
  all_goals change Fp2.sub _ _ = _ + -_
  all_goals exact sub_fold _ _

/-- EthLib's nonresidue rotation is multiplication by v in the cubic ring. -/
theorem mulByV_eq (a : Fp6) : a.mulByV = Fp6.v*a := by
  apply ext
  all_goals simp [Fp6.mulByV, Fp6.v, xi_mul]

/-- Multiplication by an embedded quadratic coefficient scales each cubic coefficient. -/
theorem mul_ofFp2 (a : Fp6) (b : Fp2) :
    a*ofFp2Hom b = ⟨a.c0*b,a.c1*b,a.c2*b⟩ := by
  apply ext
  all_goals simp

#print axioms mul_ofFp2
#print axioms v_cube
#print axioms sub_eq_add_neg
#print axioms mulByV_eq
#print axioms pow_modulus
#print axioms ringStructure
#print axioms ofFp2Hom
#print axioms characteristic
end CubicField

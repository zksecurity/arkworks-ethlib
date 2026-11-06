import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring
import EthLib.Cryptography.Bls.Fp12

open EthLib.Cryptography.Bls

namespace ExtensionAlignment

-- Restore field notation after coefficient reduction so ring sees the Fp operations.
private theorem add_fold (a b : Fp) : Fin.add a b = a+b := rfl
private theorem sub_fold (a b : Fp) : Fin.sub a b = a-b := rfl
private theorem mul_fold (a b : Fp) : Fin.mul a b = a*b := rfl

def cubicSquare (a : Fp6) : Fp6 :=
  let s0 := a.c0*a.c0
  let ab := a.c0*a.c1
  let s1 := ab+ab
  let s2 := (a.c0-a.c1+a.c2)*(a.c0-a.c1+a.c2)
  let bc := a.c1*a.c2
  let s3 := bc+bc
  let s4 := a.c2*a.c2
  ⟨s3.mulByOnePlusI+s0, s4.mulByOnePlusI+s1, s1+s2+s3-s0-s4⟩

/-- The source cubic-square schedule agrees coefficient by coefficient. -/
theorem cubic_square (a : Fp6) : cubicSquare a = a*a := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp2.instAdd, Fp2.instSub, Fp2.instMul, Fp6.instMul, cubicSquare,
    Fp6.mul, Fp2.add, Fp2.sub, Fp2.mul, Fp2.mulByOnePlusI]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold]
  all_goals ring

def cubicProduct (a b : Fp6) : Fp6 :=
  let ad := a.c0*b.c0
  let be := a.c1*b.c1
  let cf := a.c2*b.c2
  let x := (a.c1+a.c2)*(b.c1+b.c2)-be-cf
  let y := (a.c0+a.c1)*(b.c0+b.c1)-ad-be
  let z := (a.c0+a.c2)*(b.c0+b.c2)-ad+be-cf
  ⟨ad+x.mulByOnePlusI, y+cf.mulByOnePlusI, z⟩

theorem cubic_product (a b : Fp6) : cubicProduct a b = a*b := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp2.instAdd, Fp2.instSub, Fp2.instMul, Fp6.instMul,
    cubicProduct, Fp6.mul, Fp2.add, Fp2.sub, Fp2.mul, Fp2.mulByOnePlusI]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold]
  all_goals ring

private theorem fp2_mul_comm (a b : Fp2) : a*b = b*a := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  dsimp [HMul.hMul, Mul.mul, Fp2.instMul, Fp2.mul]
  congr 1
  all_goals simp only [mul_fold]
  all_goals ring

private theorem determinant_equation (a b c : Fp2) :
    a+(b+c).mulByOnePlusI = a+b.mulByOnePlusI+c.mulByOnePlusI := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  dsimp [HAdd.hAdd, Add.add, Fp2.instAdd, Fp2.add, Fp2.mulByOnePlusI]
  congr 1
  all_goals simp only [add_fold]
  all_goals ring

def cubicInverseCore (a : Fp6) : Fp6 :=
  let t0 := a.c0*a.c0
  let t1 := a.c1*a.c1
  let t2 := a.c2*a.c2
  let t3 := a.c0*a.c1
  let t4 := a.c0*a.c2
  let t5 := a.c1*a.c2
  let s0 := t0-t5.mulByOnePlusI
  let s1 := t2.mulByOnePlusI-t3
  let s2 := t1-t4
  let a1 := a.c2*s1
  let a2 := a.c1*s2
  let inv := (a.c0*s0+(a1+a2).mulByOnePlusI).inverse
  ⟨inv*s0, inv*s1, inv*s2⟩

theorem cubic_inverse_core (a : Fp6) : cubicInverseCore a = Fp6.inverse a := by
  dsimp only [cubicInverseCore, Fp6.inverse]
  rw [determinant_equation]
  congr 1 <;> exact fp2_mul_comm _ _

theorem cubic_inverse_zero : Fp6.inverse Fp6.zero = Fp6.zero := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hzero : Fp.zero = (0 : Fp) := rfl
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp2.instAdd, Fp2.instSub, Fp2.instMul, Fp6.inverse, Fp6.zero,
    Fp2.mulByOnePlusI, Fp2.mul, Fp2.add, Fp2.sub, Fp2.zero, Fp2.inverse]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold, hzero]
  all_goals ring

theorem cubic_is_zero (a : Fp6) : a.isZero = true ↔ a = Fp6.zero := by
  rcases a with ⟨⟨a0,a1⟩,⟨b0,b1⟩,⟨c0,c1⟩⟩
  simp [Fp6.isZero, Fp2.isZero, Fp.isZero, Fp6.zero, Fp2.zero, Fp.zero, and_assoc]

def quadraticProduct (a b : Fp12) : Fp12 :=
  let v0 := a.c0*b.c0
  let v1 := a.c1*b.c1
  let c1 := (a.c1+a.c0)*(b.c0+b.c1)-v0-v1
  ⟨v1.mulByV+v0,c1⟩

private theorem cubic_add_comm (a b : Fp6) : a+b = b+a := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  dsimp [HAdd.hAdd, Add.add, Fp6.instAdd, Fp6.add, Fp2.instAdd, Fp2.add]
  congr 2
  all_goals simp only [add_fold]
  all_goals ring

theorem quadratic_product (a b : Fp12) : quadraticProduct a b = a*b := by
  dsimp only [quadraticProduct, HMul.hMul, Mul.mul, Fp12.instMul, Fp12.mul]
  have hsum := cubic_add_comm a.c1 a.c0
  rw [hsum]
  congr 1
  exact cubic_add_comm _ _

private theorem quadratic_square_c0 (a b : Fp6) :
    (a*b).mulByV+(a-b)*(a-b.mulByV)+a*b = a*a+(b*b).mulByV := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp6.instAdd, Fp6.instSub, Fp6.instMul, Fp6.add, Fp6.sub, Fp6.mul, Fp6.mulByV,
    Fp2.instAdd, Fp2.instSub, Fp2.instMul, Fp2.add, Fp2.sub, Fp2.mul, Fp2.mulByOnePlusI]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold]
  all_goals ring

private theorem quadratic_square_c1 (a b : Fp6) :
    a*b+a*b = (a+b)*(a+b)-a*a-b*b := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp6.instAdd, Fp6.instSub, Fp6.instMul, Fp6.add, Fp6.sub, Fp6.mul,
    Fp2.instAdd, Fp2.instSub, Fp2.instMul, Fp2.add, Fp2.sub, Fp2.mul, Fp2.mulByOnePlusI]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold]
  all_goals ring

def quadraticSquare (a : Fp12) : Fp12 :=
  let v0 := a.c0-a.c1
  let v3 := a.c0-a.c1.mulByV
  let v2 := a.c0*a.c1
  let v0 := v0*v3
  ⟨v2.mulByV+v0+v2,v2+v2⟩

theorem quadratic_square (a : Fp12) : quadraticSquare a = a*a := by
  dsimp only [quadraticSquare, HMul.hMul, Mul.mul, Fp12.instMul, Fp12.mul]
  congr 1
  · exact quadratic_square_c0 _ _
  · exact quadratic_square_c1 _ _

private theorem cubic_zero_mul (a : Fp6) : Fp6.zero*a = Fp6.zero := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hzero : Fp.zero = (0 : Fp) := rfl
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp6.instMul, Fp6.mul, Fp6.zero, Fp2.instAdd, Fp2.instSub, Fp2.instMul,
    Fp2.add, Fp2.sub, Fp2.mul, Fp2.mulByOnePlusI, Fp2.zero]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold, hzero]
  all_goals ring

theorem quadratic_inverse_zero : Fp12.inverse Fp12.zero = Fp12.zero := by
  have hsub : Fp6.zero-Fp6.zero = Fp6.zero := rfl
  have hv : Fp6.zero.mulByV = Fp6.zero := rfl
  have hneg : -Fp6.zero = Fp6.zero := rfl
  dsimp only [Fp12.inverse, Fp12.zero]
  simp only [cubic_zero_mul, hv, hsub, cubic_inverse_zero, hneg]

theorem quadratic_is_zero (a : Fp12) :
    (a.c0.isZero && a.c1.isZero) = true ↔ a = Fp12.zero := by
  cases a
  simp [cubic_is_zero, Fp12.zero]

def cubicSparseOne (a : Fp6) (c1 : Fp2) : Fp6 :=
  let bb := a.c1*c1
  let t1 := (c1*(a.c1+a.c2)-bb).mulByOnePlusI
  let t2 := c1*(a.c0+a.c1)-bb
  ⟨t1,t2,bb⟩

theorem cubic_sparse_one (a : Fp6) (c1 : Fp2) :
    cubicSparseOne a c1 = a*⟨Fp2.zero,c1,Fp2.zero⟩ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hzero : Fp.zero = (0 : Fp) := rfl
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp6.instMul, Fp6.mul, cubicSparseOne, Fp2.instAdd, Fp2.instSub, Fp2.instMul,
    Fp2.add, Fp2.sub, Fp2.mul, Fp2.mulByOnePlusI, Fp2.zero]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold, hzero]
  all_goals ring

def cubicSparsePair (a : Fp6) (c0 c1 : Fp2) : Fp6 :=
  let aa := a.c0*c0
  let bb := a.c1*c1
  let t1 := (c1*(a.c1+a.c2)-bb).mulByOnePlusI+aa
  let t3 := c0*(a.c0+a.c2)-aa+bb
  let t2 := (c0+c1)*(a.c0+a.c1)-aa-bb
  ⟨t1,t2,t3⟩

theorem cubic_sparse_pair (a : Fp6) (c0 c1 : Fp2) :
    cubicSparsePair a c0 c1 = a*⟨c0,c1,Fp2.zero⟩ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hzero : Fp.zero = (0 : Fp) := rfl
  dsimp [HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    Fp6.instMul, Fp6.mul, cubicSparsePair, Fp2.instAdd, Fp2.instSub, Fp2.instMul,
    Fp2.add, Fp2.sub, Fp2.mul, Fp2.mulByOnePlusI, Fp2.zero]
  congr 2
  all_goals simp only [add_fold, sub_fold, mul_fold, hzero]
  all_goals ring

def sparseElement014 (c0 c1 c4 : Fp2) : Fp12 :=
  ⟨⟨c0,c1,Fp2.zero⟩,⟨Fp2.zero,c4,Fp2.zero⟩⟩

def quadraticSparse014 (a : Fp12) (c0 c1 c4 : Fp2) : Fp12 :=
  let aa := cubicSparsePair a.c0 c0 c1
  let bb := cubicSparseOne a.c1 c4
  let o := c1+c4
  let c1 := cubicSparsePair (a.c1+a.c0) c0 o-aa-bb
  ⟨bb.mulByV+aa,c1⟩

private theorem sparse_sum (c0 c1 c4 : Fp2) :
    (⟨c0,c1,Fp2.zero⟩ : Fp6)+⟨Fp2.zero,c4,Fp2.zero⟩ = ⟨c0,c1+c4,Fp2.zero⟩ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hzero : Fp.zero = (0 : Fp) := rfl
  dsimp [HAdd.hAdd, Add.add, Fp6.instAdd, Fp6.add, Fp2.instAdd, Fp2.add, Fp2.zero]
  congr 2
  all_goals simp only [add_fold, hzero]
  all_goals ring

theorem quadratic_sparse014 (a : Fp12) (c0 c1 c4 : Fp2) :
    quadraticSparse014 a c0 c1 c4 = a*sparseElement014 c0 c1 c4 := by
  rw [←quadratic_product]
  simp only [quadraticSparse014, cubic_sparse_pair, cubic_sparse_one,
    quadraticProduct, sparseElement014, sparse_sum]

#print axioms cubic_sparse_one
#print axioms cubic_sparse_pair
#print axioms quadratic_sparse014

#print axioms quadratic_product
#print axioms quadratic_square
#print axioms quadratic_inverse_zero
#print axioms quadratic_is_zero

#print axioms cubic_is_zero
#print axioms cubic_product
#print axioms cubic_inverse_core
#print axioms cubic_inverse_zero
#print axioms cubic_square
end ExtensionAlignment

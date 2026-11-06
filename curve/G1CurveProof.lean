import CurvePredicates
import G1AlignmentProof
import BaseFieldProof
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

open EthLib.Cryptography.Bls
open scoped WeierstrassCurve.Jacobian

namespace G1Curve
noncomputable section

local instance : Fact Fp.modulus.Prime := ⟨BasePrime.modulus_prime⟩
abbrev fieldStructure : Field Fp := inferInstanceAs (Field (ZMod Fp.modulus))
attribute [local instance] fieldStructure
local instance : CommRing Fp := fieldStructure.toCommRing

/-- BLS12-381's base-field curve, as an independent mathematical group. -/
def curve : WeierstrassCurve Fp := ⟨0,0,0,0,4⟩

private theorem discriminant_nonzero : curve.Δ ≠ 0 := by decide +kernel

abbrev ellipticStructure : curve.IsElliptic := ⟨isUnit_iff_ne_zero.mpr discriminant_nonzero⟩
attribute [local instance] ellipticStructure

def coords (p : G1) : Fin 3 → Fp := ![p.x,p.y,p.z]

/-- Infinity accepts every stored X/Y representation, as in EthLib and Rust. -/
def OnCurve (p : G1) : Prop := p.z = 0 ∨ curve.toJacobian.Equation (coords p)

/-- Singular inputs map to zero in Mathlib; our group-law theorems require OnCurve. -/
def interpret (p : G1) : curve.toAffine.Point :=
  WeierstrassCurve.Jacobian.Point.toAffine curve (coords p)

@[simp] theorem isZero_iff (x : Fp) : Fp.isZero x = true ↔ x = 0 := by
  constructor
  · intro h
    apply Fin.ext
    change x.val = 0
    simpa only [Fp.isZero, beq_iff_eq] using h
  · rintro rfl
    decide +kernel

@[simp] private theorem beq_iff (x y : Fp) : Fp.beq x y = true ↔ x = y := by
  simp [Fp.beq, Fin.ext_iff]

theorem equation_iff (p : G1) :
    curve.toJacobian.Equation (coords p) ↔ p.y^2 = p.x^3 + (4 : Fp)*p.z^6 := by
  rw [WeierstrassCurve.Jacobian.equation_iff]
  simp [curve, coords, sub_eq_zero]

theorem nonsingular_finite (p : G1) (hp : OnCurve p) (hz : p.z ≠ 0) :
    curve.toJacobian.Nonsingular (coords p) := by
  have he := hp.resolve_left hz
  have hzc : coords p 2 ≠ 0 := hz
  rw [WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero hzc,
    ← WeierstrassCurve.Affine.equation_iff_nonsingular]
  exact (WeierstrassCurve.Jacobian.equation_of_Z_ne_zero hzc).mp he

theorem interpret_infinity (p : G1) (hz : p.z = 0) : interpret p = 0 :=
  WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero hz

theorem interpret_nonzero (p : G1) (hp : OnCurve p) (hz : p.z ≠ 0) : interpret p ≠ 0 := by
  rw [interpret, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero (nonsingular_finite p hp hz) hz]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem interpret_zero : interpret G1.zero = 0 := interpret_infinity _ rfl

theorem neg_coords (p : G1) : coords (G1.neg p) = curve.toJacobian.neg (coords p) := by
  simp [coords, G1.neg, WeierstrassCurve.Jacobian.neg,
    WeierstrassCurve.Jacobian.negY, curve]

theorem neg_onCurve (p : G1) (hp : OnCurve p) : OnCurve (G1.neg p) := by
  by_cases hz : p.z = 0
  · exact Or.inl hz
  · apply Or.inr
    rw [neg_coords]
    exact (WeierstrassCurve.Jacobian.nonsingular_neg (nonsingular_finite p hp hz)).left

theorem interpret_neg (p : G1) (hp : OnCurve p) : interpret (G1.neg p) = -interpret p := by
  by_cases hz : p.z = 0
  · rw [interpret_infinity (G1.neg p) hz, interpret_infinity p hz, neg_zero]
  · unfold interpret
    rw [neg_coords]
    exact WeierstrassCurve.Jacobian.Point.toAffine_neg (nonsingular_finite p hp hz)

theorem double_coords (p : G1) (hz : p.z ≠ 0) :
    coords (G1.double p) = curve.toJacobian.dblXYZ (coords p) := by
  have hi : p.z.isZero = false := by cases h : p.z.isZero <;> simp_all
  funext i
  fin_cases i
  all_goals simp [G1.double, hi, coords, curve,
    WeierstrassCurve.Jacobian.dblXYZ, WeierstrassCurve.Jacobian.dblX,
    WeierstrassCurve.Jacobian.dblY, WeierstrassCurve.Jacobian.negDblY,
    WeierstrassCurve.Jacobian.dblZ, WeierstrassCurve.Jacobian.dblU_eq,
    WeierstrassCurve.Jacobian.negY]
  all_goals ring

theorem double_onCurve (p : G1) (hp : OnCurve p) : OnCurve (G1.double p) := by
  by_cases hz : p.z = 0
  · have hi : p.z.isZero = true := (isZero_iff p.z).mpr hz
    simpa only [G1.double, hi, ite_eq_left] using hp
  · apply Or.inr
    rw [double_coords p hz]
    have hn := nonsingular_finite p hp hz
    have hd := WeierstrassCurve.Jacobian.nonsingular_add hn hn
    rw [WeierstrassCurve.Jacobian.add_self] at hd
    exact hd.left

theorem interpret_double (p : G1) (hp : OnCurve p) :
    interpret (G1.double p) = interpret p + interpret p := by
  by_cases hz : p.z = 0
  · have hi : p.z.isZero = true := (isZero_iff p.z).mpr hz
    simp only [G1.double, hi, ite_eq_left, interpret_infinity p hz, add_zero]
  · unfold interpret
    rw [double_coords p hz, ← WeierstrassCurve.Jacobian.add_self]
    exact WeierstrassCurve.Jacobian.Point.toAffine_add (nonsingular_finite p hp hz)
      (nonsingular_finite p hp hz)

def XEq (p q : G1) : Prop := p.x*q.z^2 = q.x*p.z^2

def YEq (p q : G1) : Prop := p.y*q.z^3 = q.y*p.z^3

private theorem x_flag (p q : G1) :
    Fp.beq (p.x*(q.z*q.z)) (q.x*(p.z*p.z)) = true ↔ XEq p q := by
  simp [XEq, pow_two]

private theorem y_flag (p q : G1) :
    Fp.beq (p.y*q.z*(q.z*q.z)) (q.y*p.z*(p.z*p.z)) = true ↔ YEq p q := by
  have h1 : p.y*q.z*(q.z*q.z) = p.y*q.z^3 := by ring
  have h2 : q.y*p.z*(p.z*p.z) = q.y*p.z^3 := by ring
  rw [h1, h2, beq_iff]
  rfl

private def sourceAdd {R : Type*} [CommRing R] (x y z X Y Z : R) : Fin 3 → R :=
  let u1 := x*(Z*Z)
  let u2 := X*(z*z)
  let s1 := y*Z*(Z*Z)
  let s2 := Y*z*(z*z)
  let h := u2-u1
  let h2 := h+h
  let i := h2*h2
  let j := h*i
  let r := (s2-s1)+(s2-s1)
  let v := u1*i
  let outX := r*r-j-(v+v)
  let outY := r*(v-outX)-(s1+s1)*j
  let outZ := ((z+Z)*(z+Z)-z*z-Z*Z)*h
  ![outX,outY,outZ]

/-- The change of Jacobian representative between the two addition formulas. -/
def addScale {R : Type*} [CommRing R] (z Z : R) : R := -(z*Z+z*Z)

private theorem sourceAdd_scale {R : Type*} [CommRing R] (x y z X Y Z U V : R)
    (hx : U*(z*Z)^2 = (y*Z^3-Y*z^3)^2-x*Z^2*(x*Z^2-X*z^2)^2-X*z^2*(x*Z^2-X*z^2)^2)
    (hy : V*(z*Z)^3 = (y*Z^3-Y*z^3)*(U*(z*Z)^2-x*Z^2*(x*Z^2-X*z^2)^2)+
      y*Z^3*(x*Z^2-X*z^2)^3) :
    sourceAdd x y z X Y Z = addScale z Z • ![U,-V,x*Z^2-X*z^2] := by
  funext i
  fin_cases i
  all_goals simp [sourceAdd, addScale, WeierstrassCurve.Jacobian.smul_fin3]
  · linear_combination -4*hx
  · linear_combination -8*hy-8*(y*Z^3-Y*z^3)*hx
  · ring

theorem general_coords (p q : G1)
    (hp : curve.toJacobian.Equation (coords p)) (hq : curve.toJacobian.Equation (coords q))
    (hx : ¬XEq p q) :
    coords (G1.addGeneral p q) = addScale p.z q.z • curve.toJacobian.addXYZ (coords p) (coords q) := by
  have hflag : Fp.beq (p.x*(q.z*q.z)) (q.x*(p.z*p.z)) = false := by
    cases h : Fp.beq (p.x*(q.z*q.z)) (q.x*(p.z*p.z)) with
    | false => rfl
    | true => exact False.elim (hx ((x_flag p q).mp h))
  have raw : coords (G1.addGeneral p q) = sourceAdd p.x p.y p.z q.x q.y q.z := by
    simp only [G1.addGeneral, hflag, Bool.false_eq_true, ↓reduceIte, coords, sourceAdd]
  have heX := WeierstrassCurve.Jacobian.addX_eq' hp hq
  have heY := WeierstrassCurve.Jacobian.negAddY_eq' (W' := curve.toJacobian) (coords p) (coords q)
  simp only [coords, curve, WeierstrassCurve.Jacobian.addZ, zero_mul,
    add_zero, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at heX heY
  rw [raw]
  have h := sourceAdd_scale p.x p.y p.z q.x q.y q.z
    (curve.toJacobian.addX (coords p) (coords q))
    (curve.toJacobian.negAddY (coords p) (coords q)) heX heY
  simpa only [WeierstrassCurve.Jacobian.addXYZ, WeierstrassCurve.Jacobian.addY,
    WeierstrassCurve.Jacobian.negY, WeierstrassCurve.Jacobian.addZ, WeierstrassCurve.toJacobian, curve, coords,
    zero_mul, mul_zero, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

private theorem scale_unit_aux {K : Type*} [Field K] (z Z : K)
    (hz : z ≠ 0) (hZ : Z ≠ 0) (h2 : (1 : K)+1 ≠ 0) : IsUnit (addScale z Z) := by
  apply isUnit_iff_ne_zero.mpr
  unfold addScale
  apply neg_ne_zero.mpr
  have h := mul_ne_zero h2 (mul_ne_zero hz hZ)
  simpa only [add_mul, one_mul] using h

private theorem scale_unit (p q : G1) (hp : p.z ≠ 0) (hq : q.z ≠ 0) :
    IsUnit (addScale p.z q.z) :=
  scale_unit_aux p.z q.z hp hq (by decide +kernel)

theorem interpret_eq_of_XY (p q : G1) (hp : p.z ≠ 0) (hq : q.z ≠ 0)
    (hx : XEq p q) (hy : YEq p q) : interpret p = interpret q := by
  have he : coords p ≈ coords q :=
    WeierstrassCurve.Jacobian.equiv_of_X_eq_of_Y_eq hp hq hx hy
  exact WeierstrassCurve.Jacobian.Point.toAffine_of_equiv he

private theorem general_double (p q : G1) (hx : XEq p q) (hy : YEq p q) :
    G1.addGeneral p q = G1.double p := by
  unfold G1.addGeneral
  simp only [(x_flag p q).mpr hx, (y_flag p q).mpr hy, ↓reduceIte]

private theorem general_zero (p q : G1) (hx : XEq p q) (hy : ¬YEq p q) :
    G1.addGeneral p q = G1.zero := by
  have hf : Fp.beq (p.y*q.z*(q.z*q.z)) (q.y*p.z*(p.z*p.z)) = false := by
    cases h : Fp.beq (p.y*q.z*(q.z*q.z)) (q.y*p.z*(p.z*p.z)) with
    | false => rfl
    | true => exact False.elim (hy ((y_flag p q).mp h))
  unfold G1.addGeneral
  simp only [(x_flag p q).mpr hx, hf, Bool.false_eq_true, ↓reduceIte]

theorem general_correct (p q : G1) (hp : OnCurve p) (hq : OnCurve q)
    (hpz : p.z ≠ 0) (hqz : q.z ≠ 0) :
    OnCurve (G1.addGeneral p q) ∧
      interpret (G1.addGeneral p q) = interpret p + interpret q := by
  have hnP := nonsingular_finite p hp hpz
  have hnQ := nonsingular_finite q hq hqz
  by_cases hx : XEq p q
  · by_cases hy : YEq p q
    · rw [general_double p q hx hy]
      refine ⟨double_onCurve p hp, ?_⟩
      rw [interpret_double p hp, interpret_eq_of_XY p q hpz hqz hx hy]
    · rw [general_zero p q hx hy]
      refine ⟨Or.inl rfl, ?_⟩
      have hne : ¬coords p ≈ coords q := by
        intro h
        exact hy (WeierstrassCurve.Jacobian.Y_eq_of_equiv h)
      have hs := WeierstrassCurve.Jacobian.Point.toAffine_add hnP hnQ
      rw [WeierstrassCurve.Jacobian.add_of_not_equiv hne] at hs
      have hz : curve.toJacobian.addXYZ (coords p) (coords q) 2 = 0 := by
        change p.x*q.z^2-q.x*p.z^2 = 0
        exact sub_eq_zero.mpr hx
      rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero hz] at hs
      exact interpret_zero.trans hs
  · have hne : ¬coords p ≈ coords q := WeierstrassCurve.Jacobian.not_equiv_of_X_ne hx
    have he := general_coords p q (hp.resolve_left hpz) (hq.resolve_left hqz) hx
    have hn := WeierstrassCurve.Jacobian.nonsingular_add hnP hnQ
    rw [WeierstrassCurve.Jacobian.add_of_not_equiv hne] at hn
    have hscaled := (WeierstrassCurve.Jacobian.nonsingular_smul _ (scale_unit p q hpz hqz)).mpr hn
    refine ⟨Or.inr ?_, ?_⟩
    · rw [he]
      exact hscaled.left
    · unfold interpret
      rw [he, WeierstrassCurve.Jacobian.Point.toAffine_smul _ (scale_unit p q hpz hqz),
        ← WeierstrassCurve.Jacobian.add_of_not_equiv hne]
      exact WeierstrassCurve.Jacobian.Point.toAffine_add hnP hnQ

theorem add_cases (p q : G1) : G1.add p q =
    if p.z = 0 then q else if q.z = 0 then p else G1.addGeneral p q := by
  rw [G1Alignment.add_projective]
  simp only [isZero_iff]

theorem add_onCurve (p q : G1) (hp : OnCurve p) (hq : OnCurve q) : OnCurve (G1.add p q) := by
  rw [add_cases]
  split_ifs with hpz hqz
  · exact hq
  · exact hp
  · exact (general_correct p q hp hq hpz hqz).1

theorem interpret_add (p q : G1) (hp : OnCurve p) (hq : OnCurve q) :
    interpret (G1.add p q) = interpret p + interpret q := by
  rw [add_cases]
  split_ifs with hpz hqz
  · rw [interpret_infinity p hpz, zero_add]
  · rw [interpret_infinity q hqz, add_zero]
  · exact (general_correct p q hp hq hpz hqz).2

private theorem repeated_equation {R : Type*} [CommRing R] (x y z c : R) :
    y*y = x*x*x+c*((z*z)*(z*z)*(z*z)) ↔ y^2 = x^3+c*z^6 := by
  constructor <;> intro h <;> linear_combination h

theorem onCurve_iff (p : G1) : ConcreteEncoding.onCurve p = true ↔ OnCurve p := by
  by_cases hz : p.z = 0
  · simp [ConcreteEncoding.onCurve, G1.isInfinity, OnCurve, hz]
  · have hi : p.z.isZero = false := by cases h : p.z.isZero <;> simp_all
    simp only [ConcreteEncoding.onCurve, G1.isInfinity, hi, Bool.false_eq_true, ↓reduceIte,
      beq_iff, OnCurve, hz, false_or, equation_iff]
    have hc : Fp.ofNat 4 = (4 : Fp) := by decide +kernel
    simpa only [hc] using repeated_equation p.x p.y p.z (Fp.ofNat 4)

theorem interpret_eq_zero_iff (p : G1) (hp : OnCurve p) : interpret p = 0 ↔ p.z = 0 := by
  constructor
  · intro h
    by_contra hz
    exact interpret_nonzero p hp hz h
  · exact interpret_infinity p

theorem mulNat_correct (p : G1) (n : Nat) (hp : OnCurve p) :
    OnCurve (G1.mulNat p n) ∧ interpret (G1.mulNat p n) = n • interpret p := by
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    rw [G1.mulNat.eq_1]
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, interpret_zero, zero_smul, and_true]
      exact Or.inl rfl
    · have hd := double_onCurve p hp
      have hh := ih (n/2) (Nat.div_lt_self (by omega) (by decide)) (G1.double p) hd
      simp only [hn, ↓reduceIte]
      by_cases hodd : n % 2 = 1
      · rw [ite_eq_left hodd]
        refine ⟨add_onCurve p _ hp hh.1, ?_⟩
        rw [interpret_add p _ hp hh.1, hh.2, interpret_double p hp,
          smul_add, ← add_nsmul]
        have he : 1+(n/2+n/2) = n := by omega
        calc
          _ = (1+(n/2+n/2)) • interpret p := by simp only [add_nsmul, one_smul]
          _ = n • interpret p := by rw [he]
      · rw [ite_eq_right hodd]
        refine ⟨hh.1, ?_⟩
        rw [hh.2, interpret_double p hp, smul_add, ← add_nsmul]
        have he : n/2+n/2 = n := by omega
        rw [he]

theorem inSubgroup_iff (p : G1) (hp : OnCurve p) :
    G1.inSubgroup p = true ↔ Fr.modulus • interpret p = 0 := by
  by_cases hz : p.z = 0
  · have hi : p.z.isZero = true := (isZero_iff p.z).mpr hz
    simp only [G1.inSubgroup, G1.isInfinity, hi, ↓reduceIte, interpret_infinity p hz, smul_zero]
  · have hi : p.z.isZero = false := by cases h : p.z.isZero <;> simp_all
    simp only [G1.inSubgroup, G1.isInfinity, hi, Bool.false_eq_true, ↓reduceIte, isZero_iff]
    have hm := mulNat_correct p Fr.modulus hp
    simpa only [hm.2] using (interpret_eq_zero_iff (G1.mulNat p Fr.modulus) hm.1).symm

#print axioms inSubgroup_iff
#print axioms onCurve_iff
#print axioms interpret_eq_zero_iff
#print axioms mulNat_correct
#print axioms general_coords
#print axioms interpret_eq_of_XY
#print axioms general_correct
#print axioms add_cases
#print axioms add_onCurve
#print axioms interpret_add
#print axioms isZero_iff
#print axioms double_coords
#print axioms double_onCurve
#print axioms interpret_double
#print axioms equation_iff
#print axioms nonsingular_finite
#print axioms interpret_infinity
#print axioms interpret_nonzero
#print axioms interpret_zero
#print axioms neg_coords
#print axioms neg_onCurve
#print axioms interpret_neg

end
end G1Curve

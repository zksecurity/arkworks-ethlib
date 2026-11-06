import PreparedLineGeometryProof

open EthLib.Cryptography.Bls
open PreparedLineGeometry

namespace PreparedMillerStep

noncomputable section
local instance : Field Fp2 := QuadraticDomain.fieldStructure
local instance : Field Fp6 := CubicDomain.fieldStructure
local instance : Field Fp12 := DodecicDomain.fieldStructure

private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem source_sub12 (a b : Fp12) : Fp12.sub a b = a + -b := by
  apply ext12
  · change Fp6.sub a.c0 b.c0 = a.c0 + -b.c0
    exact CubicField.sub_eq_add_neg _ _
  · change Fp6.sub a.c1 b.c1 = a.c1 + -b.c1
    exact CubicField.sub_eq_add_neg _ _

private theorem extPoint (a b : Embedded.Point) (hx : a.x = b.x) (hy : a.y = b.y)
    (hi : a.inf = b.inf) : a = b := by
  cases a; cases b; cases hx; cases hy; cases hi; rfl

private theorem scaled_double_x {K : Type*} [Field K] (x m w : K) :
    (m*w⁻¹)*(m*w⁻¹) + -(x*(w^2)⁻¹) + -(x*(w^2)⁻¹) =
      (m^2 + -(2*x))*(w^2)⁻¹ := by
  simp only [←inv_pow]
  ring

private theorem scaled_y {K : Type*} [Field K] (x y nx m w : K) :
    (m*w⁻¹)*(x*(w^2)⁻¹ + -(nx*(w^2)⁻¹)) + -(y*(w^3)⁻¹) =
      (m*(x + -nx) + -y)*(w^3)⁻¹ := by
  simp only [←inv_pow]
  ring

/-- The finite EthLib Miller double updates to the untwist of the source homogeneous double. -/
theorem double_state (p : PreparedLine.Hom) (q : Embedded.Point) (f : Fp12)
    (hp : PreparedGeometry.OnCurve p) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    (millerDouble (untwist p) q f).1 =
      untwist (PreparedLine.double p (Fp.inverse (Fp.ofNat 2))).1 := by
  apply extPoint
  · simp only [millerDouble, show (untwist p).inf = false from rfl, Bool.false_eq_true,
      ite_false, HSub.hSub, Sub.sub, source_sub12]
    rw [double_slope_affine]
    simp only [untwist, wInv2_eq, wInv3_eq]
    rw [scaled_double_x]
    rw [PreparedGeometry.double_affine_x p hp hy hz]
    simp only [map_add, map_neg, map_mul, map_pow, map_ofNat]
  · simp only [millerDouble, show (untwist p).inf = false from rfl, Bool.false_eq_true,
      ite_false, HSub.hSub, Sub.sub, source_sub12]
    rw [double_slope_affine]
    simp only [untwist, wInv2_eq, wInv3_eq]
    rw [scaled_double_x, scaled_y]
    rw [PreparedGeometry.double_affine_y p hp hy hz,
      PreparedGeometry.double_affine_x p hp hy hz]
    simp only [map_add, map_neg, map_mul, map_pow, map_inv₀, map_ofNat]
  · rfl

private theorem scaled_add_x {K : Type*} [Field K] (x qx m w : K) :
    (m*w⁻¹)*(m*w⁻¹) + -(x*(w^2)⁻¹) + -(qx*(w^2)⁻¹) =
      (m^2 + -x + -qx)*(w^2)⁻¹ := by
  simp only [←inv_pow]
  ring

/-- The finite EthLib Miller add updates to the untwist of the source mixed add. -/
theorem add_state (p : PreparedLine.Hom) (qx qy : Fp2) (q : Embedded.Point) (f : Fp12)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    (millerAdd (untwist p) (untwist ⟨qx,qy,1⟩) q f).1 =
      untwist (PreparedLine.add p qx qy).1 := by
  apply extPoint
  · simp only [millerAdd, show (untwist p).inf = false from rfl,
      show (untwist ⟨qx,qy,1⟩).inf = false from rfl, Bool.false_eq_true,
      ite_false, HSub.hSub, Sub.sub, source_sub12]
    rw [add_slope_eq p qx qy hz hx]
    simp only [untwist, wInv2_eq, wInv3_eq, inv_one, mul_one]
    rw [scaled_add_x, PreparedGeometry.add_affine_x p qx qy hz hx]
    simp only [map_add, map_neg, map_mul, map_pow]
  · simp only [millerAdd, show (untwist p).inf = false from rfl,
      show (untwist ⟨qx,qy,1⟩).inf = false from rfl, Bool.false_eq_true,
      ite_false, HSub.hSub, Sub.sub, source_sub12]
    rw [add_slope_eq p qx qy hz hx]
    simp only [untwist, wInv2_eq, wInv3_eq, inv_one, mul_one]
    rw [scaled_add_x, scaled_y, PreparedGeometry.add_affine_y p qx qy hz hx,
      PreparedGeometry.add_affine_x p qx qy hz hx]
    simp only [map_add, map_neg, map_mul, map_pow, map_inv₀]
  · rfl

/-- The finite G1 evaluation point, embedded with the unchanged tower inclusion. -/
def evaluationPoint (px py : Fp) : Embedded.Point :=
  { x := embed (Fp2.ofFp px), y := embed (Fp2.ofFp py) }

/-- A double-step accumulator has the same final value under either line implementation. -/
theorem double_value (p : PreparedLine.Hom) (half : Fp) (px py : Fp) (f : Fp12)
    (hp : PreparedGeometry.OnCurve p) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    finalExponentiation (millerDouble (untwist p) (evaluationPoint px py) f).2 =
      finalExponentiation (f*f*PreparedMiller.lineValue (PreparedLine.double p half).2 px py) := by
  simp only [millerDouble, show (untwist p).inf = false from rfl, Bool.false_eq_true, ite_false]
  simp only [FinalScaling.final_mul]
  rw [double_line_ethlib p half px py hp hy hz]
  rfl

/-- A mixed-add accumulator has the same final value under either line implementation. -/
theorem add_value (p : PreparedLine.Hom) (qx qy : Fp2) (px py : Fp) (f : Fp12)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    finalExponentiation (millerAdd (untwist p) (untwist ⟨qx,qy,1⟩) (evaluationPoint px py) f).2 =
      finalExponentiation (f*PreparedMiller.lineValue (PreparedLine.add p qx qy).2 px py) := by
  simp only [millerAdd, show (untwist p).inf = false from rfl,
    show (untwist ⟨qx,qy,1⟩).inf = false from rfl, Bool.false_eq_true, ite_false]
  rw [FinalScaling.final_mul, FinalScaling.final_mul, add_line_ethlib p qx qy px py hz hx]
  rfl

#print axioms add_state
#print axioms double_value
#print axioms add_value
#print axioms double_state
end
end PreparedMillerStep

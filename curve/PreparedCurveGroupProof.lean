import PreparedReferenceWalkProof
import PreparedPrefixProof
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open EthLib.Cryptography.Bls

namespace PreparedCurve
noncomputable section
local instance : Field Fp2 := QuadraticDomain.fieldStructure
local instance : DecidableEq Fp2 := Classical.decEq _

/-- The BLS12-381 quadratic twist used by the source prepared formulas. -/
def curve : WeierstrassCurve Fp2 := ⟨0,0,0,0,PreparedLine.coeffB⟩

private theorem discriminant_nonzero : curve.Δ ≠ 0 := by
  intro h
  have hc := congrArg Fp2.c1 h
  have hn : curve.Δ.c1 ≠ (0 : Fp2).c1 := by decide +kernel
  exact hn hc

/-- The twist is nonsingular over the proved quadratic field. -/
abbrev ellipticStructure : curve.IsElliptic := ⟨isUnit_iff_ne_zero.mpr discriminant_nonzero⟩
attribute [local instance] ellipticStructure

theorem equation_iff (x y : Fp2) : curve.toAffine.Equation x y ↔ y^2 = x^3 + PreparedLine.coeffB := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve, zero_mul, add_zero]

private theorem normalized_equation {K : Type*} [Field K] (x y z b : K)
    (hz : z ≠ 0) (h : y^2*z = x^3 + b*z^3) : (y*z⁻¹)^2 = (x*z⁻¹)^3+b := by
  field_simp
  linear_combination h

private theorem homogeneous_equation {K : Type*} [Field K] (x y z b : K)
    (hz : z ≠ 0) (h : (y*z⁻¹)^2 = (x*z⁻¹)^3+b) : y^2*z = x^3+b*z^3 := by
  field_simp at h
  linear_combination h

theorem onCurve_iff (p : PreparedLine.Hom) (hz : p.z ≠ 0) :
    PreparedGeometry.OnCurve p ↔ curve.toAffine.Equation (p.x*p.z⁻¹) (p.y*p.z⁻¹) := by
  rw [equation_iff]
  exact ⟨normalized_equation _ _ _ _ hz, homogeneous_equation _ _ _ _ hz⟩

/-- Interpret a finite source homogeneous point as a mathematical curve point. -/
def point (p : PreparedLine.Hom) (h : PreparedGeometry.OnCurve p) (hz : p.z ≠ 0) :
    curve.toAffine.Point := WeierstrassCurve.Affine.Point.mk ((onCurve_iff p hz).mp h)

theorem point_nonzero (p : PreparedLine.Hom) (h : PreparedGeometry.OnCurve p) (hz : p.z ≠ 0) :
    point p h hz ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

theorem y_nonzero (p : PreparedLine.Hom) (h : PreparedGeometry.OnCurve p) (hz : p.z ≠ 0)
    (hn : point p h hz + point p h hz ≠ 0) : p.y ≠ 0 := by
  intro hy
  have he : p.y*p.z⁻¹ = curve.toAffine.negY (p.x*p.z⁻¹) (p.y*p.z⁻¹) := by
    simp only [WeierstrassCurve.Affine.negY, curve, hy, zero_mul, neg_zero, sub_zero]
  exact hn (WeierstrassCurve.Affine.Point.add_self_of_Y_eq he)

private theorem two_nonzero : (2 : Fp2) ≠ 0 := by
  intro h
  have hc := congrArg Fp2.c0 h
  have hn : (2 : Fp) ≠ 0 := by decide +kernel
  exact hn hc

private theorem y_ne_neg (x y : Fp2) (hy : y ≠ 0) : y ≠ curve.toAffine.negY x y := by
  intro h
  simp only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero] at h
  apply mul_ne_zero two_nonzero hy
  linear_combination h

private theorem tangent_slope (x y : Fp2) (hy : y ≠ 0) :
    curve.toAffine.slope x x y y = 3*x^2*(2*y)⁻¹ := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (y_ne_neg x y hy)]
  simp only [curve, zero_mul, mul_zero, add_zero, sub_zero,
    WeierstrassCurve.Affine.negY, sub_neg_eq_add, ←two_mul, div_eq_mul_inv]

theorem point_double (p : PreparedLine.Hom) (hp : PreparedGeometry.OnCurve p)
    (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    point (PreparedLine.double p (Fp.inverse (Fp.ofNat 2))).1
      (PreparedGeometry.double_onCurve p _ hp PreparedGeometry.source_half)
      (PreparedGeometry.double_z_nonzero p _ hy hz) = point p hp hz + point p hp hz := by
  have hyn : p.y*p.z⁻¹ ≠ 0 := mul_ne_zero hy (inv_ne_zero hz)
  simp only [point, WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (y_ne_neg _ _ hyn)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [PreparedGeometry.double_affine_x p hp hy hz]
    simp only [WeierstrassCurve.Affine.addX]
    simp only [tangent_slope _ _ hyn]
    simp only [curve, zero_mul, add_zero, sub_eq_add_neg]
    ring
  · rw [PreparedGeometry.double_affine_y p hp hy hz, PreparedGeometry.double_affine_x p hp hy hz]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]
    simp only [tangent_slope _ _ hyn]
    simp only [curve, zero_mul, add_zero, sub_eq_add_neg]
    ring

private theorem chord_slope (p : PreparedLine.Hom) (qx qy : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    curve.toAffine.slope (p.x*p.z⁻¹) qx (p.y*p.z⁻¹) qy =
      (p.y + -(qy*p.z))*(p.x + -(qx*p.z))⁻¹ := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (PreparedGeometry.affine_x_ne p qx hz hx)]
  rw [PreparedGeometry.add_slope p qx qy hz hx]
  simp only [div_eq_mul_inv, sub_eq_add_neg]
  have hn : p.y*p.z⁻¹ + -qy = -(qy + -(p.y*p.z⁻¹)) := by ring
  have hd : p.x*p.z⁻¹ + -qx = -(qx + -(p.x*p.z⁻¹)) := by ring
  rw [hn, hd, inv_neg, neg_mul_neg]

theorem add_coordinates (p : PreparedLine.Hom) (qx qy : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    let a := (PreparedLine.add p qx qy).1
    let m := curve.toAffine.slope (p.x*p.z⁻¹) qx (p.y*p.z⁻¹) qy
    a.x*a.z⁻¹ = curve.toAffine.addX (p.x*p.z⁻¹) qx m ∧
      a.y*a.z⁻¹ = curve.toAffine.addY (p.x*p.z⁻¹) qx (p.y*p.z⁻¹) m := by
  dsimp only
  constructor
  · rw [PreparedGeometry.add_affine_x p qx qy hz hx]
    simp only [WeierstrassCurve.Affine.addX]
    rw [chord_slope p qx qy hz hx]
    simp only [curve, zero_mul, add_zero, sub_eq_add_neg]
    ring
  · rw [PreparedGeometry.add_affine_y p qx qy hz hx,
      PreparedGeometry.add_affine_x p qx qy hz hx]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]
    rw [chord_slope p qx qy hz hx]
    simp only [curve, zero_mul, add_zero, sub_eq_add_neg]
    ring

/-- The finite affine anchor for the source mixed-add schedule. -/
def affinePoint (qx qy : Fp2) (hq : curve.toAffine.Equation qx qy) : curve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk hq

/-- Source mixed addition preserves the twist equation when its x coordinates differ. -/
theorem add_onCurve (p : PreparedLine.Hom) (qx qy : Fp2)
    (hp : PreparedGeometry.OnCurve p) (hq : curve.toAffine.Equation qx qy)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    PreparedGeometry.OnCurve (PreparedLine.add p qx qy).1 := by
  have hp' := WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((onCurve_iff p hz).mp hp)
  have hq' := WeierstrassCurve.Affine.equation_iff_nonsingular.mp hq
  have hn := WeierstrassCurve.Affine.nonsingular_add hp' hq'
    (fun h => PreparedGeometry.affine_x_ne p qx hz hx h.1)
  have he := add_coordinates p qx qy hz hx
  apply (onCurve_iff _ (PreparedGeometry.add_z_nonzero p qx qy hz hx)).mpr
  simpa only [he.1, he.2] using hn.1

/-- The source mixed-add state is addition in Mathlib's curve group. -/
theorem point_add (p : PreparedLine.Hom) (qx qy : Fp2)
    (hp : PreparedGeometry.OnCurve p) (hq : curve.toAffine.Equation qx qy)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    point (PreparedLine.add p qx qy).1 (add_onCurve p qx qy hp hq hz hx)
      (PreparedGeometry.add_z_nonzero p qx qy hz hx) = point p hp hz + affinePoint qx qy hq := by
  simp only [point, affinePoint, WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (PreparedGeometry.affine_x_ne p qx hz hx)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact add_coordinates p qx qy hz hx

#print axioms ellipticStructure
#print axioms equation_iff
#print axioms onCurve_iff
#print axioms point_nonzero
#print axioms y_nonzero
#print axioms point_double
#print axioms add_coordinates
#print axioms add_onCurve
#print axioms point_add
end
end PreparedCurve

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

open WeierstrassCurve

namespace CubicEndomorphism
noncomputable section
variable {K : Type*} [Field K]

def curve (c : K) : WeierstrassCurve K := ⟨0, 0, 0, 0, c⟩

private theorem equation_iff (c x y : K) :
    (curve c).toAffine.Equation x y ↔ y^2 = x^3+c := by
  simp [Affine.equation_iff, curve]

theorem nonsingular_map (c b x y : K) [(curve c).IsElliptic] (hb : b^3 = 1)
    (h : (curve c).toAffine.Nonsingular x y) :
    (curve c).toAffine.Nonsingular (x*b) y := by
  rw [← Affine.equation_iff_nonsingular] at h ⊢
  rw [equation_iff] at h ⊢
  rw [mul_pow, hb, mul_one]
  exact h

/-- The geometric cube-root automorphism fixes y and infinity and scales x. -/
def mapPoint (c b : K) [(curve c).IsElliptic] (hb : b^3 = 1) :
    (curve c).toAffine.Point → (curve c).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (x*b) y (nonsingular_map c b x y hb h)

private theorem root_ne_zero (b : K) (hb : b^3 = 1) : b ≠ 0 := by
  intro hz
  simp only [hz, zero_pow (by omega : 3 ≠ 0), zero_ne_one] at hb

private theorem root_four (b : K) (hb : b^3 = 1) : b^4 = b := by
  rw [show (4 : Nat) = 3+1 from rfl, pow_succ, hb, one_mul]

variable [DecidableEq K]

theorem slope_map (c b x₁ x₂ y₁ y₂ : K) (hb : b^3 = 1) :
    (curve c).toAffine.slope (x₁*b) (x₂*b) y₁ y₂ =
      b^2 * (curve c).toAffine.slope x₁ x₂ y₁ y₂ := by
  have hn := root_ne_zero b hb
  have hx : x₁*b = x₂*b ↔ x₁ = x₂ := mul_left_inj' hn
  simp only [Affine.slope, Affine.negY, curve, hx, zero_mul, sub_zero]
  split_ifs with hxy hy
  · ring
  · ring
  · rw [← sub_mul, div_mul_eq_div_mul_one_div]
    have hi : b⁻¹ = b^2 := by
      apply inv_eq_of_mul_eq_one_right
      calc
        b*b^2 = b^3 := by ring
        _ = 1 := hb
    rw [one_div, hi]
    ring

omit [DecidableEq K] in
theorem addX_map (c b x₁ x₂ l : K) (hb : b^3 = 1) :
    (curve c).toAffine.addX (x₁*b) (x₂*b) (b^2*l) =
      (curve c).toAffine.addX x₁ x₂ l * b := by
  have h4 := root_four b hb
  simp only [Affine.addX, curve, zero_mul, add_zero, sub_zero]
  linear_combination l^2 * h4

omit [DecidableEq K] in
private theorem negY_short (c x y : K) : (curve c).toAffine.negY x y = -y := by
  simp [Affine.negY, curve]

omit [DecidableEq K] in
theorem addY_map (c b x₁ x₂ y₁ l : K) (hb : b^3 = 1) :
    (curve c).toAffine.addY (x₁*b) (x₂*b) y₁ (b^2*l) =
      (curve c).toAffine.addY x₁ x₂ y₁ l := by
  simp only [Affine.addY, negY_short, Affine.negAddY]
  rw [addX_map c b x₁ x₂ l hb]
  linear_combination -l*((curve c).toAffine.addX x₁ x₂ l-x₁)*hb

/-- The geometric map respects the complete affine group law, including vertical lines. -/
theorem map_add (c b : K) [(curve c).IsElliptic] (hb : b^3 = 1)
    (p q : (curve c).toAffine.Point) :
    mapPoint c b hb (p+q) = mapPoint c b hb p + mapPoint c b hb q := by
  cases p with
  | zero =>
    change mapPoint c b hb (0+q) = 0+mapPoint c b hb q
    rw [zero_add, zero_add]
  | some x₁ y₁ h₁ =>
    cases q with
    | zero =>
      change mapPoint c b hb (Affine.Point.some x₁ y₁ h₁+0) =
        mapPoint c b hb (Affine.Point.some x₁ y₁ h₁)+0
      rw [add_zero, add_zero]
    | some x₂ y₂ h₂ =>
      have hn := root_ne_zero b hb
      have hx : x₁*b = x₂*b ↔ x₁ = x₂ := mul_left_inj' hn
      have hy : (curve c).toAffine.negY (x₂*b) y₂ = (curve c).toAffine.negY x₂ y₂ := by
        simp only [Affine.negY, curve, zero_mul, sub_zero]
      by_cases hxy : x₁ = x₂ ∧ y₁ = (curve c).toAffine.negY x₂ y₂
      · have hm : x₁*b = x₂*b ∧ y₁ = (curve c).toAffine.negY (x₂*b) y₂ := by
          exact ⟨hx.mpr hxy.1, hy.symm ▸ hxy.2⟩
        rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        simp only [mapPoint]
        rw [Affine.Point.add_of_Y_eq hm.1 hm.2]
        rfl
      · have hm : ¬(x₁*b = x₂*b ∧ y₁ = (curve c).toAffine.negY (x₂*b) y₂) := by
          simpa only [hx, hy] using hxy
        rw [Affine.Point.add_some hxy]
        simp only [mapPoint]
        rw [Affine.Point.add_some hm]
        simp only [Affine.Point.some.injEq]
        rw [slope_map c b x₁ x₂ y₁ y₂ hb]
        exact ⟨(addX_map c b x₁ x₂ _ hb).symm, (addY_map c b x₁ x₂ y₁ _ hb).symm⟩

/-- The cube-root coordinate automorphism as a mathematical group homomorphism. -/
def hom (c b : K) [(curve c).IsElliptic] (hb : b^3 = 1) :
    (curve c).toAffine.Point →+ (curve c).toAffine.Point where
  toFun := mapPoint c b hb
  map_zero' := rfl
  map_add' := map_add c b hb

#print axioms nonsingular_map
#print axioms slope_map
#print axioms addX_map
#print axioms addY_map
#print axioms map_add
#print axioms hom
end
end CubicEndomorphism

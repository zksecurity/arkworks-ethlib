import CubicEndomorphismProof

open WeierstrassCurve

namespace CubicRelation
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
private theorem root_sum (b : K) (hb : b^3 = 1) (hne : b ≠ 1) : b^2+b+1 = 0 := by
  have h : (b-1)*(b^2+b+1) = 0 := by linear_combination hb
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

/-- A horizontal chord through P and its cube-root image meets the second image. -/
theorem add_map (c b : K) [(CubicEndomorphism.curve c).IsElliptic]
    (hb : b^3 = 1) (hne : b ≠ 1) (p : (CubicEndomorphism.curve c).toAffine.Point) :
    p + CubicEndomorphism.mapPoint c b hb p =
      -CubicEndomorphism.mapPoint c b hb (CubicEndomorphism.mapPoint c b hb p) := by
  cases p with
  | zero =>
    change (0 : (CubicEndomorphism.curve c).toAffine.Point)+0 = -0
    rw [zero_add, neg_zero]
  | some x y h =>
    simp only [CubicEndomorphism.mapPoint, Affine.Point.neg_some]
    by_cases hx : x = 0
    · subst x
      simp only [zero_mul]
      have hn := (Affine.nonsingular_iff 0 y).mp h
      have hy : y ≠ (CubicEndomorphism.curve c).toAffine.negY 0 y := by
        simpa [Affine.negY, CubicEndomorphism.curve] using hn.2
      rw [Affine.Point.add_self_of_Y_ne hy]
      simp [Affine.addX, Affine.addY, Affine.negAddY,
        Affine.negY, Affine.slope, CubicEndomorphism.curve]
    · have hxb : x ≠ x*b := by
        intro he
        have he' : x*b = x*1 := by simpa only [mul_one] using he.symm
        exact hne (mul_left_cancel₀ hx he')
      rw [Affine.Point.add_of_X_ne hxb]
      simp only [Affine.Point.some.injEq]
      have hs : (CubicEndomorphism.curve c).toAffine.slope x (x*b) y y = 0 := by
        rw [Affine.slope, ite_eq_right hxb, sub_self, zero_div]
      rw [hs]
      constructor
      · simp only [Affine.addX, CubicEndomorphism.curve, zero_mul, add_zero,
          sub_zero, zero_pow (by omega : 2 ≠ 0)]
        linear_combination -x*root_sum b hb hne
      · simp only [Affine.addY, Affine.negY, Affine.negAddY,
          CubicEndomorphism.curve, zero_mul, sub_zero, zero_add]

#print axioms add_map
end
end CubicRelation

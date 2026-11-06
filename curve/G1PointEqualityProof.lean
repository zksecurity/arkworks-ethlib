import G1CurveProof

open EthLib.Cryptography.Bls
open WeierstrassCurve

namespace G1PointEquality
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing
local instance (priority := high + 1) : Div Fp := ⟨G1Curve.fieldStructure.div⟩

/-- Equality in the mathematical group is exactly Jacobian cross-coordinate equality. -/
theorem finite_iff (p q : G1) (hp : G1Curve.OnCurve p) (hq : G1Curve.OnCurve q)
    (hpz : p.z ≠ 0) (hqz : q.z ≠ 0) :
    G1Curve.interpret p = G1Curve.interpret q ↔ G1Curve.XEq p q ∧ G1Curve.YEq p q := by
  constructor
  · intro he
    unfold G1Curve.interpret at he
    rw [Jacobian.Point.toAffine_of_Z_ne_zero (G1Curve.nonsingular_finite p hp hpz) hpz,
      Jacobian.Point.toAffine_of_Z_ne_zero (G1Curve.nonsingular_finite q hq hqz) hqz] at he
    have hxy := Affine.Point.some.inj he
    obtain ⟨hx, hy⟩ := hxy
    change p.x/p.z^2 = q.x/q.z^2 at hx
    change p.y/p.z^3 = q.y/q.z^3 at hy
    exact ⟨(div_eq_div_iff (pow_ne_zero 2 hpz) (pow_ne_zero 2 hqz)).mp hx,
      (div_eq_div_iff (pow_ne_zero 3 hpz) (pow_ne_zero 3 hqz)).mp hy⟩
  · rintro ⟨hx, hy⟩
    exact G1Curve.interpret_eq_of_XY p q hpz hqz hx hy

/-- The pinned projective equality formula, including its infinity branches. -/
def model (p q : G1) : Bool :=
  if p.isInfinity then q.isInfinity else if q.isInfinity then false else
    let z1sq := p.z*p.z
    let z2sq := q.z*q.z
    Fp.beq (p.x*z2sq) (q.x*z1sq) &&
      Fp.beq (p.y*(z2sq*q.z)) (q.y*(z1sq*p.z))

private theorem beq_iff (x y : Fp) : Fp.beq x y = true ↔ x = y := by
  simp only [Fp.beq, beq_iff_eq, ← Fin.ext_iff]

private theorem cross_iff (p q : G1) :
    (p.x*(q.z*q.z) = q.x*(p.z*p.z) ∧
      p.y*((q.z*q.z)*q.z) = q.y*((p.z*p.z)*p.z)) ↔ G1Curve.XEq p q ∧ G1Curve.YEq p q := by
  simp only [G1Curve.XEq, G1Curve.YEq, pow_succ, pow_zero, one_mul]

theorem model_iff (p q : G1) (hp : G1Curve.OnCurve p) (hq : G1Curve.OnCurve q) :
    model p q = true ↔ G1Curve.interpret p = G1Curve.interpret q := by
  by_cases hpz : p.z = 0
  · simp only [model, G1.isInfinity, (G1Curve.isZero_iff p.z).mpr hpz, ↓reduceIte,
      G1Curve.isZero_iff, G1Curve.interpret_infinity p hpz]
    exact (G1Curve.interpret_eq_zero_iff q hq).symm.trans eq_comm
  · by_cases hqz : q.z = 0
    · have hpn : p.z.isZero = false := by cases h : p.z.isZero <;> simp_all
      simp only [model, G1.isInfinity, hpn, Bool.false_eq_true, ↓reduceIte,
        (G1Curve.isZero_iff q.z).mpr hqz, G1Curve.interpret_infinity q hqz]
      exact ⟨False.elim, fun he => hpz ((G1Curve.interpret_eq_zero_iff p hp).mp he)⟩
    · have hpn : p.z.isZero = false := by cases h : p.z.isZero <;> simp_all
      have hqn : q.z.isZero = false := by cases h : q.z.isZero <;> simp_all
      simp only [model, G1.isInfinity, hpn, hqn, Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true, beq_iff]
      exact cross_iff p q |>.trans (finite_iff p q hp hq hpz hqz).symm

#print axioms finite_iff
#print axioms model_iff
end
end G1PointEquality

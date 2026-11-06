import G1PointEqualityProof
import G1AffineInterpretationProof
import EthLib.Cryptography.Bls.Compress

open EthLib.Cryptography.Bls

namespace G1Compression
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing
local instance (priority := high + 1) : Div Fp := ⟨G1Curve.fieldStructure.div⟩

theorem infinity_eq (p q : G1) (hp : G1Curve.OnCurve p) (hq : G1Curve.OnCurve q)
    (he : G1Curve.interpret p = G1Curve.interpret q) : p.isInfinity = q.isInfinity := by
  apply Bool.eq_iff_iff.mpr
  simp only [G1.isInfinity, G1Curve.isZero_iff,
    ← G1Curve.interpret_eq_zero_iff p hp, ← G1Curve.interpret_eq_zero_iff q hq, he]

/-- On-curve Jacobian representatives of the same group point export identical affine data. -/
theorem affine_eq (p q : G1) (hp : G1Curve.OnCurve p) (hq : G1Curve.OnCurve q)
    (he : G1Curve.interpret p = G1Curve.interpret q) : G1.toAffine p = G1.toAffine q := by
  by_cases hpz : p.z = 0
  · have hqz := (G1Curve.interpret_eq_zero_iff q hq).mp
      (he.symm.trans (G1Curve.interpret_infinity p hpz))
    simp only [G1.toAffine, (G1Curve.isZero_iff p.z).mpr hpz,
      (G1Curve.isZero_iff q.z).mpr hqz, ↓reduceIte]
  · have hqz : q.z ≠ 0 := by
      intro hz
      exact hpz ((G1Curve.interpret_eq_zero_iff p hp).mp
        (he.trans (G1Curve.interpret_infinity q hz)))
    obtain ⟨hx,hy⟩ := (G1PointEquality.finite_iff p q hp hq hpz hqz).mp he
    rw [G1AffineInterpretation.toAffine_finite p hpz, G1AffineInterpretation.toAffine_finite q hqz]
    apply Prod.ext
    · exact (div_eq_div_iff (pow_ne_zero 2 hpz) (pow_ne_zero 2 hqz)).mpr hx
    · exact (div_eq_div_iff (pow_ne_zero 3 hpz) (pow_ne_zero 3 hqz)).mpr hy

/-- Compression depends only on the mathematical group point on the full curve. -/
theorem compress_eq (p q : G1) (hp : G1Curve.OnCurve p) (hq : G1Curve.OnCurve q)
    (he : G1Curve.interpret p = G1Curve.interpret q) : G1.compress p = G1.compress q := by
  have hi := infinity_eq p q hp hq he
  have ha := affine_eq p q hp hq he
  simp only [G1.compress, hi, ha]

#print axioms infinity_eq
#print axioms affine_eq
#print axioms compress_eq
end
end G1Compression

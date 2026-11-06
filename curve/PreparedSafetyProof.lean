import PreparedCurveGroupProof

open EthLib.Cryptography.Bls
open PreparedCurve

namespace PreparedSafety

noncomputable section
local instance : Field Fp2 := QuadraticDomain.fieldStructure
local instance : DecidableEq Fp2 := Classical.decEq _
local instance : curve.IsElliptic := ellipticStructure

private theorem multiple_ne_anchor {G : Type*} [AddGroup G] (q : G) (k : Nat)
    (hk : 0 < k) (hn : (2*k-1) • q ≠ 0) : (2*k) • q ≠ q := by
  intro he
  apply hn
  have hs : (2*k-1) • q + q = 0+q := by
    calc
      _ = (2*k-1+1) • q := by rw [add_nsmul, one_nsmul]
      _ = (2*k) • q := by congr 1; omega
      _ = _ := by rw [he, zero_add]
  exact add_right_cancel hs

private theorem multiple_ne_neg_anchor {G : Type*} [AddGroup G] (q : G) (k : Nat)
    (hn : (2*k+1) • q ≠ 0) : (2*k) • q ≠ -q := by
  intro he
  apply hn
  rw [add_nsmul, one_nsmul, he, neg_add_cancel]

private theorem x_separation (p : PreparedLine.Hom) (hp : PreparedGeometry.OnCurve p)
    (hz : p.z ≠ 0) (qx qy : Fp2) (hq : curve.toAffine.Equation qx qy)
    (he : point p hp hz ≠ affinePoint qx qy hq)
    (hn : point p hp hz ≠ -affinePoint qx qy hq) : p.x + -(qx*p.z) ≠ 0 := by
  intro h
  have hx : p.x = qx*p.z := by linear_combination h
  have hxn : p.x*p.z⁻¹ = qx := by rw [hx, mul_assoc, mul_inv_cancel₀ hz, mul_one]
  have hpoints : point p hp hz = affinePoint qx qy hq ∨
      point p hp hz = -affinePoint qx qy hq :=
    WeierstrassCurve.Affine.Point.X_eq_iff.mp hxn
  exact hpoints.elim he hn

/-- The group scalar-prefix invariant excludes every exceptional source step.
The factor hypothesis is discharged by the kernel-checked fixed-loop gcd certificate. -/
theorem safe_of_factors (qx qy : Fp2) (hq : curve.toAffine.Equation qx qy)
    (bits k : Nat) (state : PreparedLine.Hom) (hp : PreparedGeometry.OnCurve state)
    (hz : state.z ≠ 0) (hk : 0 < k)
    (hrep : point state hp hz = k • affinePoint qx qy hq)
    (hfactors : ∀ n ∈ PreparedPrefix.factors bits k, n • affinePoint qx qy hq ≠ 0) :
    PreparedReferenceWalk.Safe qx qy bits state := by
  induction bits generalizing k state with
  | zero => trivial
  | succ bits ih =>
    let q := affinePoint qx qy hq
    have hd0 : (2*k) • q ≠ 0 := by
      apply hfactors (2*k)
      rw [PreparedPrefix.factors]
      split_ifs <;> simp
    have hdouble : point state hp hz + point state hp hz ≠ 0 := by
      rw [hrep, ←two_nsmul, ←mul_nsmul]
      simpa only [Nat.mul_comm] using hd0
    have hy := y_nonzero state hp hz hdouble
    let d := (PreparedLine.double state (Fp.inverse (Fp.ofNat 2))).1
    have hdp : PreparedGeometry.OnCurve d :=
      PreparedGeometry.double_onCurve state _ hp PreparedGeometry.source_half
    have hdz : d.z ≠ 0 := PreparedGeometry.double_z_nonzero state _ hy hz
    have hdrep : point d hdp hdz = (2*k) • q := by
      rw [point_double state hp hy hz, hrep, ←two_nsmul, ←mul_nsmul]
      simp only [q, Nat.mul_comm]
    refine ⟨hp, hy, hz, ?_⟩
    by_cases hb : (CurveG1.pairing.BLS_X.val >>> bits)%2 = 1
    · have hm : (2*k-1) • q ≠ 0 := by
        apply hfactors (2*k-1)
        simp only [PreparedPrefix.factors, hb, ite_true, List.mem_cons]
        exact Or.inr (Or.inl True.intro)
      have hplus : (2*k+1) • q ≠ 0 := by
        apply hfactors (2*k+1)
        simp only [PreparedPrefix.factors, hb, ite_true, List.mem_cons]
        exact Or.inr (Or.inr (Or.inl True.intro))
      have hx : d.x + -(qx*d.z) ≠ 0 := by
        apply x_separation d hdp hdz qx qy hq
        · rw [hdrep]
          exact multiple_ne_anchor q k hk hm
        · rw [hdrep]
          exact multiple_ne_neg_anchor q k hplus
      let a := (PreparedLine.add d qx qy).1
      have hap : PreparedGeometry.OnCurve a := add_onCurve d qx qy hdp hq hdz hx
      have haz : a.z ≠ 0 := PreparedGeometry.add_z_nonzero d qx qy hdz hx
      have harep : point a hap haz = (2*k+1) • q := by
        rw [point_add d qx qy hdp hq hdz hx, hdrep, add_nsmul, one_nsmul]
      have htail : ∀ n ∈ PreparedPrefix.factors bits (2*k+1), n • q ≠ 0 := by
        intro n hn
        apply hfactors n
        simp only [PreparedPrefix.factors, hb, ite_true, List.mem_cons]
        exact Or.inr (Or.inr (Or.inr hn))
      simp only [hb, ite_true]
      exact ⟨hx, ih (2*k+1) a hap haz (by omega) harep htail⟩
    · have htail : ∀ n ∈ PreparedPrefix.factors bits (2*k), n • q ≠ 0 := by
        intro n hn
        apply hfactors n
        simp only [PreparedPrefix.factors, hb, ite_false, List.mem_cons]
        exact Or.inr hn
      simp only [hb, ite_false]
      exact ih (2*k) d hdp hdz (by omega) hdrep htail

/-- Every finite on-curve r-torsion anchor satisfies the complete source loop's safety conditions. -/
theorem safe_affine (qx qy : Fp2) (hq : curve.toAffine.Equation qx qy)
    (hr : Fr.modulus • affinePoint qx qy hq = 0) :
    PreparedReferenceWalk.Safe qx qy 63 ⟨qx,qy,1⟩ := by
  have hp : PreparedGeometry.OnCurve ⟨qx,qy,1⟩ := by
    change qy^2*1 = qx^3 + PreparedLine.coeffB*1^3
    simpa only [mul_one, one_pow] using (equation_iff qx qy).mp hq
  have hz : (1 : Fp2) ≠ 0 := one_ne_zero
  have hrep : point ⟨qx,qy,1⟩ hp hz = 1 • affinePoint qx qy hq := by
    simp only [point, affinePoint, WeierstrassCurve.Affine.Point.mk, inv_one, mul_one, one_nsmul]
  have hq0 : affinePoint qx qy hq ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  exact safe_of_factors qx qy hq 63 1 ⟨qx,qy,1⟩ hp hz (by decide) hrep
    (PreparedPrefix.factors_nonzero _ hr hq0)

#print axioms safe_of_factors
#print axioms safe_affine
end
end PreparedSafety

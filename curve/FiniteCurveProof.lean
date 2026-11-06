import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators

namespace FiniteCurve
noncomputable section

open WeierstrassCurve.Affine

/-- Finite coordinate fields give a finite mathematical curve group. -/
theorem finite_points {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) :
    Finite W.toAffine.Point := by
  have h : (Set.univ : Set W.toAffine.Point).Finite := by
    apply Set.Finite.of_finite_fibers (fun (p : W.toAffine.Point) => p.xRep 0) (Set.toFinite _)
    intro x _
    change (Set.univ ∩ {p : W.toAffine.Point | p.xRep 0 = x}).Finite
    simpa only [Set.univ_inter] using finite_preimage_xRep0 (W := W.toAffine) x
  exact Set.finite_univ_iff.mp h

/-- An x-coordinate fiber has at most two finite points and possibly infinity. -/
theorem fiber_card_le_three {F : Type*} [Field F] (W : WeierstrassCurve F) (x : F) :
    Nat.card {p : W.toAffine.Point // p.xRep 0 = x} ≤ 3 := by
  classical
  change ({p : W.toAffine.Point | p.xRep 0 = x} : Set W.toAffine.Point).ncard ≤ 3
  by_cases h : ∃ q : W.toAffine.Point, q.xRep = ![x, 1]
  · obtain ⟨q, hq⟩ := h
    have hs : {p : W.toAffine.Point | p.xRep 0 = x} ⊆ {q, -q, 0} := by
      intro p hp
      cases p with
      | zero => exact Or.inr (Or.inr rfl)
      | some xp yp hn =>
        have hxp : xp = x := hp
        have he : (Point.some xp yp hn).xRep = q.xRep := by
          rw [hq, Point.xRep_some, hxp]
        rcases Point.xRep_eq_xRep_iff.mp he with he | he <;> simp [he]
    refine (Set.ncard_le_ncard hs).trans ?_
    have h1 := Set.ncard_insert_le q ({-q, 0} : Set W.toAffine.Point)
    have h2 := Set.ncard_insert_le (-q) ({0} : Set W.toAffine.Point)
    simp only [Set.ncard_singleton] at h2
    omega
  · have hs : {p : W.toAffine.Point | p.xRep 0 = x} ⊆ {0} := by
      intro p hp
      cases p with
      | zero => exact rfl
      | some xp yp hn =>
        have hxp : xp = x := hp
        exact (h ⟨Point.some xp yp hn, by rw [Point.xRep_some, hxp]⟩).elim
    have hc := Set.ncard_le_ncard hs
    simp only [Set.ncard_singleton] at hc
    omega

/-- A coarse bound sufficient to exclude two independent large prime-order directions. -/
theorem card_le_three_mul {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) :
    Nat.card W.toAffine.Point ≤ 3 * Fintype.card F := by
  let : Finite W.toAffine.Point := finite_points W
  let f : W.toAffine.Point → F := fun p => p.xRep 0
  calc
    _ = Nat.card (Σ x : F, {p : W.toAffine.Point // f p = x}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ x : F, Nat.card {p : W.toAffine.Point // f p = x} := Nat.card_sigma
    _ ≤ ∑ _x : F, 3 := Finset.sum_le_sum fun x _ => fiber_card_le_three W x
    _ = 3 * Fintype.card F := by simp [Nat.mul_comm]

#print axioms finite_points
#print axioms fiber_card_le_three
#print axioms card_le_three_mul
end
end FiniteCurve

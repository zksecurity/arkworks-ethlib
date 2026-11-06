import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace PrimeTorsion

/-- A prime-order point generates all r-torsion when the full group has fewer than r² elements. -/
theorem mem_zmultiples_of_card_lt_sq {G : Type*} [AddCommGroup G] [Finite G]
    (r : Nat) (hr : r.Prime) (g : G) (hg : addOrderOf g = r)
    (hcard : Nat.card G < r*r) (p : G) (hp : r • p = 0) :
    p ∈ AddSubgroup.zmultiples g := by
  let H := AddSubgroup.zmultiples g
  have hH : Nat.card H = r := by simpa only [H, Nat.card_zmultiples] using hg
  have hi : Nat.card (G ⧸ H) < r := by
    have he := H.card_mul_index
    rw [hH, H.index_eq_card] at he
    nlinarith [hr.pos]
  let q : G ⧸ H := QuotientAddGroup.mk p
  have hq : r • q = 0 := by
    change r • (QuotientAddGroup.mk' H p) = 0
    rw [← map_nsmul, hp, map_zero]
  have hd : addOrderOf q ∣ r := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hq
  have hzero : q = 0 := by
    rcases (Nat.dvd_prime hr).mp hd with h1 | hrq
    · exact AddMonoid.addOrderOf_eq_one_iff.mp h1
    · have hle := Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card (G ⧸ H)) (addOrderOf_dvd_natCard q)
      rw [hrq] at hle
      omega
  exact (QuotientAddGroup.eq_zero_iff p).mp hzero

#print axioms mem_zmultiples_of_card_lt_sq
end PrimeTorsion

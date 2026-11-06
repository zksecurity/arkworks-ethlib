import Fp12FrobeniusRefinement
import CyclotomicProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteExtension

namespace ConcreteCyclotomic

private theorem easy_refines (f : Raw12) (hf : Valid12 f) :
    CurveG1.pairing.final_exponentiation_easy f ⦃ r =>
      Valid12 r ∧ decode12 r = Cyclotomic.middle (decode12 f) ⦄ := by
  unfold CurveG1.pairing.final_exponentiation_easy
  step*
  all_goals simp_all [Cyclotomic.middle, Cyclotomic.easy, DodecicField.powNat_eq_pow]

local instance : CommRing Fp12 := DodecicField.ringStructure

/-- The actual extracted easy stages establish the optimized hard stage's precondition. -/
@[step] theorem easy_spec (f : Raw12) (hf : Valid12 f) :
    CurveG1.pairing.final_exponentiation_easy f ⦃ r =>
      Valid12 r ∧ decode12 r = Cyclotomic.middle (decode12 f) ∧
      (decode12 r = Fp12.zero ∨
        Fp12.powNat (decode12 r) (Fp.modulus^4-Fp.modulus^2+1) = Fp12.one) ⦄ := by
  apply spec_mono (easy_refines f hf)
  rintro r ⟨hr,he⟩
  refine ⟨hr,he,?_⟩
  have h := Cyclotomic.middle_zero_or_cyclotomic (decode12 f)
  rw [←he] at h
  have hz : (0 : Fp12) = Fp12.zero := rfl
  have ho : (1 : Fp12) = Fp12.one := rfl
  simpa only [DodecicField.powNat_eq_pow, ←hz, ←ho] using h

#print axioms easy_spec
end ConcreteCyclotomic

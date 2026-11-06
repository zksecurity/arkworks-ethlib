import CyclotomicParameterProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteExtension

namespace ConcreteCyclotomicParameter

local instance : CommRing Fp12 := DodecicField.ringStructure

/-- Extracted absolute-parameter exponentiation computes the power and preserves its domain. -/
@[step] theorem absolute_spec (a : Raw12) (ha : Valid12 a)
    (hg : CyclotomicSquare.Admissible (decode12 a)) :
    CurveG1.pairing.Fp12.cyclotomic_exp_x_abs a ⦃ r =>
      Valid12 r ∧ decode12 r = (decode12 a)^CurveG1.pairing.BLS_X.val ∧
      CyclotomicSquare.Admissible (decode12 r) ⦄ := by
  apply spec_mono (ConcreteCyclotomicExponent.absolute_source_spec a ha)
  rintro r ⟨hr,he⟩
  have hp := he.trans (CyclotomicParameter.absolute_power _ hg)
  refine ⟨hr,hp,?_⟩
  rw [hp]
  exact CyclotomicParameter.power_admissible _ hg _

/-- Extracted exp_by_x follows the negative-parameter convention and preserves its domain. -/
@[step] theorem signed_spec (a : Raw12) (ha : Valid12 a)
    (hg : CyclotomicSquare.Admissible (decode12 a)) :
    CurveG1.pairing.Fp12.exp_by_x a ⦃ r =>
      Valid12 r ∧ decode12 r = ((decode12 a)^CurveG1.pairing.BLS_X.val).conjugate ∧
      CyclotomicSquare.Admissible (decode12 r) ⦄ := by
  apply spec_mono (ConcreteCyclotomicExponent.signed_source_spec a ha)
  rintro r ⟨hr,he⟩
  have hp : decode12 r = ((decode12 a)^CurveG1.pairing.BLS_X.val).conjugate := by
    rw [he, CyclotomicParameter.absolute_power _ hg]
  refine ⟨hr,hp,?_⟩
  rw [hp]
  exact CyclotomicParameter.conjugate_admissible _
    (CyclotomicParameter.power_admissible _ hg _)

#print axioms absolute_spec
#print axioms signed_spec
end ConcreteCyclotomicParameter

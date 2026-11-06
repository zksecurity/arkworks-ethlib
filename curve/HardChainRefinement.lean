import CyclotomicParameterRefinement
import HardChainProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteExtension

namespace ConcreteHardChain
local instance : CommRing Fp12 := DodecicField.ringStructure

@[local step] private theorem square_spec (a : Raw12) (ha : Valid12 a)
    (hg : CyclotomicSquare.Admissible (decode12 a)) :
    CurveG1.pairing.Fp12.cyclotomic_square a ⦃ r =>
      Valid12 r ∧ decode12 r = decode12 a*decode12 a ∧
      CyclotomicSquare.Admissible (decode12 r) ⦄ := by
  apply spec_mono (ConcreteCyclotomicSquare.source_spec a ha)
  rintro r ⟨hr,he⟩
  have hp := he.trans (CyclotomicSquare.square_correct_on_domain _ hg)
  refine ⟨hr,hp,?_⟩
  rw [hp]
  exact CyclotomicParameter.product_admissible _ _ hg hg

@[local step] private theorem multiply_spec (a b : Raw12) (ha : Valid12 a) (hb : Valid12 b)
    (hg : CyclotomicSquare.Admissible (decode12 a))
    (hh : CyclotomicSquare.Admissible (decode12 b)) :
    CurveG1.pairing.Fp12.times a b ⦃ r =>
      Valid12 r ∧ decode12 r = decode12 a*decode12 b ∧
      CyclotomicSquare.Admissible (decode12 r) ⦄ := by
  apply spec_mono (fp12_times_spec a b ha hb)
  rintro r ⟨hr,he⟩
  refine ⟨hr,he,?_⟩
  rw [he]
  exact CyclotomicParameter.product_admissible _ _ hg hh

@[local step] private theorem conjugate_spec (a : Raw12) (ha : Valid12 a)
    (hg : CyclotomicSquare.Admissible (decode12 a)) :
    CurveG1.pairing.Fp12.conjugate a ⦃ r =>
      Valid12 r ∧ decode12 r = (decode12 a).conjugate ∧
      CyclotomicSquare.Admissible (decode12 r) ⦄ := by
  apply spec_mono (fp12_conjugate_spec a ha)
  rintro r ⟨hr,he⟩
  refine ⟨hr,he,?_⟩
  rw [he]
  exact CyclotomicParameter.conjugate_admissible _ hg

@[local step] private theorem frobenius_spec (a : Raw12) (power : Usize) (ha : Valid12 a)
    (hg : CyclotomicSquare.Admissible (decode12 a)) :
    CurveG1.pairing.Fp12.frobenius a power ⦃ r =>
      Valid12 r ∧ decode12 r = (decode12 a)^(Fp.modulus^power.val) ∧
      CyclotomicSquare.Admissible (decode12 r) ⦄ := by
  apply spec_mono (ConcreteFrobenius.fp12_frobenius_spec a power ha)
  rintro r ⟨hr,he⟩
  rw [DodecicField.powNat_eq_pow] at he
  refine ⟨hr,he,?_⟩
  rw [he]
  exact CyclotomicParameter.power_admissible _ hg _

/-- Every extracted hard-chain temporary follows the source-order mathematical chain. -/
theorem source_spec (a : Raw12) (ha : Valid12 a)
    (hg : CyclotomicSquare.Admissible (decode12 a)) :
    CurveG1.pairing.final_exponentiation_hard a ⦃ r =>
      Valid12 r ∧ decode12 r = HardChain.chain (decode12 a) ⦄ := by
  unfold CurveG1.pairing.final_exponentiation_hard
  step*
  all_goals simp_all [HardChain.chain, HardChain.signed]

/-- The optimized extracted hard chain computes the cubed EthLib hard power. -/
@[step] theorem hard_spec (a : Raw12) (ha : Valid12 a)
    (hg : CyclotomicSquare.Admissible (decode12 a)) :
    CurveG1.pairing.final_exponentiation_hard a ⦃ r =>
      Valid12 r ∧ decode12 r = ((decode12 a)^finalExpHard)^3 ⦄ := by
  apply spec_mono (source_spec a ha hg)
  rintro r ⟨hr,he⟩
  exact ⟨hr,he.trans (HardChain.chain_correct _ hg)⟩

#print axioms source_spec
#print axioms hard_spec
end ConcreteHardChain

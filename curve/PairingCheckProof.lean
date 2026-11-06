import ExtensionProof
import EthLibPairingProduct
import CyclotomicRefinement
import HardChainRefinement

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteExtension ConcretePairing

namespace ConcretePairing

local instance : CommRing Fp12 := DodecicField.ringStructure

@[local step] private theorem easy_domain_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.final_exponentiation_easy a ⦃ r =>
      Valid12 r ∧ decode12 r = Cyclotomic.middle (decode12 a) ∧
      CyclotomicSquare.Admissible (decode12 r) ⦄ := by
  apply spec_mono (ConcreteCyclotomic.easy_spec a ha)
  rintro r ⟨hr,he,hg⟩
  refine ⟨hr,he,?_⟩
  simpa only [CyclotomicSquare.Admissible, DodecicField.powNat_eq_pow,
    show (0 : Fp12) = Fp12.zero from rfl, show (1 : Fp12) = Fp12.one from rfl] using hg

/-- The live optimized routine uses arkworks' cubed convention relative to EthLib. -/
@[step] theorem final_exponentiation_cube_spec (f : Raw12) (hf : Valid12 f) :
    CurveG1.pairing.final_exponentiation f ⦃ out => Valid12 out ∧
      decode12 out = (finalExponentiation (decode12 f))^3 ⦄ := by
  unfold CurveG1.pairing.final_exponentiation
  step*
  all_goals simp_all [HardExponent.final_eq_middle_power]
  have hz : decode12 f = Fp12.zero := by
    apply (ExtensionAlignment.quadratic_is_zero _).mp
    simpa only [Bool.and_eq_true] using b_post
  have hc : Fp12.conjugate (0 : Fp12) = 0 := by
    rw [←Cyclotomic.power_six, zero_pow (by decide +kernel : Fp.modulus^6 ≠ 0)]
  have he : Cyclotomic.easy Fp12.zero = 0 := by
    change Fp12.conjugate (0 : Fp12) * Fp12.inverse (0 : Fp12) = 0
    rw [hc, zero_mul]
  rw [hz]
  simp only [Cyclotomic.middle, he, mul_zero,
    zero_pow (by decide +kernel : finalExpHard ≠ 0), zero_pow (by decide : (3 : Nat) ≠ 0)]
  rfl

#print axioms final_exponentiation_cube_spec
end ConcretePairing

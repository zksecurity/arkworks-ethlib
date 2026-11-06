import Fp12FrobeniusRefinement
import CyclotomicSquareProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteExtension

namespace ConcreteCyclotomicSquare

local instance : CommRing Fp2 := QuadraticField.ringStructure

@[simp] private theorem native_sub_eq_add_neg (a b : Fp2) : a-b = a + -b := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  cases a with
  | mk a0 a1 =>
    cases b with
    | mk b0 b1 =>
      change (⟨a0-b0,a1-b1⟩ : Fp2) = ⟨a0 + -b0,a1 + -b1⟩
      congr 1 <;> ring

/-- The source schedule computes the stated polynomial even outside its optimized domain. -/
theorem source_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.cyclotomic_square a ⦃ r =>
      Valid12 r ∧ decode12 r = CyclotomicSquare.square (decode12 a) ⦄ := by
  rcases ha with ⟨⟨h00,h01,h02⟩,⟨h10,h11,h12⟩⟩
  unfold CurveG1.pairing.Fp12.cyclotomic_square
  step*
  all_goals simp_all [Valid12, Valid6, decode12, decode6, CyclotomicSquare.square]
  all_goals (repeat' apply And.intro)
  all_goals ring

local instance : CommRing Fp12 := DodecicField.ringStructure

/-- Extracted Granger–Scott squaring equals ordinary squaring and preserves its precondition. -/
@[step] theorem square_spec (a : Raw12) (ha : Valid12 a)
    (hg : decode12 a = Fp12.zero ∨
      Fp12.powNat (decode12 a) (Fp.modulus^4-Fp.modulus^2+1) = Fp12.one) :
    CurveG1.pairing.Fp12.cyclotomic_square a ⦃ r =>
      Valid12 r ∧ decode12 r = decode12 a*decode12 a ∧
      (decode12 r = Fp12.zero ∨
        Fp12.powNat (decode12 r) (Fp.modulus^4-Fp.modulus^2+1) = Fp12.one) ⦄ := by
  have hz : (0 : Fp12) = Fp12.zero := rfl
  have ho : (1 : Fp12) = Fp12.one := rfl
  have hdomain : CyclotomicSquare.Admissible (decode12 a) := by
    unfold CyclotomicSquare.Admissible
    simpa only [DodecicField.powNat_eq_pow, ←hz, ←ho] using hg
  apply spec_mono (source_spec a ha)
  rintro r ⟨hr,he⟩
  have hs : decode12 r = decode12 a*decode12 a :=
    he.trans (CyclotomicSquare.square_correct_on_domain _ hdomain)
  refine ⟨hr,hs,?_⟩
  have hp := CyclotomicSquare.squared_admissible _ hdomain
  rw [←hs] at hp
  unfold CyclotomicSquare.Admissible at hp
  simpa only [DodecicField.powNat_eq_pow, ←hz, ←ho] using hp

#print axioms source_spec
#print axioms square_spec
end ConcreteCyclotomicSquare

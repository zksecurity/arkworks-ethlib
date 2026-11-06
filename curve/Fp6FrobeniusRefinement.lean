import ExtensionProof
import Fp6FrobeniusProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteField ConcreteExtension

namespace ConcreteFrobenius

private def pair (a : Aeneas.Std.Array Raw 2#usize) : Raw2 :=
  ⟨a.val[0]'(by simp),a.val[1]'(by simp)⟩

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem coefficients (i : Nat) (hi : i < 6) :
    let first := (CurveG1.field.FROBENIUS_FP6_C1.val)[i]'(by simpa using hi)
    let second := (CurveG1.field.FROBENIUS_FP6_C2.val)[i]'(by simpa using hi)
    Valid2 (pair first) ∧ decode2 (pair first) = CubicFrobenius.coefficient i ∧
    Valid2 (pair second) ∧ decode2 (pair second) =
      CubicFrobenius.coefficient i*CubicFrobenius.coefficient i := by
  interval_cases i
  all_goals dsimp only
  all_goals refine ⟨?_,?_,?_,?_⟩
  all_goals first
    | (unfold Valid2 FieldProof.Valid pair; constructor <;> decide +kernel +revert)
    | (apply ext2 <;> decide +kernel +revert)

private theorem fp6_frobenius_map_spec (a : Raw6) (power : Usize) (ha : Valid6 a) :
    CurveG1.pairing.Fp6.frobenius a power ⦃ r =>
      Valid6 r ∧ decode6 r = CubicFrobenius.map (decode6 a) power.val ⦄ := by
  rcases ha with ⟨ha0,ha1,ha2⟩
  unfold CurveG1.pairing.Fp6.frobenius
  step*
  all_goals have hc := coefficients i.val (by omega)
  all_goals dsimp only at hc
  all_goals rw [←first_post, ←second_post] at hc
  all_goals simp only [pair] at hc
  all_goals simp_all [Valid2, Valid6, decode2, decode6, CubicFrobenius.map,
    CubicFrobenius.coefficient]

local instance : CommRing Fp6 := CubicField.ringStructure

/-- Extracted cubic Frobenius agrees with the full modulus power in the unchanged EthLib ring. -/
@[step] theorem fp6_frobenius_spec (a : Raw6) (power : Usize) (ha : Valid6 a) :
    CurveG1.pairing.Fp6.frobenius a power ⦃ r =>
      Valid6 r ∧ decode6 r = decode6 a^(Fp.modulus^power.val) ⦄ := by
  apply spec_mono (fp6_frobenius_map_spec a power ha)
  rintro r ⟨hr,he⟩
  exact ⟨hr, he.trans (CubicFrobenius.map_eq_power (decode6 a) power.val)⟩

#print axioms fp6_frobenius_spec
end ConcreteFrobenius

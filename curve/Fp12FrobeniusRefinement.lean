import Fp6FrobeniusRefinement
import Fp12FrobeniusProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteField ConcreteExtension

namespace ConcreteFrobenius

private def pair12 (a : Aeneas.Std.Array Raw 2#usize) : Raw2 :=
  ⟨a.val[0]'(by simp),a.val[1]'(by simp)⟩

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem coefficient12 (i : Nat) (hi : i < 12) :
    let entry := (CurveG1.field.FROBENIUS_FP12_C1.val)[i]'(by simpa using hi)
    Valid2 (pair12 entry) ∧ decode2 (pair12 entry) = DodecicFrobenius.coefficient i := by
  interval_cases i
  all_goals dsimp only
  all_goals refine ⟨?_,?_⟩
  all_goals first
    | (unfold Valid2 FieldProof.Valid pair12; constructor <;> decide +kernel +revert)
    | (apply ext2 <;> decide +kernel +revert)

private theorem fp12_frobenius_map_spec (a : Raw12) (power : Usize) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.frobenius a power ⦃ r =>
      Valid12 r ∧ decode12 r = DodecicFrobenius.map (decode12 a) power.val ⦄ := by
  rcases ha with ⟨ha0,ha1⟩
  unfold CurveG1.pairing.Fp12.frobenius
  step*
  all_goals have hc := coefficient12 i.val (by omega)
  all_goals dsimp only at hc
  all_goals rw [←entry_post] at hc
  all_goals
    have hperiod : DodecicFrobenius.coefficient i.val =
        DodecicFrobenius.coefficient power.val := by
      unfold DodecicFrobenius.coefficient
      rw [i_post, Nat.mod_mod]
    rw [hperiod] at hc
    simp only [pair12] at hc
    simp_all [Valid2, Valid6, Valid12, decode2, decode6, decode12,
      DodecicFrobenius.map, CubicField.mul_ofFp2]
  refine ⟨?_,?_,?_⟩
  · exact congrArg (fun x : Fp2 => x*DodecicFrobenius.coefficient power.val)
      (congrArg Fp6.c0 c1_post1)
  · exact congrArg (fun x : Fp2 => x*DodecicFrobenius.coefficient power.val)
      (congrArg Fp6.c1 c1_post1)
  · exact congrArg (fun x : Fp2 => x*DodecicFrobenius.coefficient power.val)
      (congrArg Fp6.c2 c1_post1)

/-- Extracted degree-twelve Frobenius agrees with the pinned executable modulus power. -/
@[step] theorem fp12_frobenius_spec (a : Raw12) (power : Usize) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.frobenius a power ⦃ r =>
      Valid12 r ∧ decode12 r = Fp12.powNat (decode12 a) (Fp.modulus^power.val) ⦄ := by
  apply spec_mono (fp12_frobenius_map_spec a power ha)
  rintro r ⟨hr,he⟩
  exact ⟨hr, he.trans (DodecicFrobenius.map_eq_power (decode12 a) power.val)⟩

#print axioms fp12_frobenius_spec
end ConcreteFrobenius

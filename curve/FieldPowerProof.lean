import FieldPowerModelProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteField

namespace ConcreteFieldPower

@[step] theorem exponent_bit_spec (e : Limbs) (index : U32) (hi : index.val < 384) :
    CurveG1.field.exponent_bit e index ⦃ out => out = (value e).testBit index.val ⦄ := by
  have hw : index.val / 64 < e.val.length := by simp; omega
  unfold CurveG1.field.exponent_bit
  step*
  all_goals rw [SourceFieldPower.exponent_testBit e index.val hi]
  all_goals simp_all [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, UScalar.eq_equiv]

private theorem loop_step (a : Fp) (k bits : Nat) (started : Bool) (acc : Fp) (hb : bits ≠ 0) :
    SourceFieldPower.loopBits a k bits started acc =
      (if !started && !(k.testBit (bits-1)) then
        SourceFieldPower.loopBits a k (bits-1) false acc
      else SourceFieldPower.loopBits a k (bits-1) true
        (if k.testBit (bits-1) then (acc*acc)*a else acc*acc)) := by
  cases bits
  · exact False.elim (hb rfl)
  · rfl

@[step] theorem pow_loop_spec (a : Raw) (e : Limbs) (bits : U32) (started : Bool) (acc : Raw)
    (ha : Valid a) (hbits : bits.val ≤ 384) (hacc : Valid acc) :
    CurveG1.field.pow_loop a e bits started acc ⦃ out => Valid out ∧ decode out =
      SourceFieldPower.loopBits (decode a) (value e) bits.val started (decode acc) ⦄ := by
  by_cases hz : bits = 0#u32
  · rw [CurveG1.field.pow_loop]
    simp_all [SourceFieldPower.loopBits]
  · have hpos : 0 < bits.val := by scalar_tac
    have hn : bits.val ≠ 0 := by omega
    cases started <;> cases hs : (value e).testBit (bits.val-1)
    all_goals rw [CurveG1.field.pow_loop, loop_step _ _ _ _ _ hn]
    all_goals step*
    all_goals simp_all
    all_goals step*
termination_by bits.val
decreasing_by all_goals scalar_tac

@[step] theorem pow_spec (a : Raw) (e : Limbs) (ha : Valid a) :
    CurveG1.field.pow a e ⦃ out => Valid out ∧ decode out = Fp.powNat (decode a) (value e) ⦄ := by
  unfold CurveG1.field.pow
  step as ⟨one, ho, heo⟩
  apply spec_mono (pow_loop_spec a e 384#u32 false one ha (by decide) ho)
  rintro out ⟨hv, heout⟩
  refine ⟨hv, ?_⟩
  rw [heout, heo]
  change SourceFieldPower.loopBits (decode a) (value e) 384 false (Fp.ofNat 1) =
    Fp.powNat (decode a) (value e)
  have hb : B^6 = 2^384 := by rw [FieldProof.B, ← pow_mul]
  have he : value e < 2^384 := by simpa only [hb] using FieldProof.value_bound e
  rw [show Fp.ofNat 1 = (1 : Fp) by decide +kernel,
    SourceFieldPower.loop_initial, Nat.mod_eq_of_lt he, BaseField.powNat_eq_pow]

#print axioms exponent_bit_spec
#print axioms pow_loop_spec
#print axioms pow_spec
end ConcreteFieldPower

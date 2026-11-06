import FieldPowerProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteField

namespace OptimizedFieldPower
local instance : CommRing Fp := Fin.instCommRing Fp.modulus

@[step] theorem exponent_bit_spec (e : Limbs) (index : U32) (hi : index.val < 384) :
    CurveG1.optimized.field_power.exponent_bit e index ⦃ out =>
      out = (value e).testBit index.val ⦄ := by
  simpa only [CurveG1.optimized.field_power.exponent_bit, CurveG1.field.exponent_bit] using
    ConcreteFieldPower.exponent_bit_spec e index hi

private theorem loop_step (a : Fp) (k bits : Nat) (started : Bool) (acc : Fp) (hb : bits ≠ 0) :
    SourceFieldPower.loopBits a k bits started acc =
      (if !started && !(k.testBit (bits-1)) then
        SourceFieldPower.loopBits a k (bits-1) false acc
      else SourceFieldPower.loopBits a k (bits-1) true
        (if k.testBit (bits-1) then (acc*acc)*a else acc*acc)) := by
  cases bits
  · exact False.elim (hb rfl)
  · rfl

/-- Before the first set bit the accumulator is one; afterwards it has the original loop's meaning. -/
@[step] theorem pow_loop_spec (a : Raw) (e : Limbs) (bits : U32) (started : Bool) (acc : Raw)
    (ha : Valid a) (hbits : bits.val ≤ 384) (hacc : Valid acc)
    (hinit : started = false → decode acc = 1) :
    CurveG1.optimized.field_power.pow_loop a e bits started acc ⦃ out =>
      Valid out ∧ decode out =
        SourceFieldPower.loopBits (decode a) (value e) bits.val started (decode acc) ⦄ := by
  by_cases hz : bits = 0#u32
  · rw [CurveG1.optimized.field_power.pow_loop]
    simp_all [SourceFieldPower.loopBits]
  · have hpos : 0 < bits.val := by scalar_tac
    have hn : bits.val ≠ 0 := by omega
    cases started <;> cases hs : (value e).testBit (bits.val-1)
    all_goals rw [CurveG1.optimized.field_power.pow_loop, loop_step _ _ _ _ _ hn]
    all_goals step*
    all_goals simp_all
    all_goals step*
termination_by bits.val
decreasing_by all_goals scalar_tac

/-- The optimized extracted Rust computes the same EthLib power for every canonical base and exponent. -/
@[step] theorem pow_spec (a : Raw) (e : Limbs) (ha : Valid a) :
    CurveG1.optimized.field_power.pow a e ⦃ out =>
      Valid out ∧ decode out = Fp.powNat (decode a) (value e) ⦄ := by
  unfold CurveG1.optimized.field_power.pow
  step as ⟨one, ho, heo⟩
  have hone : Fp.ofNat 1 = (1 : Fp) := by decide +kernel
  apply spec_mono (pow_loop_spec a e 384#u32 false one ha (by decide) ho (by intro _; exact heo.trans hone))
  rintro out ⟨hv, heout⟩
  refine ⟨hv, ?_⟩
  rw [heout, heo]
  change SourceFieldPower.loopBits (decode a) (value e) 384 false (Fp.ofNat 1) =
    Fp.powNat (decode a) (value e)
  have hb : B^6 = 2^384 := by rw [FieldProof.B, ← pow_mul]
  have he : value e < 2^384 := by simpa only [hb] using FieldProof.value_bound e
  rw [hone, SourceFieldPower.loop_initial, Nat.mod_eq_of_lt he, BaseField.powNat_eq_pow]

/-- Any successful outputs from the two functions have identical canonical Montgomery values. -/
theorem same_montgomery_value (a : Raw) (e : Limbs) (ha : Valid a) (original optimized : Raw)
    (hOriginal : CurveG1.field.pow a e = .ok original)
    (hOptimized : CurveG1.optimized.field_power.pow a e = .ok optimized) :
    value original.limbs = value optimized.limbs := by
  have h1 := ConcreteFieldPower.pow_spec a e ha
  have h2 := pow_spec a e ha
  rw [hOriginal, spec_ok] at h1
  rw [hOptimized, spec_ok] at h2
  exact (decode_injective original optimized h1.1 h2.1).mp (h1.2.trans h2.2.symm)

/-- Both extracted computations terminate and return the same canonical Montgomery value. -/
theorem equivalence_spec (a : Raw) (e : Limbs) (ha : Valid a) :
    (do
      let original ← CurveG1.field.pow a e
      let optimized ← CurveG1.optimized.field_power.pow a e
      pure (original, optimized)) ⦃ out =>
        Valid out.1 ∧ Valid out.2 ∧ value out.1.limbs = value out.2.limbs ⦄ := by
  step as ⟨original, ho, heo⟩
  step as ⟨optimized, hn, hen⟩
  exact ⟨ho, hn, (decode_injective original optimized ho hn).mp (heo.trans hen.symm)⟩

#print axioms exponent_bit_spec
#print axioms pow_loop_spec
#print axioms pow_spec
#print axioms same_montgomery_value
#print axioms equivalence_spec
end OptimizedFieldPower

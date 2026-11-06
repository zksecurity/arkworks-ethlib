import FieldPowerProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteField

namespace AlternativeFieldPower
local instance : CommRing Fp := Fin.instCommRing Fp.modulus

@[step] theorem exponent_bit_spec (e : Limbs) (index : U32) (hi : index.val < 384) :
    CurveG1.alternative.field_power.exponent_bit e index ⦃ out =>
      out = (value e).testBit index.val ⦄ := by
  simpa only [CurveG1.alternative.field_power.exponent_bit, CurveG1.field.exponent_bit] using
    ConcreteFieldPower.exponent_bit_spec e index hi

/-- The accumulator contains the consumed low bits; the running base supplies the next power of two. -/
theorem pow_loop_spec (a : Fp) (power : Raw) (e : Limbs) (index : U32) (acc : Raw)
    (hi : index.val ≤ 384) (hp : Valid power) (ha : Valid acc)
    (hpower : decode power = a^(2^index.val))
    (hacc : decode acc = a^(value e % 2^index.val)) :
    CurveG1.alternative.field_power.pow_loop power e index acc ⦃ out =>
      Valid out ∧ decode out = Fp.powNat a (value e) ⦄ := by
  by_cases hz : index = 384#u32
  · rw [CurveG1.alternative.field_power.pow_loop]
    have hb : B^6 = 2^384 := by rw [FieldProof.B, ← pow_mul]
    have he : value e < 2^384 := by simpa only [hb] using FieldProof.value_bound e
    simp only [hz, ↓reduceIte, spec_ok]
    constructor
    · exact ha
    · rw [BaseField.powNat_eq_pow]
      have hi384 : index.val = 384 := by rw [hz]; rfl
      rw [hi384] at hacc
      simpa only [Nat.mod_eq_of_lt he] using hacc
  · have hlt : index.val < 384 := by scalar_tac
    rw [CurveG1.alternative.field_power.pow_loop]
    simp only [hz, ↓reduceIte]
    step as ⟨set, hset⟩
    cases hs : (value e).testBit index.val
    · simp only [hs] at hset
      simp only [hset, Bool.false_eq_true, ↓reduceIte]
      step as ⟨squared, hv, he⟩
      step as ⟨nextIndex, hnext⟩
      apply pow_loop_spec a squared e nextIndex acc
      · scalar_tac
      · exact hv
      · exact ha
      · rw [he, hpower, hnext, Nat.pow_succ, pow_mul, pow_two]
      · rw [hnext, GLVGroup.low_bits_succ, hs]
        simpa only [Bool.toNat_false, zero_mul, add_zero] using hacc
    · simp only [hs] at hset
      simp only [hset, ↓reduceIte]
      step as ⟨next, hn, hen⟩
      step as ⟨squared, hv, he⟩
      step as ⟨nextIndex, hnext⟩
      apply pow_loop_spec a squared e nextIndex next
      · scalar_tac
      · exact hv
      · exact hn
      · rw [he, hpower, hnext, Nat.pow_succ, pow_mul, pow_two]
      · rw [hen, hacc, hpower, hnext, GLVGroup.low_bits_succ, hs]
        simp only [Bool.toNat_true, one_mul, pow_add]
termination_by 384 - index.val
decreasing_by all_goals scalar_tac

/-- The LSB-first Rust computes EthLib exponentiation for every canonical base and six-word exponent. -/
@[step] theorem pow_spec (a : Raw) (e : Limbs) (ha : Valid a) :
    CurveG1.alternative.field_power.pow a e ⦃ out =>
      Valid out ∧ decode out = Fp.powNat (decode a) (value e) ⦄ := by
  unfold CurveG1.alternative.field_power.pow
  step as ⟨one, ho, heo⟩
  apply pow_loop_spec (decode a) a e 0#u32 one (by decide) ha ho
  · simp
  · rw [heo]
    have hz : (0#u32).val = 0 := by scalar_tac
    rw [hz, Nat.pow_zero, Nat.mod_one, pow_zero]
    decide +kernel

/-- The two algorithms terminate with identical canonical Montgomery values despite different schedules. -/
theorem equivalence_spec (a : Raw) (e : Limbs) (ha : Valid a) :
    (do
      let original ← CurveG1.field.pow a e
      let alternative ← CurveG1.alternative.field_power.pow a e
      pure (original, alternative)) ⦃ out =>
        Valid out.1 ∧ Valid out.2 ∧ value out.1.limbs = value out.2.limbs ⦄ := by
  step as ⟨original, ho, heo⟩
  step as ⟨alternative, hn, hen⟩
  exact ⟨ho, hn, (decode_injective original alternative ho hn).mp (heo.trans hen.symm)⟩

#print axioms exponent_bit_spec
#print axioms pow_loop_spec
#print axioms pow_spec
#print axioms equivalence_spec
end AlternativeFieldPower

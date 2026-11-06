import MontgomeryProof
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof MontgomeryProof

namespace MontgomeryConversion

/-- Interpret the cyclic array from the limb position used by upstream's loop. -/
def rotatedValue (a : Limbs) (index : Nat) : Nat :=
  a[index % 6]!.val + B * a[(index + 1) % 6]!.val + B^2 * a[(index + 2) % 6]!.val +
  B^3 * a[(index + 3) % 6]!.val + B^4 * a[(index + 4) % 6]!.val + B^5 * a[(index + 5) % 6]!.val

@[simp] theorem rotated_zero (a : Limbs) : rotatedValue a 0 = value a := by
  simp [rotatedValue, value]

@[simp] theorem rotated_six (a : Limbs) : rotatedValue a 6 = value a := by
  simp [rotatedValue, value]

theorem discarded_zero (x carry low : U64)
    (heq : low.val + B * carry.val =
      x.val + (x.val * 0x89f3fffcfffcfffd % B) * 0xb9feffffffffaaab) : low = 0#u64 := by
  have hc := cancel_low x.val
  unfold B at *
  scalar_tac

def ConversionPost (r : Limbs) (index : Nat) (out : CurveG1.montgomery.ConversionRound) : Prop :=
  B * rotatedValue out.limbs (index + 1) + out.discarded.val =
    rotatedValue r index + out.factor.val * Fp.modulus ∧ out.discarded = 0#u64

-- Separate fixed-index lemmas keep each unrolled arithmetic proof within the default budget.
private theorem conversion_0 (r : Limbs) :
    CurveG1.montgomery.conversion_round r 0#usize ⦃ out => ConversionPost r 0 out ⦄ := by
  unfold ConversionPost CurveG1.montgomery.conversion_round
  step*
  have hz : discarded = 0#u64 := by
    apply discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [rotatedValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq, Aeneas.Std.Array.set]
  simp_all [B, Fp.modulus, Nat.mul_add]
  omega

private theorem conversion_1 (r : Limbs) :
    CurveG1.montgomery.conversion_round r 1#usize ⦃ out => ConversionPost r 1 out ⦄ := by
  unfold ConversionPost CurveG1.montgomery.conversion_round
  step*
  have hz : discarded = 0#u64 := by
    apply discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [rotatedValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq, Aeneas.Std.Array.set]
  simp_all [B, Fp.modulus, Nat.mul_add]
  omega

private theorem conversion_2 (r : Limbs) :
    CurveG1.montgomery.conversion_round r 2#usize ⦃ out => ConversionPost r 2 out ⦄ := by
  unfold ConversionPost CurveG1.montgomery.conversion_round
  step*
  have hz : discarded = 0#u64 := by
    apply discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [rotatedValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq, Aeneas.Std.Array.set]
  simp_all [B, Fp.modulus, Nat.mul_add]
  omega

private theorem conversion_3 (r : Limbs) :
    CurveG1.montgomery.conversion_round r 3#usize ⦃ out => ConversionPost r 3 out ⦄ := by
  unfold ConversionPost CurveG1.montgomery.conversion_round
  step*
  have hz : discarded = 0#u64 := by
    apply discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [rotatedValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq, Aeneas.Std.Array.set]
  simp_all [B, Fp.modulus, Nat.mul_add]
  omega

private theorem conversion_4 (r : Limbs) :
    CurveG1.montgomery.conversion_round r 4#usize ⦃ out => ConversionPost r 4 out ⦄ := by
  unfold ConversionPost CurveG1.montgomery.conversion_round
  step*
  have hz : discarded = 0#u64 := by
    apply discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [rotatedValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq, Aeneas.Std.Array.set]
  simp_all [B, Fp.modulus, Nat.mul_add]
  omega

private theorem conversion_5 (r : Limbs) :
    CurveG1.montgomery.conversion_round r 5#usize ⦃ out => ConversionPost r 5 out ⦄ := by
  unfold ConversionPost CurveG1.montgomery.conversion_round
  step*
  have hz : discarded = 0#u64 := by
    apply discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [rotatedValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq, Aeneas.Std.Array.set]
  simp_all [B, Fp.modulus, Nat.mul_add]
  omega

theorem conversion_equation (r : Limbs) (index : Usize) (hi : index.val < 6) :
    CurveG1.montgomery.conversion_round r index ⦃ out => ConversionPost r index.val out ⦄ := by
  interval_cases hindex : index.val
  · have he : index = 0#usize := by scalar_tac
    subst index
    exact conversion_0 r
  · have he : index = 1#usize := by scalar_tac
    subst index
    exact conversion_1 r
  · have he : index = 2#usize := by scalar_tac
    subst index
    exact conversion_2 r
  · have he : index = 3#usize := by scalar_tac
    subst index
    exact conversion_3 r
  · have he : index = 4#usize := by scalar_tac
    subst index
    exact conversion_4 r
  · have he : index = 5#usize := by scalar_tac
    subst index
    exact conversion_5 r

@[step] theorem conversion_round_spec (r : Limbs) (index : Usize)
    (hi : index.val < 6) (hr : rotatedValue r index.val < Fp.modulus) :
    CurveG1.montgomery.conversion_round r index ⦃ out =>
      B * rotatedValue out.limbs (index.val + 1) =
        rotatedValue r index.val + out.factor.val * Fp.modulus ∧
      rotatedValue out.limbs (index.val + 1) < Fp.modulus ⦄ := by
  apply spec_mono (conversion_equation r index hi)
  rintro out ⟨heq, hz⟩
  have heq' : B * rotatedValue out.limbs (index.val + 1) =
      rotatedValue r index.val + out.factor.val * Fp.modulus := by
    simpa only [hz, UScalar.ofNatCore_val_eq, Nat.add_zero] using heq
  refine ⟨heq', ?_⟩
  have hk : out.factor.val ≤ B - 1 := by unfold B; scalar_tac
  have hm := Nat.mul_le_mul_right Fp.modulus hk
  simp only [B, Fp.modulus, Nat.reducePow, Nat.reduceSub] at *
  omega

@[step] theorem into_canonical_spec (a : Limbs) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.into_canonical a ⦃ out =>
      value out < Fp.modulus ∧ value out = (value a * rInverse) % Fp.modulus ⦄ := by
  unfold CurveG1.montgomery.into_canonical
  step*
  all_goals simp_all only [UScalar.ofNatCore_val_eq, Nat.reduceAdd, rotated_zero, rotated_six]
  refine ⟨by trivial, ?_⟩
  have heq := telescope (value a) 1 0 0 0 0 0
    r0.factor.val r1.factor.val r2.factor.val r3.factor.val r4.factor.val cr.factor.val
    (rotatedValue r0.limbs 1) (rotatedValue r1.limbs 2) (rotatedValue r2.limbs 3)
    (rotatedValue r3.limbs 4) (rotatedValue r4.limbs 5) (value cr.limbs)
    (by simpa using r0_post) (by simpa using r1_post) (by simpa using r2_post)
    (by simpa using r3_post) (by simpa using r4_post) (by simpa using cr_post)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at heq
  have hmod : (B^6 * value cr.limbs) % Fp.modulus = value a % Fp.modulus := by
    rw [heq]
    simp [Nat.add_mod]
  have hc := cancel_radix _ _ hmod
  simpa only [Nat.mod_eq_of_lt (by assumption : value cr.limbs < Fp.modulus)] using hc

theorem radix_shift (n : Nat) : (n * B^6 * rInverse) % Fp.modulus = n % Fp.modulus := by
  have h := Nat.mul_mod n (B^6 * rInverse) Fp.modulus
  rw [radix_inverse] at h
  simpa [Nat.mul_assoc] using h

theorem encode_r2 (n : Nat) :
    (n * value CurveG1.montgomery.R2 * rInverse) % Fp.modulus = (n * B^6) % Fp.modulus := by
  rw [r2_constant]
  have hp : B^12 = B^6 * B^6 := by ring
  calc
    (n * (B^12 % Fp.modulus) * rInverse) % Fp.modulus =
        (n * B^12 * rInverse) % Fp.modulus := by simp [Nat.mul_mod]
    _ = (n * B^6 * B^6 * rInverse) % Fp.modulus := by rw [hp, ← Nat.mul_assoc]
    _ = (n * B^6) % Fp.modulus := radix_shift _

attribute [local step] MontgomeryProof.multiply_value

@[step] theorem from_canonical_spec (a : Limbs) :
    CurveG1.montgomery.from_canonical a ⦃ out =>
      (∀ x, out = some x → value x < Fp.modulus) ∧
      out.map value = if value a < Fp.modulus then some ((value a * B^6) % Fp.modulus) else none ⦄ := by
  unfold CurveG1.montgomery.from_canonical
  step*
  all_goals simp only [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at *
  all_goals try simp only [modulus_value, encode_r2] at *
  all_goals simp_all [value, B, Fp.modulus]

#print axioms conversion_equation
#print axioms conversion_round_spec
#print axioms into_canonical_spec
#print axioms from_canonical_spec
end MontgomeryConversion

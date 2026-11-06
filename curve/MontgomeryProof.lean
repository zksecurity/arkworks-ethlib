import LimbProof
import Mathlib.Tactic.ClearExcept
import Mathlib.Tactic.LinearCombination

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof

namespace MontgomeryProof

@[step] theorem mac_spec (a b c carry : U64) :
    CurveG1.montgomery.mac a b c carry ⦃ out =>
      out.1.val + B * out.2.val = a.val + b.val * c.val + carry.val ∧
      out.2.val ≤ b.val + 1 ∧ out.2.val ≤ c.val + 1 ⦄ := by
  have ha : a.val ≤ B - 1 := by unfold B; scalar_tac
  have hb : b.val ≤ B - 1 := by unfold B; scalar_tac
  have hc : c.val ≤ B - 1 := by unfold B; scalar_tac
  have hd : carry.val ≤ B - 1 := by unfold B; scalar_tac
  have hm := Nat.mul_le_mul hb hc
  have hm3 := Nat.mul_le_mul_right c.val hb
  have hm2 := Nat.mul_le_mul_left b.val hc
  have ht : a.val + b.val * c.val + carry.val < 2 ^ 128 := by
    norm_num [B] at *
    omega
  unfold CurveG1.montgomery.mac
  step*
  all_goals simp_all only [U64.cast_U128_val_eq]
  all_goals simp_all [B, Nat.shiftRight_eq_div_pow, UScalar.cast_val_eq]
  all_goals scalar_tac

theorem cancel_low (x : Nat) :
    (x + ((x * 0x89f3fffcfffcfffd) % B) * 0xb9feffffffffaaab) % B = 0 := by
  unfold B
  omega

theorem round_equation (a r : Limbs) (digit : U64) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.round a digit r ⦃ out =>
      B * value out.limbs + out.discarded.val =
        value r + value a * digit.val + out.factor.val * Fp.modulus ∧
      out.discarded = 0#u64 ⦄ := by
  have hatop : a[5]!.val ≤ 0x1a0111ea397fe69a := by
    unfold value B Fp.modulus at ha
    scalar_tac
  unfold CurveG1.montgomery.round
  step*
  all_goals simp_all [CurveG1.field.MODULUS, Array.getElem!_Nat_eq]
  · scalar_tac
  · constructor
    · simp_all [value, B, Fp.modulus, Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
        Array.getElem!_Nat_eq]
      omega
    · clear * - discarded_post k_post
      have hc := cancel_low t0.val
      simp_all [CurveG1.montgomery.INV, core.num.U64.wrapping_mul]
      simp only [B, U64.size, U64.numBits] at *
      scalar_tac

@[step] theorem round_spec (a r : Limbs) (digit : U64)
    (ha : value a < Fp.modulus) (hr : value r < value a + Fp.modulus) :
    CurveG1.montgomery.round a digit r ⦃ out =>
      B * value out.limbs = value r + value a * digit.val + out.factor.val * Fp.modulus ∧
      value out.limbs < value a + Fp.modulus ⦄ := by
  apply spec_mono (round_equation a r digit ha)
  rintro out ⟨heq, hz⟩
  have heq' : B * value out.limbs = value r + value a * digit.val + out.factor.val * Fp.modulus := by
    simpa only [hz, UScalar.ofNatCore_val_eq, Nat.add_zero] using heq
  refine ⟨heq', ?_⟩
  have hd : digit.val ≤ B - 1 := by unfold B; scalar_tac
  have hk : out.factor.val ≤ B - 1 := by unfold B; scalar_tac
  have hprod := Nat.mul_le_mul_left (value a) hd
  have hred := Nat.mul_le_mul_right Fp.modulus hk
  simp only [B, Fp.modulus, Nat.reducePow, Nat.reduceSub] at *
  omega

@[step] theorem reduce_spec (r : Limbs) (hr : value r < 2 * Fp.modulus) :
    CurveG1.montgomery.reduce r ⦃ out =>
      value out < Fp.modulus ∧ value out = value r % Fp.modulus ⦄ := by
  unfold CurveG1.montgomery.reduce
  step*
  all_goals simp_all [Fp.modulus]
  all_goals omega

theorem telescope (a b0 b1 b2 b3 b4 b5 k0 k1 k2 k3 k4 k5 r0 r1 r2 r3 r4 r5 : Nat)
    (h0 : B * r0 = a * b0 + k0 * Fp.modulus)
    (h1 : B * r1 = r0 + a * b1 + k1 * Fp.modulus)
    (h2 : B * r2 = r1 + a * b2 + k2 * Fp.modulus)
    (h3 : B * r3 = r2 + a * b3 + k3 * Fp.modulus)
    (h4 : B * r4 = r3 + a * b4 + k4 * Fp.modulus)
    (h5 : B * r5 = r4 + a * b5 + k5 * Fp.modulus) :
    B ^ 6 * r5 = a * (b0 + B * b1 + B ^ 2 * b2 + B ^ 3 * b3 + B ^ 4 * b4 + B ^ 5 * b5) +
      Fp.modulus * (k0 + B * k1 + B ^ 2 * k2 + B ^ 3 * k3 + B ^ 4 * k4 + B ^ 5 * k5) := by
  linear_combination h0 + B * h1 + B ^ 2 * h2 + B ^ 3 * h3 + B ^ 4 * h4 + B ^ 5 * h5

@[step] theorem multiply_spec (a b : Limbs) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.multiply a b ⦃ out =>
      value out < Fp.modulus ∧
      (B ^ 6 * value out) % Fp.modulus = (value a * value b) % Fp.modulus ⦄ := by
  have hp := Fp.modulus_pos
  unfold CurveG1.montgomery.multiply
  step*
  all_goals simp_all only [zero_value]
  · omega
  · refine ⟨True.intro, ?_⟩
    have heq := telescope (value a) (b.val[0]).val (b.val[1]).val (b.val[2]).val (b.val[3]).val (b.val[4]).val (b.val[5]).val
      r0.factor.val r1.factor.val r2.factor.val r3.factor.val r4.factor.val r5.factor.val
      (value r0.limbs) (value r1.limbs) (value r2.limbs) (value r3.limbs) (value r4.limbs) (value r5.limbs)
      (by simpa only [Nat.zero_add] using r0_post) r1_post r2_post r3_post r4_post r5_post
    have hb : value b = (b.val[0]).val + B * (b.val[1]).val + B ^ 2 * (b.val[2]).val +
        B ^ 3 * (b.val[3]).val + B ^ 4 * (b.val[4]).val + B ^ 5 * (b.val[5]).val := by
      simp [value, Array.getElem!_Nat_eq]
    rw [← hb] at heq
    rw [Nat.mul_mod_mod, heq]
    simp [Nat.add_mod, Nat.mul_mod]

theorem r_constant : value CurveG1.montgomery.R = B ^ 6 % Fp.modulus := by
  simp [value, CurveG1.montgomery.R, B, Fp.modulus]

theorem r2_constant : value CurveG1.montgomery.R2 = B ^ 12 % Fp.modulus := by
  simp [value, CurveG1.montgomery.R2, B, Fp.modulus]

def rInverse : Nat :=
  0x14fec701e8fb0ce9ed5e64273c4f538b1797ab1458a88de9343ea97914956dc87fe11274d898fafbf4d38259380b4820

theorem radix_inverse : (B ^ 6 * rInverse) % Fp.modulus = 1 := by decide +kernel

theorem cancel_radix (x y : Nat) (h : (B ^ 6 * x) % Fp.modulus = y % Fp.modulus) :
    x % Fp.modulus = (y * rInverse) % Fp.modulus := by
  calc
    x % Fp.modulus = ((B ^ 6 * rInverse) * x) % Fp.modulus := by
      rw [Nat.mul_mod, radix_inverse]
      simp
    _ = ((B ^ 6 * x) * rInverse) % Fp.modulus := by congr 1; ring
    _ = ((B ^ 6 * x) % Fp.modulus * rInverse) % Fp.modulus := by simp
    _ = (y % Fp.modulus * rInverse) % Fp.modulus := by rw [h]
    _ = (y * rInverse) % Fp.modulus := by simp

/-- Actual extracted multiplication returns canonical raw Montgomery limbs and computes a * b/R mod p. -/
theorem multiply_value (a b : Limbs) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.multiply a b ⦃ out =>
      value out < Fp.modulus ∧ value out = (value a * value b * rInverse) % Fp.modulus ⦄ := by
  apply spec_mono (multiply_spec a b ha)
  rintro out ⟨hv, heq⟩
  exact ⟨hv, by simpa only [Nat.mod_eq_of_lt hv] using cancel_radix _ _ heq⟩

#print axioms mac_spec
#print axioms round_equation
#print axioms round_spec
#print axioms reduce_spec
#print axioms multiply_spec
#print axioms multiply_value
#print axioms radix_inverse
#print axioms r_constant
#print axioms r2_constant
end MontgomeryProof

import GLVGroupProof
import BaseFieldProof

open EthLib.Cryptography.Bls

namespace SourceFieldPower
local instance : CommRing Fp := Fin.instCommRing Fp.modulus

/-- MSB-first field exponentiation with the source leading-zero iterator state. -/
def loopBits (a : Fp) (k bits : Nat) (started : Bool) (acc : Fp) : Fp :=
  match bits with
  | 0 => acc
  | bits+1 =>
    let set := k.testBit bits
    if !started && !set then loopBits a k bits false acc
    else loopBits a k bits true (if set then (acc*acc)*a else acc*acc)

theorem loop_started (a : Fp) (k bits : Nat) (acc : Fp) :
    loopBits a k bits true acc = acc^(2^bits) * a^(k % 2^bits) := by
  induction bits generalizing acc with
  | zero => simp only [loopBits, pow_zero, pow_one, Nat.mod_one, mul_one]
  | succ bits ih =>
    cases hs : k.testBit bits
    all_goals simp only [loopBits, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, hs]
    all_goals rw [ih, GLVGroup.low_bits_succ]
    all_goals simp only [hs, Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul,
      add_zero, Nat.pow_succ, pow_mul, pow_add, mul_pow, pow_two]
    all_goals ring

theorem loop_initial (a : Fp) (k bits : Nat) :
    loopBits a k bits false 1 = a^(k % 2^bits) := by
  induction bits with
  | zero => simp only [loopBits, pow_zero, Nat.mod_one]
  | succ bits ih =>
    cases hs : k.testBit bits
    all_goals simp only [loopBits, Bool.not_false, Bool.true_and, hs, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    · rw [ih, GLVGroup.low_bits_succ]
      simp only [hs, Bool.toNat_false, zero_mul, add_zero]
    · rw [loop_started, GLVGroup.low_bits_succ]
      simp only [hs, Bool.toNat_true, one_mul, mul_one, pow_add, mul_comm]

open FieldProof

theorem exponent_word (e : Limbs) (w : Nat) (hw : w < 6) :
    value e / B^w % B = e.val[w]!.val := by
  interval_cases w
  all_goals simp [value, B]
  all_goals scalar_tac

theorem exponent_testBit (e : Limbs) (i : Nat) (hi : i < 384) :
    (value e).testBit i = (e.val[i / 64]!.val).testBit (i % 64) := by
  have hw : i / 64 < 6 := by omega
  have ho : i % 64 < 64 := Nat.mod_lt i (by decide)
  have h := congrArg (fun n : Nat => n.testBit (i % 64)) (exponent_word e (i / 64) hw)
  rw [show B^(i / 64) = 2^(64*(i / 64)) by simp [B, pow_mul]] at h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at h
  simp only [show i % 64 < 64 from ho, decide_true, Bool.true_and] at h
  convert h using 1; congr 1; omega

#print axioms exponent_word
#print axioms exponent_testBit
#print axioms loop_started
#print axioms loop_initial
end SourceFieldPower

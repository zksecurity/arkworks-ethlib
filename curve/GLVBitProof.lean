import GLVReductionProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteCurve

namespace ConcreteGLV

theorem scalar_word (k : Scalar) (w : Nat) (hw : w < 4) :
    scalarValue k / B^w % B = k.val[w]!.val := by
  interval_cases w
  all_goals simp [scalarValue, B]
  all_goals scalar_tac

theorem scalar_testBit (k : Scalar) (i : Nat) (hi : i < 256) :
    (scalarValue k).testBit i = (k.val[i / 64]!.val).testBit (i % 64) := by
  have hw : i / 64 < 4 := by omega
  have ho : i % 64 < 64 := Nat.mod_lt i (by decide)
  have h := congrArg (fun n : Nat => n.testBit (i % 64)) (scalar_word k (i / 64) hw)
  rw [show B^(i / 64) = 2^(64*(i / 64)) by simp [B, pow_mul]] at h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at h
  simp only [show i % 64 < 64 from ho, decide_true, Bool.true_and] at h
  convert h using 1; congr 1; omega

@[step] theorem scalar_bit_spec (k : Scalar) (index : U32) (hi : index.val < 256) :
    CurveG1.glv.scalar_bit k index ⦃ out => out = (scalarValue k).testBit index.val ⦄ := by
  have hw : index.val / 64 < k.val.length := by simp; omega
  unfold CurveG1.glv.scalar_bit
  step*
  all_goals rw [scalar_testBit k index.val hi]
  all_goals simp_all [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, UScalar.eq_equiv]

#print axioms scalar_word
#print axioms scalar_testBit
#print axioms scalar_bit_spec

end ConcreteGLV

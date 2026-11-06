import CyclotomicSquareRefinement

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteExtension

namespace ConcreteCyclotomicExponent

/-- The source accumulator starts at the precomputed multiplicative identity. -/
@[step] theorem one_spec :
    CurveG1.pairing.Fp12.cyclotomic_one ⦃ r =>
      Valid12 r ∧ decode12 r = Fp12.one ⦄ := by
  unfold CurveG1.pairing.Fp12.cyclotomic_one
  step*
  all_goals simp_all [Valid12, Valid6, Valid2, decode12, decode6, decode2,
    Fp12.one, Fp6.one, Fp6.zero, Fp2.one, Fp2.zero]
  constructor
  · unfold FieldProof.Valid
    decide +kernel
  · decide +kernel

/-- The fixed digit at a given little-endian position. -/
def digitAt (bit : Nat) : I8 :=
  CurveG1.pairing.BLS_X_NAF.val[bit]!

/-- Pure source schedule, without any assumption that its inputs are cyclotomic. -/
def digits (base inverse acc : Fp12) (remaining : Nat) (found : Bool) : Fp12 :=
  match remaining with
  | 0 => acc
  | bit+1 =>
    let digit := digitAt bit
    let squared := if found then CyclotomicSquare.square acc else acc
    let next := if digit.val > 0 then squared*base
                else if digit.val < 0 then squared*inverse else squared
    digits base inverse next bit (found || (digit != 0#i8))

attribute [local step] ConcreteCyclotomicSquare.source_spec

/-- Every extracted loop operation follows the pure fixed-NAF schedule. -/
@[step] theorem digits_spec (base inverse acc : Raw12) (remaining : U32) (found : Bool)
    (hb : Valid12 base) (hi : Valid12 inverse) (ha : Valid12 acc)
    (hn : remaining.val ≤ 65) :
    CurveG1.pairing.cyclotomic_x_digits base inverse acc remaining found ⦃ r =>
      Valid12 r ∧ decode12 r = digits (decode12 base) (decode12 inverse)
        (decode12 acc) remaining.val found ⦄ := by
  rw [CurveG1.pairing.cyclotomic_x_digits]
  cases found <;> step*
  all_goals (try (split <;> step*))
  all_goals (try (split <;> step*))
  all_goals simp_all [digits]
  all_goals
    have hidx : remaining.val-1 < CurveG1.pairing.BLS_X_NAF.val.length := by simp; omega
    conv_rhs => rw [show remaining.val = (remaining.val-1)+1 by omega, digits]
    simp only [digitAt, _root_.getElem!_pos CurveG1.pairing.BLS_X_NAF.val (remaining.val-1) hidx]
    simp_all
    all_goals (split_ifs <;> (try simp_all) <;> omega)
termination_by remaining.val
decreasing_by all_goals scalar_tac

/-- Source behavior, including zero's early return and the initial identity accumulator. -/
def sourceAbs (a : Fp12) : Fp12 :=
  if a.c0.isZero && a.c1.isZero then a
  else digits a a.conjugate Fp12.one 65 false

/-- The extracted absolute-parameter helper terminates and follows the source schedule. -/
@[step] theorem absolute_source_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.cyclotomic_exp_x_abs a ⦃ r =>
      Valid12 r ∧ decode12 r = sourceAbs (decode12 a) ⦄ := by
  unfold CurveG1.pairing.Fp12.cyclotomic_exp_x_abs
  step*
  all_goals simp_all [sourceAbs]

/-- The signed wrapper applies conjugation after the same checked NAF loop. -/
@[step] theorem signed_source_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.exp_by_x a ⦃ r =>
      Valid12 r ∧ decode12 r = (sourceAbs (decode12 a)).conjugate ⦄ := by
  unfold CurveG1.pairing.Fp12.exp_by_x
  step*

#print axioms one_spec
#print axioms digits_spec
#print axioms absolute_source_spec
#print axioms signed_source_spec
end ConcreteCyclotomicExponent

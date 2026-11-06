import MontgomeryConversionProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof MontgomeryProof

namespace MontgomerySquare

abbrev Wide := Aeneas.Std.Array U64 12#usize

def wideValue (a : Wide) : Nat :=
  a[0]!.val +
  B^1 * a[1]!.val +
  B^2 * a[2]!.val +
  B^3 * a[3]!.val +
  B^4 * a[4]!.val +
  B^5 * a[5]!.val +
  B^6 * a[6]!.val +
  B^7 * a[7]!.val +
  B^8 * a[8]!.val +
  B^9 * a[9]!.val +
  B^10 * a[10]!.val +
  B^11 * a[11]!.val

theorem wide_bound (a : Wide) : wideValue a < B^12 := by
  unfold wideValue B
  scalar_tac

/-- Squaring's diagonal and reduction additions accept arbitrary word carries. -/
theorem adc_word_spec (a b carry : U64) :
    CurveG1.field.adc a b carry ⦃ out =>
      out.1.val + B * out.2.val = a.val + b.val + carry.val ∧ out.2.val ≤ 2 ⦄ := by
  unfold CurveG1.field.adc
  step*
  all_goals (simp only [B, Nat.shiftRight_eq_div_pow] at *; scalar_tac)

def crossValue (a : Limbs) : Nat :=
  B^1 * (a[0]!.val * a[1]!.val) +
  B^2 * (a[0]!.val * a[2]!.val) +
  B^3 * (a[0]!.val * a[3]!.val) +
  B^4 * (a[0]!.val * a[4]!.val) +
  B^5 * (a[0]!.val * a[5]!.val) +
  B^3 * (a[1]!.val * a[2]!.val) +
  B^4 * (a[1]!.val * a[3]!.val) +
  B^5 * (a[1]!.val * a[4]!.val) +
  B^6 * (a[1]!.val * a[5]!.val) +
  B^5 * (a[2]!.val * a[3]!.val) +
  B^6 * (a[2]!.val * a[4]!.val) +
  B^7 * (a[2]!.val * a[5]!.val) +
  B^7 * (a[3]!.val * a[4]!.val) +
  B^8 * (a[3]!.val * a[5]!.val) +
  B^9 * (a[4]!.val * a[5]!.val)

@[step] theorem square_cross_spec (a : Limbs) :
    CurveG1.montgomery.square_cross a ⦃ out =>
      wideValue out = crossValue a ∧ out[0]! = 0#u64 ∧ out[11]! = 0#u64 ⦄ := by
  unfold CurveG1.montgomery.square_cross
  step*
  all_goals simp_all [wideValue, crossValue, B, Aeneas.Std.Array.set,
    Array.getElem!_Nat_eq]
  all_goals omega

private theorem or_carry (x y : U64) :
    ((x.val * 2) % B ||| (y.val / 2^63)) = (x.val * 2) % B + y.val / 2^63 := by
  have hx : x.val < B := by unfold B; scalar_tac
  have hy : y.val < B := by unfold B; scalar_tac
  have hd : y.val / 2^63 < 2^1 := by unfold B at hy; omega
  have hm : (x.val * 2) % B = (x.val % 2^63) * 2 := by unfold B at *; omega
  rw [hm]
  change ((x.val % 2^63) * 2 ||| y.val / 2^63) =
    (x.val % 2^63) * 2 + y.val / 2^63
  rw [Nat.mul_comm (x.val % 2^63) 2]
  exact (Nat.two_pow_add_eq_or_of_lt hd (x.val % 2^63)).symm

def doubledValue (r : Wide) : Nat :=
  B * ((r[1]!.val * 2) % B) +
  B^2 * (((r[2]!.val * 2) % B) ||| (r[1]!.val / 2^63)) +
  B^3 * (((r[3]!.val * 2) % B) ||| (r[2]!.val / 2^63)) +
  B^4 * (((r[4]!.val * 2) % B) ||| (r[3]!.val / 2^63)) +
  B^5 * (((r[5]!.val * 2) % B) ||| (r[4]!.val / 2^63)) +
  B^6 * (((r[6]!.val * 2) % B) ||| (r[5]!.val / 2^63)) +
  B^7 * (((r[7]!.val * 2) % B) ||| (r[6]!.val / 2^63)) +
  B^8 * (((r[8]!.val * 2) % B) ||| (r[7]!.val / 2^63)) +
  B^9 * (((r[9]!.val * 2) % B) ||| (r[8]!.val / 2^63)) +
  B^10 * (((r[10]!.val * 2) % B) ||| (r[9]!.val / 2^63)) +
  B^11 * (r[10]!.val / 2^63)

private theorem doubling_value (r : Wide) (h0 : r[0]! = 0#u64) (h11 : r[11]! = 0#u64) :
    doubledValue r = 2 * wideValue r := by
  have hor2 := or_carry r[2]! r[1]!
  have hor3 := or_carry r[3]! r[2]!
  have hor4 := or_carry r[4]! r[3]!
  have hor5 := or_carry r[5]! r[4]!
  have hor6 := or_carry r[6]! r[5]!
  have hor7 := or_carry r[7]! r[6]!
  have hor8 := or_carry r[8]! r[7]!
  have hor9 := or_carry r[9]! r[8]!
  have hor10 := or_carry r[10]! r[9]!
  simp_all [doubledValue, wideValue, B]
  scalar_tac

@[step] theorem square_double_spec (r : Wide) (h0 : r[0]! = 0#u64) (h11 : r[11]! = 0#u64) :
    CurveG1.montgomery.square_double r ⦃ out => wideValue out = 2 * wideValue r ⦄ := by
  rw [← doubling_value r h0 h11]
  unfold CurveG1.montgomery.square_double
  step*
  all_goals simp_all [wideValue, doubledValue, Aeneas.Std.Array.set, Array.getElem!_Nat_eq,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, U64.size, U64.numBits, B]

def diagonalValue (a : Limbs) : Nat :=
  B^0 * (a[0]!.val * a[0]!.val) +
  B^2 * (a[1]!.val * a[1]!.val) +
  B^4 * (a[2]!.val * a[2]!.val) +
  B^6 * (a[3]!.val * a[3]!.val) +
  B^8 * (a[4]!.val * a[4]!.val) +
  B^10 * (a[5]!.val * a[5]!.val)

private theorem adc_zero_spec (a carry : U64) :
    CurveG1.field.adc a 0#u64 carry ⦃ out =>
      out.1.val + B * out.2.val = a.val + carry.val ∧ out.2.val ≤ 1 ⦄ := by
  apply spec_mono (adc_word_spec a 0#u64 carry)
  rintro out ⟨heq, _⟩
  simp only [UScalar.ofNatCore_val_eq, Nat.add_zero] at heq
  refine ⟨heq, ?_⟩
  unfold B at *
  scalar_tac

attribute [local step] adc_zero_spec

@[step] theorem square_diagonal_spec (a : Limbs) (r : Wide) :
    CurveG1.montgomery.square_diagonal a r ⦃ out =>
      wideValue out.limbs + B^12 * out.carry.val = wideValue r + diagonalValue a ∧ out.carry.val ≤ 1 ⦄ := by
  unfold CurveG1.montgomery.square_diagonal
  step*
  all_goals simp_all [wideValue, diagonalValue, B, Aeneas.Std.Array.set, Array.getElem!_Nat_eq]
  all_goals omega


theorem square_identity (a : Limbs) :
    2 * crossValue a + diagonalValue a = (value a)^2 := by
  unfold crossValue diagonalValue value
  ring

theorem product_no_overflow (a : Limbs) (out : CurveG1.montgomery.SquareDiagonal)
    (heq : wideValue out.limbs + B^12 * out.carry.val = 2 * crossValue a + diagonalValue a) :
    wideValue out.limbs = (value a)^2 ∧ out.carry = 0#u64 := by
  rw [square_identity] at heq
  have hsmall : (value a)^2 < B^12 := by
    have hp : (B^6)^2 = B^12 := (Nat.pow_mul B 6 2).symm
    rw [← hp]
    exact Nat.pow_lt_pow_left (value_bound a) (by decide : 2 ≠ 0)
  have hc : out.carry.val = 0 := by
    by_contra h
    have hcpos : 1 ≤ out.carry.val := by omega
    have hm := Nat.mul_le_mul_left (B^12) hcpos
    simp only [Nat.mul_one] at hm
    omega
  constructor
  · simpa only [hc, Nat.mul_zero, Nat.add_zero] using heq
  · apply UScalar.eq_of_val_eq
    exact hc

/-- The exact three-phase prefix of the extracted square, before Montgomery reduction. -/
def squareProduct (a : Limbs) : Result CurveG1.montgomery.SquareDiagonal := do
  let cross ← CurveG1.montgomery.square_cross a
  let doubled ← CurveG1.montgomery.square_double cross
  CurveG1.montgomery.square_diagonal a doubled

theorem square_product_spec (a : Limbs) :
    squareProduct a ⦃ out => wideValue out.limbs = (value a)^2 ∧ out.carry = 0#u64 ⦄ := by
  unfold squareProduct
  step*
  apply product_no_overflow a
  simp_all

#print axioms square_product_spec

#print axioms square_identity
#print axioms product_no_overflow

#print axioms square_diagonal_spec
#print axioms square_double_spec

#print axioms square_cross_spec

#print axioms wide_bound
#print axioms adc_word_spec
end MontgomerySquare

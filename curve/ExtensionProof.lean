import EncodingProof
import ExtensionAlignmentProof
import Fp2FieldProof
import EthLib.Cryptography.Bls.Fp12
import EthLib.Cryptography.Bls.G2

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteField ConcreteEncoding

namespace ConcreteExtension

abbrev Raw2 := CurveG1.pairing.Fp2
abbrev Raw6 := CurveG1.pairing.Fp6
abbrev Raw12 := CurveG1.pairing.Fp12

def Valid2 (a : Raw2) : Prop := FieldProof.Valid a.c0 ∧ FieldProof.Valid a.c1
def decode2 (a : Raw2) : Fp2 := ⟨decode a.c0, decode a.c1⟩
def Valid6 (a : Raw6) : Prop := Valid2 a.c0 ∧ Valid2 a.c1 ∧ Valid2 a.c2
def decode6 (a : Raw6) : Fp6 := ⟨decode2 a.c0, decode2 a.c1, decode2 a.c2⟩
def Valid12 (a : Raw12) : Prop := Valid6 a.c0 ∧ Valid6 a.c1
def decode12 (a : Raw12) : Fp12 := ⟨decode6 a.c0, decode6 a.c1⟩

@[simp] private theorem fp_zero : Fp.ofNat 0 = Fp.zero := rfl
@[simp] private theorem fp_one : Fp.ofNat 1 = Fp.one := rfl

@[step] theorem fp2_of_fp_spec (a : Raw) (ha : FieldProof.Valid a) :
    CurveG1.pairing.Fp2.of_fp a ⦃ r => Valid2 r ∧ decode2 r = Fp2.ofFp (decode a) ⦄ := by
  unfold CurveG1.pairing.Fp2.of_fp
  step*
  all_goals simp_all [Valid2, decode2, Fp2.ofFp]

@[step] theorem fp2_zero_spec :
    CurveG1.pairing.Fp2.zero  ⦃ r => Valid2 r ∧ decode2 r = Fp2.zero ⦄ := by
  unfold CurveG1.pairing.Fp2.zero
  step*
  all_goals simp_all [Valid2, decode2, Fp2.zero, Fp2.ofFp]

@[step] theorem fp2_one_spec :
    CurveG1.pairing.Fp2.one  ⦃ r => Valid2 r ∧ decode2 r = Fp2.one ⦄ := by
  unfold CurveG1.pairing.Fp2.one
  step*
  all_goals simp_all [Valid2, decode2, Fp2.one, Fp2.ofFp]

@[step] theorem fp2_plus_spec (a b : Raw2) (ha : Valid2 a) (hb : Valid2 b) :
    CurveG1.pairing.Fp2.plus a b ⦃ r => Valid2 r ∧ decode2 r = decode2 a + decode2 b ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp2.plus
  step*
  all_goals simp_all [Valid2, decode2]
  all_goals rfl

@[step] theorem fp2_minus_spec (a b : Raw2) (ha : Valid2 a) (hb : Valid2 b) :
    CurveG1.pairing.Fp2.minus a b ⦃ r => Valid2 r ∧ decode2 r = decode2 a - decode2 b ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp2.minus
  step*
  all_goals simp_all [Valid2, decode2]
  all_goals rfl

@[step] theorem fp2_negative_spec (a : Raw2) (ha : Valid2 a) :
    CurveG1.pairing.Fp2.negative a ⦃ r => Valid2 r ∧ decode2 r = -decode2 a ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp2.negative
  step*
  all_goals simp_all [Valid2, decode2]
  all_goals rfl

/-- The source scalar path uses exactly two base-field products. -/
@[step] theorem fp2_mul_by_fp_spec (a : Raw2) (b : Raw) (ha : Valid2 a) (hb : FieldProof.Valid b) :
    CurveG1.pairing.Fp2.mul_by_fp a b ⦃ r =>
      Valid2 r ∧ decode2 r = decode2 a * Fp2.ofFp (decode b) ⦄ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  rcases ha with ⟨ha0,ha1⟩
  unfold CurveG1.pairing.Fp2.mul_by_fp
  step*
  all_goals simp_all [Valid2, decode2, Fp2.ofFp]
  all_goals congr 1 <;> simp only [show Fp.zero = (0 : Fp) from rfl, mul_zero, sub_zero, zero_add]

@[step] theorem fp2_times_spec (a b : Raw2) (ha : Valid2 a) (hb : Valid2 b) :
    CurveG1.pairing.Fp2.times a b ⦃ r => Valid2 r ∧ decode2 r = decode2 a * decode2 b ⦄ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp2.times
  step*
  all_goals simp_all [Valid2, decode2]
  all_goals
    congr 1
    ring

@[step] theorem fp2_square_spec (a : Raw2) (ha : Valid2 a) :
    CurveG1.pairing.Fp2.square a ⦃ r => Valid2 r ∧ decode2 r = decode2 a * decode2 a ⦄ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp2.square
  step*
  all_goals simp_all [Valid2, decode2]
  all_goals congr 1 <;> ring

private theorem fp2_frobenius_coefficient (i : Nat) (hi : i < 2) :
    FieldProof.Valid ((CurveG1.field.FROBENIUS_FP2_C1.val)[i]'(by simpa using hi)) ∧
    decode ((CurveG1.field.FROBENIUS_FP2_C1.val)[i]'(by simpa using hi)) =
      (if i = 0 then (1 : Fp) else -1) := by
  have he : i = 0 ∨ i = 1 := by omega
  rcases he with h | h
  all_goals subst i
  all_goals constructor
  all_goals first | (unfold FieldProof.Valid; decide +kernel +revert) | decide +kernel +revert

/-- Source-scheduled Frobenius computes the corresponding modulus power. -/
@[step] theorem fp2_frobenius_spec (a : Raw2) (power : Usize) (ha : Valid2 a) :
    CurveG1.pairing.Fp2.frobenius a power ⦃ r =>
      Valid2 r ∧ decode2 r = Fp2.powNat (decode2 a) (Fp.modulus^power.val) ⦄ := by
  rcases ha with ⟨ha0,ha1⟩
  unfold CurveG1.pairing.Fp2.frobenius
  step*
  all_goals have hcoeff := fp2_frobenius_coefficient i.val (by omega)
  all_goals rw [←coefficient_post] at hcoeff
  · exact hcoeff.1
  · rw [QuadraticField.pow_modulus_pow]
    let _ : CommRing Fp := Fin.instCommRing Fp.modulus
    by_cases he : power.val%2 = 0
    all_goals simp_all [Valid2, decode2, Fp2.conjugate]

@[step] theorem fp2_mul_xi_spec (a : Raw2) (ha : Valid2 a) :
    CurveG1.pairing.Fp2.mul_xi a ⦃ r => Valid2 r ∧ decode2 r = Fp2.mulByOnePlusI (decode2 a) ⦄ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp2.mul_xi
  step*
  all_goals simp_all [Valid2, decode2, Fp2.mulByOnePlusI]
  all_goals exact add_comm _ _


@[step] theorem fp2_equal_spec (a b : Raw2) (ha : Valid2 a) (hb : Valid2 b) :
    CurveG1.pairing.Fp2.equal a b ⦃ r => r = Fp2.beq (decode2 a) (decode2 b) ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp2.equal
  step*
  all_goals simp_all [decode2, Fp2.beq]

@[step] theorem fp2_is_zero_spec (a : Raw2) (ha : Valid2 a) :
    CurveG1.pairing.Fp2.is_zero a ⦃ r => r = Fp2.isZero (decode2 a) ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp2.is_zero
  step*
  all_goals simp_all [decode2, Fp2.isZero]

@[step] theorem fp2_inverse_spec (a : Raw2) (ha : Valid2 a) :
    CurveG1.pairing.Fp2.inverse a ⦃ r => Valid2 r ∧ decode2 r = Fp2.inverse (decode2 a) ⦄ := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp2.inverse
  step*
  all_goals simp_all [Valid2, decode2, Fp2.inverse, Fp2.isZero, Fp.isZero]
  all_goals simp [Fp2.zero, Fp.zero, add_comm]

@[step] theorem fp6_of_fp2_spec (a : Raw2) (ha : Valid2 a) :
    CurveG1.pairing.Fp6.of_fp2 a ⦃ r => Valid6 r ∧ decode6 r = Fp6.ofFp2 (decode2 a) ⦄ := by
  unfold CurveG1.pairing.Fp6.of_fp2
  step*
  all_goals simp_all [Valid6, decode6, Fp6.ofFp2]

@[step] theorem fp6_zero_spec :
    CurveG1.pairing.Fp6.zero  ⦃ r => Valid6 r ∧ decode6 r = Fp6.zero ⦄ := by
  unfold CurveG1.pairing.Fp6.zero
  step*
  all_goals simp_all [Valid6, decode6, Fp6.zero]

@[step] theorem fp6_one_spec :
    CurveG1.pairing.Fp6.one  ⦃ r => Valid6 r ∧ decode6 r = Fp6.one ⦄ := by
  unfold CurveG1.pairing.Fp6.one
  step*
  all_goals simp_all [Valid6, decode6, Fp6.one, Fp6.ofFp2]

@[step] theorem fp6_plus_spec (a b : Raw6) (ha : Valid6 a) (hb : Valid6 b) :
    CurveG1.pairing.Fp6.plus a b ⦃ r => Valid6 r ∧ decode6 r = decode6 a + decode6 b ⦄ := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  unfold CurveG1.pairing.Fp6.plus
  step*
  all_goals simp_all [Valid6, decode6]
  all_goals rfl

@[step] theorem fp6_minus_spec (a b : Raw6) (ha : Valid6 a) (hb : Valid6 b) :
    CurveG1.pairing.Fp6.minus a b ⦃ r => Valid6 r ∧ decode6 r = decode6 a - decode6 b ⦄ := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  unfold CurveG1.pairing.Fp6.minus
  step*
  all_goals simp_all [Valid6, decode6]
  all_goals rfl

@[step] theorem fp6_negative_spec (a : Raw6) (ha : Valid6 a) :
    CurveG1.pairing.Fp6.negative a ⦃ r => Valid6 r ∧ decode6 r = -decode6 a ⦄ := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  unfold CurveG1.pairing.Fp6.negative
  step*
  all_goals simp_all [Valid6, decode6]
  all_goals rfl

@[step] theorem fp6_times_spec (a b : Raw6) (ha : Valid6 a) (hb : Valid6 b) :
    CurveG1.pairing.Fp6.times a b ⦃ r => Valid6 r ∧ decode6 r = decode6 a * decode6 b ⦄ := by
  rw [← ExtensionAlignment.cubic_product]
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  unfold CurveG1.pairing.Fp6.times
  step*
  all_goals simp_all [Valid6, decode6, ExtensionAlignment.cubicProduct]

@[step] theorem fp6_square_spec (a : Raw6) (ha : Valid6 a) :
    CurveG1.pairing.Fp6.square a ⦃ r => Valid6 r ∧ decode6 r = decode6 a*decode6 a ⦄ := by
  rw [← ExtensionAlignment.cubic_square]
  rcases ha with ⟨ha0,ha1,ha2⟩
  unfold CurveG1.pairing.Fp6.square
  step*
  all_goals simp_all [Valid6, decode6, ExtensionAlignment.cubicSquare]

@[step] theorem fp6_mul_by_1_spec (a : Raw6) (c1 : Raw2) (ha : Valid6 a) (hc1 : Valid2 c1) :
    CurveG1.pairing.Fp6.mul_by_1 a c1 ⦃ r => Valid6 r ∧
      decode6 r = decode6 a*⟨Fp2.zero,decode2 c1,Fp2.zero⟩ ⦄ := by
  rw [←ExtensionAlignment.cubic_sparse_one]
  rcases ha with ⟨ha0,ha1,ha2⟩
  unfold CurveG1.pairing.Fp6.mul_by_1
  step*
  all_goals simp_all [Valid6, decode6, ExtensionAlignment.cubicSparseOne]

@[step] theorem fp6_mul_by_01_spec (a : Raw6) (c0 c1 : Raw2)
    (ha : Valid6 a) (hc0 : Valid2 c0) (hc1 : Valid2 c1) :
    CurveG1.pairing.Fp6.mul_by_01 a c0 c1 ⦃ r => Valid6 r ∧
      decode6 r = decode6 a*⟨decode2 c0,decode2 c1,Fp2.zero⟩ ⦄ := by
  rw [←ExtensionAlignment.cubic_sparse_pair]
  rcases ha with ⟨ha0,ha1,ha2⟩
  unfold CurveG1.pairing.Fp6.mul_by_01
  step*
  all_goals simp_all [Valid6, decode6, ExtensionAlignment.cubicSparsePair]

@[step] theorem fp6_mul_v_spec (a : Raw6) (ha : Valid6 a) :
    CurveG1.pairing.Fp6.mul_v a ⦃ r => Valid6 r ∧ decode6 r = Fp6.mulByV (decode6 a) ⦄ := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  unfold CurveG1.pairing.Fp6.mul_v
  step*
  all_goals simp_all [Valid6, decode6, Fp6.mulByV]


@[step] theorem fp6_equal_spec (a b : Raw6) (ha : Valid6 a) (hb : Valid6 b) :
    CurveG1.pairing.Fp6.equal a b ⦃ r => r = Fp6.beq (decode6 a) (decode6 b) ⦄ := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  unfold CurveG1.pairing.Fp6.equal
  step*
  all_goals simp_all [decode6, Fp6.beq]

@[step] theorem fp6_is_zero_spec (a : Raw6) (ha : Valid6 a) :
    CurveG1.pairing.Fp6.is_zero a ⦃ r => r = Fp6.isZero (decode6 a) ⦄ := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  unfold CurveG1.pairing.Fp6.is_zero
  step*
  all_goals simp_all [decode6, Fp6.isZero]

@[step] theorem fp6_inverse_spec (a : Raw6) (ha : Valid6 a) :
    CurveG1.pairing.Fp6.inverse a ⦃ r => Valid6 r ∧ decode6 r = Fp6.inverse (decode6 a) ⦄ := by
  have ⟨ha0,ha1,ha2⟩ := ha
  unfold CurveG1.pairing.Fp6.inverse
  step*
  · simp_all [ExtensionAlignment.cubic_is_zero, ExtensionAlignment.cubic_inverse_zero, Valid6]
  · rw [← ExtensionAlignment.cubic_inverse_core]
    simp_all [Valid6, decode6, ExtensionAlignment.cubicInverseCore]

@[step] theorem fp12_of_fp2_spec (a : Raw2) (ha : Valid2 a) :
    CurveG1.pairing.Fp12.of_fp2 a ⦃ r => Valid12 r ∧ decode12 r = ⟨Fp6.ofFp2 (decode2 a), Fp6.zero⟩ ⦄ := by
  unfold CurveG1.pairing.Fp12.of_fp2
  step*
  all_goals simp_all [Valid12, decode12]

@[step] theorem fp12_zero_spec :
    CurveG1.pairing.Fp12.zero  ⦃ r => Valid12 r ∧ decode12 r = Fp12.zero ⦄ := by
  unfold CurveG1.pairing.Fp12.zero
  step*
  all_goals simp_all [Valid12, decode12, Fp12.zero]

@[step] theorem fp12_one_spec :
    CurveG1.pairing.Fp12.one  ⦃ r => Valid12 r ∧ decode12 r = Fp12.one ⦄ := by
  unfold CurveG1.pairing.Fp12.one
  step*
  all_goals simp_all [Valid12, decode12, Fp12.one]

@[step] theorem fp12_plus_spec (a b : Raw12) (ha : Valid12 a) (hb : Valid12 b) :
    CurveG1.pairing.Fp12.plus a b ⦃ r => Valid12 r ∧ decode12 r = decode12 a + decode12 b ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp12.plus
  step*
  all_goals simp_all [Valid12, decode12]
  all_goals rfl

@[step] theorem fp12_minus_spec (a b : Raw12) (ha : Valid12 a) (hb : Valid12 b) :
    CurveG1.pairing.Fp12.minus a b ⦃ r => Valid12 r ∧ decode12 r = decode12 a - decode12 b ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp12.minus
  step*
  all_goals simp_all [Valid12, decode12]
  all_goals rfl

@[step] theorem fp12_negative_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.negative a ⦃ r => Valid12 r ∧ decode12 r = -decode12 a ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp12.negative
  step*
  all_goals simp_all [Valid12, decode12]
  all_goals rfl

@[step] theorem fp12_times_spec (a b : Raw12) (ha : Valid12 a) (hb : Valid12 b) :
    CurveG1.pairing.Fp12.times a b ⦃ r => Valid12 r ∧ decode12 r = decode12 a * decode12 b ⦄ := by
  rw [← ExtensionAlignment.quadratic_product]
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp12.times
  step*
  all_goals simp_all [Valid12, decode12, ExtensionAlignment.quadraticProduct]

@[step] theorem fp12_square_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.square a ⦃ r => Valid12 r ∧ decode12 r = decode12 a*decode12 a ⦄ := by
  rw [← ExtensionAlignment.quadratic_square]
  rcases ha with ⟨ha0,ha1⟩
  unfold CurveG1.pairing.Fp12.square
  step*
  all_goals simp_all [Valid12, decode12, ExtensionAlignment.quadraticSquare]

@[step] theorem fp12_mul_by_014_spec (a : Raw12) (c0 c1 c4 : Raw2)
    (ha : Valid12 a) (hc0 : Valid2 c0) (hc1 : Valid2 c1) (hc4 : Valid2 c4) :
    CurveG1.pairing.Fp12.mul_by_014 a c0 c1 c4 ⦃ r => Valid12 r ∧
      decode12 r = decode12 a*ExtensionAlignment.sparseElement014 (decode2 c0) (decode2 c1) (decode2 c4) ⦄ := by
  rw [←ExtensionAlignment.quadratic_sparse014]
  rcases ha with ⟨ha0,ha1⟩
  unfold CurveG1.pairing.Fp12.mul_by_014
  step*
  all_goals simp_all [Valid12, decode12, ExtensionAlignment.quadraticSparse014,
    ExtensionAlignment.cubic_sparse_one, ExtensionAlignment.cubic_sparse_pair]

@[step] theorem fp12_is_zero_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.is_zero a ⦃ r =>
      r = ((decode12 a).c0.isZero && (decode12 a).c1.isZero) ⦄ := by
  rcases ha with ⟨ha0,ha1⟩
  unfold CurveG1.pairing.Fp12.is_zero
  step*
  all_goals simp_all [decode12]

@[step] theorem fp12_inverse_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.inverse a ⦃ r => Valid12 r ∧ decode12 r = Fp12.inverse (decode12 a) ⦄ := by
  have ⟨ha0,ha1⟩ := ha
  unfold CurveG1.pairing.Fp12.inverse
  step*
  · have hzero : decode12 a = Fp12.zero := by
      cases h : decode12 a
      simp_all [ExtensionAlignment.cubic_is_zero, Fp12.zero]
    simp_all [ExtensionAlignment.quadratic_inverse_zero, Valid12]
  · simp_all [Valid12, decode12, Fp12.inverse]

@[step] theorem fp12_conjugate_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.conjugate a ⦃ r => Valid12 r ∧ decode12 r = Fp12.conjugate (decode12 a) ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp12.conjugate
  step*
  all_goals simp_all [Valid12, decode12, Fp12.conjugate]


@[step] theorem fp12_equal_spec (a b : Raw12) (ha : Valid12 a) (hb : Valid12 b) :
    CurveG1.pairing.Fp12.equal a b ⦃ r => r = Fp12.beq (decode12 a) (decode12 b) ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  unfold CurveG1.pairing.Fp12.equal
  step*
  all_goals simp_all [decode12, Fp12.beq]

@[step] theorem fp12_is_one_spec (a : Raw12) (ha : Valid12 a) :
    CurveG1.pairing.Fp12.is_one a ⦃ r => r = Fp12.isOne (decode12 a) ⦄ := by
  rcases ha with ⟨ha0, ha1⟩
  unfold CurveG1.pairing.Fp12.is_one
  step*
  all_goals simp_all [decode12, Fp12.isOne]

abbrev RawG2 := CurveG1.pairing.G2

def ValidG2 (p : RawG2) : Prop := Valid2 p.x ∧ Valid2 p.y ∧ Valid2 p.z
def decodeG2 (p : RawG2) : G2 := ⟨decode2 p.x, decode2 p.y, decode2 p.z⟩

#print axioms fp2_of_fp_spec
#print axioms fp2_zero_spec
#print axioms fp2_one_spec
#print axioms fp2_plus_spec
#print axioms fp2_minus_spec
#print axioms fp2_negative_spec
#print axioms fp2_mul_by_fp_spec
#print axioms fp2_times_spec
#print axioms fp2_square_spec
#print axioms fp2_inverse_spec
#print axioms fp2_frobenius_spec
#print axioms fp2_mul_xi_spec
#print axioms fp2_equal_spec
#print axioms fp2_is_zero_spec
#print axioms fp6_of_fp2_spec
#print axioms fp6_zero_spec
#print axioms fp6_one_spec
#print axioms fp6_plus_spec
#print axioms fp6_minus_spec
#print axioms fp6_negative_spec
#print axioms fp6_times_spec
#print axioms fp6_square_spec
#print axioms fp6_mul_by_1_spec
#print axioms fp6_mul_by_01_spec
#print axioms fp6_inverse_spec
#print axioms fp6_mul_v_spec
#print axioms fp6_equal_spec
#print axioms fp6_is_zero_spec
#print axioms fp12_of_fp2_spec
#print axioms fp12_zero_spec
#print axioms fp12_one_spec
#print axioms fp12_plus_spec
#print axioms fp12_minus_spec
#print axioms fp12_negative_spec
#print axioms fp12_times_spec
#print axioms fp12_square_spec
#print axioms fp12_mul_by_014_spec
#print axioms fp12_is_zero_spec
#print axioms fp12_inverse_spec
#print axioms fp12_conjugate_spec
#print axioms fp12_equal_spec
#print axioms fp12_is_one_spec

end ConcreteExtension

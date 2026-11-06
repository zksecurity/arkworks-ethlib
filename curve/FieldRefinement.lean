import FieldProof
import Mathlib.Data.ZMod.Defs

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof

namespace ConcreteField

abbrev Raw := CurveG1.field.Fp

def decode (a : Raw) : Fp := Fp.ofNat (value a.limbs * MontgomeryProof.rInverse)

/-- The numeric view is explicit so downstream curve proofs retain abstract field values. -/
theorem decode_val (a : Raw) :
    (decode a).val = (value a.limbs * MontgomeryProof.rInverse) % Fp.modulus := by
  rfl

theorem ofNat_mod (n : Nat) : Fp.ofNat (n % Fp.modulus) = Fp.ofNat n := by
  apply Fin.ext
  simp [Fp.ofNat]

theorem ofNat_add (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b := by
  apply Fin.ext
  simp [Fp.ofNat, Fin.val_add, Nat.add_mod]

theorem ofNat_mul (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b := by
  apply Fin.ext
  simp [Fp.ofNat, Fin.val_mul, Nat.mul_mod]

attribute [local simp] ofNat_mod ofNat_add ofNat_mul

theorem decoded_residue (a : Raw) (ha : Valid a) :
    ((decode a).val * B^6) % Fp.modulus = value a.limbs := by
  rw [decode_val]
  rw [Nat.mod_mul_mod]
  calc
    (value a.limbs * MontgomeryProof.rInverse * B^6) % Fp.modulus =
        (value a.limbs * B^6 * MontgomeryProof.rInverse) % Fp.modulus := by
          rw [Nat.mul_assoc, Nat.mul_comm MontgomeryProof.rInverse (B^6), ← Nat.mul_assoc]
    _ = value a.limbs % Fp.modulus := MontgomeryConversion.radix_shift _
    _ = value a.limbs := Nat.mod_eq_of_lt ha

theorem decode_injective (a b : Raw) (ha : Valid a) (hb : Valid b) :
    decode a = decode b ↔ value a.limbs = value b.limbs := by
  constructor
  · intro h
    rw [← decoded_residue a ha, ← decoded_residue b hb, h]
  · intro h
    simp [decode, h]

theorem ofNat_modulus : Fp.ofNat Fp.modulus = 0 := by
  apply Fin.ext
  simp [Fp.ofNat]

theorem ofNat_sub (a b : Nat) (hb : b ≤ a) :
    Fp.ofNat (a - b) = Fp.ofNat a - Fp.ofNat b := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  apply eq_sub_iff_add_eq.mpr
  rw [← ofNat_add, Nat.sub_add_cancel hb]

@[step] theorem constant_spec (n : U32) :
    CurveG1.field.Fp.Insts.Curve_g1Field.constant n ⦃ r =>
      Valid r ∧ decode r = Fp.ofNat n.val ⦄ := by
  apply spec_mono (FieldProof.constant_spec n)
  rintro r ⟨hr, hv⟩
  refine ⟨hr, ?_⟩
  apply Fin.ext
  simpa [decode, hv, Fp.ofNat, Nat.mul_mod] using MontgomeryConversion.radix_shift n.val

@[step] theorem plus_spec (a b : Raw) (ha : Valid a) (hb : Valid b) :
    CurveG1.field.Fp.Insts.Curve_g1Field.plus a b ⦃ r =>
      Valid r ∧ decode r = decode a + decode b ⦄ := by
  apply spec_mono (FieldProof.plus_spec a b ha hb)
  rintro r ⟨hr, hv⟩
  refine ⟨hr, ?_⟩
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  simp only [decode, hv, ofNat_mul, ofNat_mod, ofNat_add]
  ring

@[step] theorem minus_spec (a b : Raw) (ha : Valid a) (hb : Valid b) :
    CurveG1.field.Fp.Insts.Curve_g1Field.minus a b ⦃ r =>
      Valid r ∧ decode r = decode a - decode b ⦄ := by
  apply spec_mono (FieldProof.minus_spec a b ha hb)
  rintro r ⟨hr, hv⟩
  refine ⟨hr, ?_⟩
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hle : value b.limbs ≤ value a.limbs + Fp.modulus := by unfold Valid at hb; omega
  simp only [decode, hv, ofNat_mul, ofNat_mod, ofNat_sub _ _ hle, ofNat_add, ofNat_modulus]
  ring

@[step] theorem times_spec (a b : Raw) (ha : Valid a) (_hb : Valid b) :
    CurveG1.field.Fp.Insts.Curve_g1Field.times a b ⦃ r =>
      Valid r ∧ decode r = decode a * decode b ⦄ := by
  apply spec_mono (FieldProof.times_spec a b ha)
  rintro r ⟨hr, hv⟩
  refine ⟨hr, ?_⟩
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  simp only [decode, hv, ofNat_mul, ofNat_mod]
  ring

@[step] theorem square_spec (a : Raw) (ha : Valid a) :
    CurveG1.field.Fp.Insts.Curve_g1Field.square a ⦃ r =>
      Valid r ∧ decode r = decode a * decode a ⦄ := by
  apply spec_mono (FieldProof.square_spec a ha)
  rintro r ⟨hr, hv⟩
  refine ⟨hr, ?_⟩
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  simp only [decode, hv, Nat.pow_two, ofNat_mul, ofNat_mod]
  ring

@[step] theorem sum_products_spec (a b c d : Raw)
    (ha : Valid a) (hb : Valid b) (hc : Valid c) (hd : Valid d) :
    CurveG1.field.Fp.Insts.Curve_g1Field.sum_products a b c d ⦃ r =>
      Valid r ∧ decode r = decode a*decode b+decode c*decode d ⦄ := by
  apply spec_mono (FieldProof.sum_products_spec a b c d ha hb hc hd)
  rintro r ⟨hr, hv⟩
  refine ⟨hr, ?_⟩
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  simp only [decode, hv, ofNat_mul, ofNat_mod, ofNat_add]
  ring

@[step] theorem negative_spec (a : Raw) (ha : Valid a) :
    CurveG1.field.Fp.Insts.Curve_g1Field.negative a ⦃ r =>
      Valid r ∧ decode r = -decode a ⦄ := by
  apply spec_mono (FieldProof.negative_spec a ha)
  rintro r ⟨hr, hv⟩
  refine ⟨hr, ?_⟩
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hle : value a.limbs ≤ Fp.modulus := Nat.le_of_lt ha
  simp only [decode, hv, ofNat_mul, ofNat_mod, ofNat_sub _ _ hle, ofNat_modulus]
  ring

@[step] theorem equal_spec (a b : Raw) (ha : Valid a) (hb : Valid b) :
    CurveG1.field.Fp.Insts.Curve_g1Field.equal a b ⦃ r =>
      r = Fp.beq (decode a) (decode b) ⦄ := by
  apply spec_mono (FieldProof.equal_spec a b)
  intro r hr
  rw [hr]
  apply Bool.eq_iff_iff.mpr
  simpa only [Fp.beq, decide_eq_true_eq, beq_iff_eq, ← Fin.ext_iff] using
    (decode_injective a b ha hb).symm

@[step] theorem is_zero_spec (a : Raw) (ha : Valid a) :
    CurveG1.field.Fp.Insts.Curve_g1Field.is_zero a ⦃ r =>
      r = Fp.isZero (decode a) ⦄ := by
  apply spec_mono (FieldProof.is_zero_spec a)
  intro r hr
  rw [hr]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Fp.isZero, beq_iff_eq]
  constructor
  · intro h
    simp [decode_val, h]
  · intro h
    rw [← decoded_residue a ha, h]
    simp

/-- The public constructor accepts exactly the canonical limb representations. -/
theorem from_limbs_correct (a : Limbs) :
    CurveG1.field.Fp.from_limbs a ⦃ r =>
      match r with
      | some f => decode f = Fp.ofNat (value a) ∧ Valid f
      | none => Fp.modulus ≤ value a ⦄ := by
  unfold CurveG1.field.Fp.from_limbs
  step*
  all_goals simp_all only [Valid, decode]
  all_goals simp_all
  rw [← ofNat_mul, ← ofNat_mul]
  apply Fin.ext
  exact MontgomeryConversion.radix_shift (value a)

/-- The precomputed identity supports source normalization without conversion products. -/
theorem montgomery_one :
    FieldProof.Valid (CurveG1.field.FROBENIUS_FP2_C1.val[0]'(by simp)) ∧
    ConcreteField.decode (CurveG1.field.FROBENIUS_FP2_C1.val[0]'(by simp)) = Fp.one := by
  constructor
  · unfold FieldProof.Valid
    decide +kernel
  · decide +kernel

#print axioms montgomery_one
#print axioms plus_spec
#print axioms minus_spec
#print axioms times_spec
#print axioms square_spec
#print axioms sum_products_spec
#print axioms negative_spec
#print axioms equal_spec
#print axioms is_zero_spec
#print axioms constant_spec
#print axioms from_limbs_correct

/-- The source G1 curve coefficient is the canonical Montgomery encoding of four. -/
theorem curve_b_canonical :
    FieldProof.Valid CurveG1.field.G1_COEFF_B ∧ decode CurveG1.field.G1_COEFF_B = Fp.ofNat 4 := by
  constructor
  · unfold FieldProof.Valid
    decide +kernel
  · decide +kernel

#print axioms curve_b_canonical

end ConcreteField

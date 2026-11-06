import FieldRefinement
import BaseFieldProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof

namespace BinaryInverse

@[simp] private theorem low_bit_zero (a : U64) : (a &&& 1#u64 = 0#u64) ↔ a.val % 2 = 0 := by
  simp [UScalar.eq_equiv]

private abbrev OneWords (a : Limbs) : Prop :=
  a[0]! = 1#u64 ∧ a[1]! = 0#u64 ∧ a[2]! = 0#u64 ∧
    a[3]! = 0#u64 ∧ a[4]! = 0#u64 ∧ a[5]! = 0#u64

private theorem one_words_value (a : Limbs) : OneWords a ↔ value a = 1 := by
  unfold OneWords value
  simp only [UScalar.eq_equiv]
  norm_num [B]
  omega

private theorem is_one_words (a : Limbs) :
    CurveG1.field.inversion.is_one a ⦃ r => r = decide (OneWords a) ⦄ := by
  unfold CurveG1.field.inversion.is_one
  step*
  all_goals simp_all [OneWords, Array.getElem!_Nat_eq]

@[step] theorem is_one_spec (a : Limbs) :
    CurveG1.field.inversion.is_one a ⦃ r => r = decide (value a = 1) ⦄ := by
  apply spec_mono (is_one_words a)
  intro r hr
  simpa only [one_words_value] using hr

/-- Modular halving preserves canonical storage and doubles back to its input. -/
@[step] theorem half_coefficient_spec (b : CurveG1.field.Fp) (hb : Valid b) :
    CurveG1.field.inversion.half_coefficient b ⦃ r =>
      Valid r ∧ (2*value r.limbs)%Fp.modulus = value b.limbs ⦄ := by
  unfold Valid at hb
  unfold CurveG1.field.inversion.half_coefficient
  step*
  all_goals simp_all [Valid]
  all_goals norm_num [B, Fp.modulus] at *
  -- Keep parity as an arithmetic fact after normalizing the word operations.
  all_goals have hpar := FieldProof.value_parity b.limbs
  all_goals have hget : b.limbs[0]! = (b.limbs.val)[0] := by simp [Array.getElem!_Nat_eq]
  all_goals rw [hget] at hpar
  all_goals omega

/-- The coefficient update is division by two under Montgomery decoding. -/
@[step] theorem half_coefficient_field_spec (b : CurveG1.field.Fp) (hb : Valid b) :
    CurveG1.field.inversion.half_coefficient b ⦃ r =>
      Valid r ∧ (2 : Fp)*ConcreteField.decode r = ConcreteField.decode b ⦄ := by
  apply spec_mono (half_coefficient_spec b hb)
  rintro r ⟨hr,hv⟩
  refine ⟨hr,?_⟩
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have he := congrArg Fp.ofNat hv
  rw [ConcreteField.ofNat_mod, ConcreteField.ofNat_mul] at he
  have htwo : Fp.ofNat 2 = (2 : Fp) := by decide +kernel
  rw [htwo] at he
  simp only [ConcreteField.decode, ConcreteField.ofNat_mul]
  rw [←mul_assoc,he]

/-- Halving both sides preserves the coefficient equation because two is invertible. -/
private theorem halve_product (a x y : Fp) (n : Nat) (hn : n % 2 = 0)
    (hxy : (2 : Fp)*y = x) (hx : a*x = Fp.ofNat n) :
    a*y = Fp.ofNat (n/2) := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  apply BaseField.double_cancel
  calc
    2*(a*y) = a*(2*y) := by ring
    _ = Fp.ofNat n := by rw [hxy, hx]
    _ = Fp.ofNat (2*(n/2)) := by congr 1; omega
    _ = 2*Fp.ofNat (n/2) := by
      rw [ConcreteField.ofNat_mul]
      congr 1

/-- The normalization loop terminates on positive integers and only removes factors of two. -/
@[step] theorem normalize_spec (u : Limbs) (b : CurveG1.field.Fp)
    (hu : 0 < value u) (hb : Valid b) (a : Fp)
    (ha : a*ConcreteField.decode b = Fp.ofNat (value u)) :
    CurveG1.field.inversion.inverse_loop0_loop0 u b ⦃ r =>
      0 < value r.1 ∧ value r.1 % 2 = 1 ∧ value r.1 ≤ value u ∧
      value r.1 ∣ value u ∧ Valid r.2 ∧
      a*ConcreteField.decode r.2 = Fp.ofNat (value r.1) ⦄ := by
  unfold CurveG1.field.inversion.inverse_loop0_loop0
  apply loop.spec_decr_nat
    (fun s : Limbs × CurveG1.field.Fp => value s.1)
    (fun s => 0 < value s.1 ∧ value s.1 ≤ value u ∧ value s.1 ∣ value u ∧ Valid s.2 ∧
      a*ConcreteField.decode s.2 = Fp.ofNat (value s.1))
  · rintro ⟨v,c⟩ ⟨hv,hle,hdiv,hc,ha⟩
    unfold CurveG1.field.inversion.inverse_loop0_loop0.body
    step*
    all_goals simp_all [Array.getElem!_Nat_eq]
    all_goals have hpar := FieldProof.value_parity v
    all_goals have hget : v[0]! = (v.val)[0] := by simp [Array.getElem!_Nat_eq]
    all_goals rw [hget] at hpar
    have heven : value v % 2 = 0 := by omega
    have hd : value v / 2 ∣ value v := ⟨2, by omega⟩
    exact ⟨by omega, by omega, hd.trans hdiv,
      halve_product a _ _ _ heven b1_post1 ha, by omega⟩
  · exact ⟨hu, le_rfl, dvd_refl _, hb, ha⟩

/-- The second coefficient uses the identical normalization program. -/
@[step] theorem normalize_second_spec (v : Limbs) (c : CurveG1.field.Fp)
    (hv : 0 < value v) (hc : Valid c) (a : Fp)
    (ha : a*ConcreteField.decode c = Fp.ofNat (value v)) :
    CurveG1.field.inversion.inverse_loop0_loop1 v c ⦃ r =>
      0 < value r.1 ∧ value r.1 % 2 = 1 ∧ value r.1 ≤ value v ∧
      value r.1 ∣ value v ∧ Valid r.2 ∧
      a*ConcreteField.decode r.2 = Fp.ofNat (value r.1) ⦄ := by
  exact normalize_spec v c hv hc a ha

private theorem subtract_product (a x y : Fp) (m n : Nat) (hn : n ≤ m)
    (hx : a*x = Fp.ofNat m) (hy : a*y = Fp.ofNat n) :
    a*(x-y) = Fp.ofNat (m-n) := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  rw [mul_sub, hx, hy, ConcreteField.ofNat_sub _ _ hn]

/-- Both integer rows represent the original input times their decoded coefficients. -/
def Invariant (a : Fp) (u v : Limbs) (b c : CurveG1.field.Fp) : Prop :=
  Nat.Coprime (value u) (value v) ∧ Valid b ∧ Valid c ∧
  a*ConcreteField.decode b = Fp.ofNat (value u) ∧
  a*ConcreteField.decode c = Fp.ofNat (value v)

private theorem positive_of_coprime (m n : Nat) (h : Nat.Coprime m n)
    (hn : n ≠ 1) : 0 < m := by
  by_contra hz
  have hm : m = 0 := by omega
  subst m
  exact hn (by simpa using h)

/-- A complete subtraction iteration preserves the two coefficient equations and decreases size. -/
theorem inverse_body_spec (a : Fp) (u v : Limbs) (b c : CurveG1.field.Fp)
    (h : Invariant a u v b c) :
    CurveG1.field.inversion.inverse_loop0.body u v b c ⦃ r =>
      match r with
      | .done (w,d,e) => Valid d ∧ Valid e ∧
          (if value w = 1 then a*ConcreteField.decode d = 1
           else a*ConcreteField.decode e = 1)
      | .cont (w,z,d,e) => Invariant a w z d e ∧
          value w + value z < value u + value v ⦄ := by
  rcases h with ⟨hcop,hb,hc,hab,hac⟩
  unfold CurveG1.field.inversion.inverse_loop0.body
  step*
  all_goals simp_all [show Fp.ofNat 1 = (1 : Fp) from rfl]
  · refine ⟨?_, by omega⟩
    refine ⟨?_, b5_post, v1_post4, ?_, v1_post5⟩
    · rw [u2_post, Nat.coprime_sub_self_left (by omega)]
      exact hcop.of_dvd u1_post3 v1_post3
    · rw [b5_post1, u2_post]
      exact subtract_product a _ _ _ _ (by omega) u1_post5 v1_post5
  · refine ⟨?_, by omega⟩
    refine ⟨?_, u1_post4, c2_post, u1_post5, ?_⟩
    · rw [v2_post, Nat.coprime_sub_self_right (by omega)]
      exact hcop.of_dvd u1_post3 v1_post3
    · rw [c2_post1, v2_post]
      exact subtract_product a _ _ _ _ (by omega) v1_post5 u1_post5

/-- The binary-GCD loop terminates and returns a coefficient whose product with the input is one. -/
@[step] theorem inverse_loop_spec (a : Fp) (u v : Limbs) (b c : CurveG1.field.Fp)
    (h : Invariant a u v b c) :
    CurveG1.field.inversion.inverse_loop0 u v b c ⦃ r =>
      Valid r.2.1 ∧ Valid r.2.2 ∧
      (if value r.1 = 1 then a*ConcreteField.decode r.2.1 = 1
       else a*ConcreteField.decode r.2.2 = 1) ⦄ := by
  unfold CurveG1.field.inversion.inverse_loop0
  apply loop.spec_decr_nat
    (fun s : Limbs × Limbs × CurveG1.field.Fp × CurveG1.field.Fp => value s.1 + value s.2.1)
    (fun s => Invariant a s.1 s.2.1 s.2.2.1 s.2.2.2)
  · rintro ⟨w,z,d,e⟩ hs
    apply spec_mono (inverse_body_spec a w z d e hs)
    intro r hr
    cases r with
    | done y => rcases y with ⟨w,d,e⟩; exact hr
    | cont x => rcases x with ⟨w,z,d,e⟩; exact hr
  · exact h

private theorem initial_invariant (a : CurveG1.field.Fp) (ha : Valid a)
    (hz : 0 < value a.limbs) :
    Invariant (ConcreteField.decode a) a.limbs CurveG1.field.MODULUS
      ⟨CurveG1.montgomery.R2⟩ ⟨Aeneas.Std.Array.repeat 6#usize 0#u64⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [modulus_value]
    exact (Nat.coprime_of_lt_prime (by omega) ha BasePrime.modulus_prime).symm
  · unfold Valid
    decide +kernel
  · unfold Valid
    decide +kernel
  · have hr : ConcreteField.decode ⟨CurveG1.montgomery.R2⟩ = Fp.ofNat (B^6) := by
      decide +kernel
    rw [hr]
    apply Fin.ext
    change ((ConcreteField.decode a).val * (B^6 % Fp.modulus)) % Fp.modulus =
      value a.limbs % Fp.modulus
    rw [Nat.mul_mod_mod, Nat.mod_eq_of_lt ha]
    exact ConcreteField.decoded_residue a ha
  · let _ : CommRing Fp := Fin.instCommRing Fp.modulus
    have hz : ConcreteField.decode ⟨Aeneas.Std.Array.repeat 6#usize 0#u64⟩ = 0 := by
      simp [ConcreteField.decode, zero_value, Fp.ofNat]
    rw [hz, mul_zero, modulus_value, ConcreteField.ofNat_modulus]

/-- The source-specialized binary inverse agrees with EthLib on every canonical input. -/
@[step] theorem inverse_spec (a : CurveG1.field.Fp) (ha : Valid a) :
    CurveG1.field.inversion.inverse a ⦃ r =>
      match r with
      | none => ConcreteField.decode a = 0
      | some b => Valid b ∧ ConcreteField.decode a ≠ 0 ∧
          ConcreteField.decode b = Fp.inverse (ConcreteField.decode a) ⦄ := by
  unfold CurveG1.field.inversion.inverse
  step as ⟨z,hz⟩
  split
  · simp_all [Fp.isZero]
  · have hne : ConcreteField.decode a ≠ 0 := by simp_all [Fp.isZero]
    have hpos : 0 < value a.limbs := by
      by_contra h
      have he : value a.limbs = 0 := by omega
      apply hne
      simp [ConcreteField.decode, he, Fp.ofNat]
    step with inverse_loop_spec (ConcreteField.decode a) a.limbs CurveG1.field.MODULUS
      ⟨CurveG1.montgomery.R2⟩ ⟨Aeneas.Std.Array.repeat 6#usize 0#u64⟩
      (initial_invariant a ha hpos)
    step*
    all_goals simp_all
    all_goals exact BaseField.inverse_unique _ _ hne (by assumption)

#print axioms inverse_spec

#print axioms inverse_loop_spec
#print axioms inverse_body_spec
#print axioms normalize_second_spec
#print axioms normalize_spec
#print axioms half_coefficient_field_spec
#print axioms is_one_spec
#print axioms half_coefficient_spec
end BinaryInverse

namespace ConcreteEncoding
open ConcreteField

@[step] theorem inverse_spec (a : Raw) (ha : Valid a) :
    CurveG1.field.Fp.inverse a ⦃ r => Valid r ∧ decode r = Fp.inverse (decode a) ⦄ := by
  unfold CurveG1.field.Fp.inverse
  step*
  all_goals simp_all [BaseField.inverse_zero]
  · constructor
    · unfold Valid
      rw [zero_value]
      decide +kernel
    · simp [decode, zero_value, Fp.ofNat]

#print axioms inverse_spec
end ConcreteEncoding

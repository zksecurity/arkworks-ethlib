import MontgomerySquareProof
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof MontgomeryProof MontgomerySquare

namespace MontgomerySquareReduction

/-- Low limbs already cancelled by REDC are excluded; the physical array is unchanged there. -/
def suffixValue (r : Wide) (index : Nat) : Nat :=
  (if index ≤ 0 then B^(0 - index) * r[0]!.val else 0) +
  (if index ≤ 1 then B^(1 - index) * r[1]!.val else 0) +
  (if index ≤ 2 then B^(2 - index) * r[2]!.val else 0) +
  (if index ≤ 3 then B^(3 - index) * r[3]!.val else 0) +
  (if index ≤ 4 then B^(4 - index) * r[4]!.val else 0) +
  (if index ≤ 5 then B^(5 - index) * r[5]!.val else 0) +
  (if index ≤ 6 then B^(6 - index) * r[6]!.val else 0) +
  (if index ≤ 7 then B^(7 - index) * r[7]!.val else 0) +
  (if index ≤ 8 then B^(8 - index) * r[8]!.val else 0) +
  (if index ≤ 9 then B^(9 - index) * r[9]!.val else 0) +
  (if index ≤ 10 then B^(10 - index) * r[10]!.val else 0) +
  (if index ≤ 11 then B^(11 - index) * r[11]!.val else 0)

def RoundPost (r : Wide) (index : Nat) (carry : U64)
    (out : CurveG1.montgomery.SquareReductionRound) : Prop :=
  B * suffixValue out.limbs (index + 1) + B^7 * out.carry.val =
    suffixValue r index + out.factor.val * Fp.modulus + B^6 * carry.val ∧
  out.discarded = 0#u64 ∧ out.carry.val ≤ 1

private theorem reduction_0 (r : Wide) (carry2 : U64) (hc : carry2.val ≤ 1) :
    CurveG1.montgomery.square_reduction_round r 0#usize carry2 ⦃ out => RoundPost r 0 carry2 out ⦄ := by
  unfold CurveG1.montgomery.square_reduction_round
  step*
  have hz : discarded = 0#u64 := by
    apply MontgomeryConversion.discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [RoundPost, suffixValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq,
    Aeneas.Std.Array.set, B, Fp.modulus, Nat.mul_add]
  omega
private theorem reduction_1 (r : Wide) (carry2 : U64) (hc : carry2.val ≤ 1) :
    CurveG1.montgomery.square_reduction_round r 1#usize carry2 ⦃ out => RoundPost r 1 carry2 out ⦄ := by
  unfold CurveG1.montgomery.square_reduction_round
  step*
  have hz : discarded = 0#u64 := by
    apply MontgomeryConversion.discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [RoundPost, suffixValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq,
    Aeneas.Std.Array.set, B, Fp.modulus, Nat.mul_add]
  omega
private theorem reduction_2 (r : Wide) (carry2 : U64) (hc : carry2.val ≤ 1) :
    CurveG1.montgomery.square_reduction_round r 2#usize carry2 ⦃ out => RoundPost r 2 carry2 out ⦄ := by
  unfold CurveG1.montgomery.square_reduction_round
  step*
  have hz : discarded = 0#u64 := by
    apply MontgomeryConversion.discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [RoundPost, suffixValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq,
    Aeneas.Std.Array.set, B, Fp.modulus, Nat.mul_add]
  omega
private theorem reduction_3 (r : Wide) (carry2 : U64) (hc : carry2.val ≤ 1) :
    CurveG1.montgomery.square_reduction_round r 3#usize carry2 ⦃ out => RoundPost r 3 carry2 out ⦄ := by
  unfold CurveG1.montgomery.square_reduction_round
  step*
  have hz : discarded = 0#u64 := by
    apply MontgomeryConversion.discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [RoundPost, suffixValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq,
    Aeneas.Std.Array.set, B, Fp.modulus, Nat.mul_add]
  omega
private theorem reduction_4 (r : Wide) (carry2 : U64) (hc : carry2.val ≤ 1) :
    CurveG1.montgomery.square_reduction_round r 4#usize carry2 ⦃ out => RoundPost r 4 carry2 out ⦄ := by
  unfold CurveG1.montgomery.square_reduction_round
  step*
  have hz : discarded = 0#u64 := by
    apply MontgomeryConversion.discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [RoundPost, suffixValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq,
    Aeneas.Std.Array.set, B, Fp.modulus, Nat.mul_add]
  omega
private theorem reduction_5 (r : Wide) (carry2 : U64) (hc : carry2.val ≤ 1) :
    CurveG1.montgomery.square_reduction_round r 5#usize carry2 ⦃ out => RoundPost r 5 carry2 out ⦄ := by
  unfold CurveG1.montgomery.square_reduction_round
  step*
  have hz : discarded = 0#u64 := by
    apply MontgomeryConversion.discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  clear k_post
  simp_all [RoundPost, suffixValue, CurveG1.field.MODULUS, Array.getElem!_Nat_eq,
    Aeneas.Std.Array.set, B, Fp.modulus, Nat.mul_add]
  omega

@[step] theorem reduction_round_spec (r : Wide) (index : Usize) (carry : U64)
    (hi : index.val < 6) (hc : carry.val ≤ 1) :
    CurveG1.montgomery.square_reduction_round r index carry ⦃ out =>
      B * suffixValue out.limbs (index.val + 1) + B^7 * out.carry.val =
        suffixValue r index.val + out.factor.val * Fp.modulus + B^6 * carry.val ∧
      out.discarded = 0#u64 ∧ out.carry.val ≤ 1 ⦄ := by
  interval_cases hindex : index.val
  · have he : index = 0#usize := by scalar_tac
    subst index
    exact reduction_0 r carry hc
  · have he : index = 1#usize := by scalar_tac
    subst index
    exact reduction_1 r carry hc
  · have he : index = 2#usize := by scalar_tac
    subst index
    exact reduction_2 r carry hc
  · have he : index = 3#usize := by scalar_tac
    subst index
    exact reduction_3 r carry hc
  · have he : index = 4#usize := by scalar_tac
    subst index
    exact reduction_4 r carry hc
  · have he : index = 5#usize := by scalar_tac
    subst index
    exact reduction_5 r carry hc

@[simp] theorem suffix_zero (r : Wide) : suffixValue r 0 = wideValue r := by
  simp [suffixValue, wideValue]

def highLimbs (r : Wide) : Limbs :=
  Array.make 6#usize [r[6]!, r[7]!, r[8]!, r[9]!, r[10]!, r[11]!]

@[simp] theorem suffix_six (r : Wide) : suffixValue r 6 = value (highLimbs r) := by
  simp [suffixValue, highLimbs, value]

theorem reduction_telescope (t0 t1 t2 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 k0 k1 k2 k3 k4 k5 : Nat)
    (h0 : B*t1 + B^7*c0 = t0 + k0*Fp.modulus)
    (h1 : B*t2 + B^7*c1 = t1 + k1*Fp.modulus + B^6*c0)
    (h2 : B*t3 + B^7*c2 = t2 + k2*Fp.modulus + B^6*c1)
    (h3 : B*t4 + B^7*c3 = t3 + k3*Fp.modulus + B^6*c2)
    (h4 : B*t5 + B^7*c4 = t4 + k4*Fp.modulus + B^6*c3)
    (h5 : B*t6 + B^7*c5 = t5 + k5*Fp.modulus + B^6*c4)
    : B^6*t6 + B^12*c5 = t0 + Fp.modulus * (k0+B*k1+B^2*k2+B^3*k3+B^4*k4+B^5*k5) := by
  linear_combination h0 + B*h1 + B^2*h2 + B^3*h3 + B^4*h4 + B^5*h5

def factorLimbs (r0 r1 r2 r3 r4 r5 : CurveG1.montgomery.SquareReductionRound) : Limbs :=
  Array.make 6#usize [r0.factor, r1.factor, r2.factor, r3.factor, r4.factor, r5.factor]

theorem factor_value (r0 r1 r2 r3 r4 r5 : CurveG1.montgomery.SquareReductionRound) :
    value (factorLimbs r0 r1 r2 r3 r4 r5) =
      r0.factor.val + B*r1.factor.val + B^2*r2.factor.val + B^3*r3.factor.val +
        B^4*r4.factor.val + B^5*r5.factor.val := by
  simp [factorLimbs, value]

theorem rounds_equation (initial : Wide)
    (r0 r1 r2 r3 r4 r5 : CurveG1.montgomery.SquareReductionRound)
    (h0 : B*suffixValue r0.limbs 1 + B^7*r0.carry.val = wideValue initial + r0.factor.val*Fp.modulus)
    (h1 : B*suffixValue r1.limbs 2 + B^7*r1.carry.val =
      suffixValue r0.limbs 1 + r1.factor.val*Fp.modulus + B^6*r0.carry.val)
    (h2 : B*suffixValue r2.limbs 3 + B^7*r2.carry.val =
      suffixValue r1.limbs 2 + r2.factor.val*Fp.modulus + B^6*r1.carry.val)
    (h3 : B*suffixValue r3.limbs 4 + B^7*r3.carry.val =
      suffixValue r2.limbs 3 + r3.factor.val*Fp.modulus + B^6*r2.carry.val)
    (h4 : B*suffixValue r4.limbs 5 + B^7*r4.carry.val =
      suffixValue r3.limbs 4 + r4.factor.val*Fp.modulus + B^6*r3.carry.val)
    (h5 : B*suffixValue r5.limbs 6 + B^7*r5.carry.val =
      suffixValue r4.limbs 5 + r5.factor.val*Fp.modulus + B^6*r4.carry.val)
    : B^6 * value (highLimbs r5.limbs) + B^12 * r5.carry.val =
      wideValue initial + Fp.modulus * value (factorLimbs r0 r1 r2 r3 r4 r5) := by
  have he := reduction_telescope
    (wideValue initial) (suffixValue r0.limbs 1) (suffixValue r1.limbs 2)
    (suffixValue r2.limbs 3) (suffixValue r3.limbs 4) (suffixValue r4.limbs 5) (suffixValue r5.limbs 6)
    r0.carry.val r1.carry.val r2.carry.val r3.carry.val r4.carry.val r5.carry.val
    r0.factor.val r1.factor.val r2.factor.val r3.factor.val r4.factor.val r5.factor.val
    h0 h1 h2 h3 h4 h5
  rw [suffix_six] at he
  rw [factor_value]
  exact he

theorem reduction_bounds (a q : Nat) (out : Limbs) (carry : U64)
    (ha : a < Fp.modulus) (hq : q < B^6)
    (heq : B^6 * value out + B^12 * carry.val = a^2 + Fp.modulus * q) :
    carry = 0#u64 ∧ value out < 2 * Fp.modulus ∧
      (B^6 * value out) % Fp.modulus = a^2 % Fp.modulus := by
  have hs := Nat.pow_lt_pow_left ha (by decide : 2 ≠ 0)
  have hm := Nat.mul_lt_mul_of_pos_left hq Fp.modulus_pos
  have hc : carry.val = 0 := by
    norm_num [B, Fp.modulus] at heq hs hm
    omega
  have hr : value out < 2 * Fp.modulus := by
    norm_num [B, Fp.modulus, hc] at heq hs hm ⊢
    omega
  refine ⟨UScalar.eq_of_val_eq hc, hr, ?_⟩
  have he : B^6 * value out = a^2 + Fp.modulus * q := by
    simpa only [hc, Nat.mul_zero, Nat.add_zero] using heq
  have h := congrArg (fun n => n % Fp.modulus) he
  simpa [Nat.add_mod, Nat.mul_mod] using h

/-- Six unmodified reduction rounds factored from the generated square body. -/
def sixRoundsWith (round : Wide → Usize → U64 → Result CurveG1.montgomery.SquareReductionRound) (r : Wide) : Result CurveG1.montgomery.SquareReductionRound := do
  let r0 ← round r 0#usize 0#u64
  let r1 ← round r0.limbs 1#usize r0.carry
  let r2 ← round r1.limbs 2#usize r1.carry
  let r3 ← round r2.limbs 3#usize r2.carry
  let r4 ← round r3.limbs 4#usize r3.carry
  round r4.limbs 5#usize r4.carry

/-- Abstract arithmetic parameters keep composition from expanding twelve-limb expressions. -/
private theorem six_rounds_param
    (round : Wide → Usize → U64 → Result CurveG1.montgomery.SquareReductionRound)
    (base modulus : Nat) (measure : Wide → Nat → Nat)
    (post : CurveG1.montgomery.SquareReductionRound → Prop)
    (round_correct : ∀ (r : Wide) (index : Usize) (carry : U64), index.val < 6 → carry.val ≤ 1 →
      round r index carry ⦃ out =>
        base * measure out.limbs (index.val + 1) + base^7 * out.carry.val =
          measure r index.val + out.factor.val * modulus + base^6 * carry.val ∧
        out.discarded = 0#u64 ∧ out.carry.val ≤ 1 ⦄)
    (r : Wide)
    (finish : ∀ (r0 r1 r2 r3 r4 r5 : CurveG1.montgomery.SquareReductionRound),
      base*measure r0.limbs 1 + base^7*r0.carry.val = measure r 0 + r0.factor.val*modulus →
      base*measure r1.limbs 2 + base^7*r1.carry.val = measure r0.limbs 1 + r1.factor.val*modulus + base^6*r0.carry.val →
      base*measure r2.limbs 3 + base^7*r2.carry.val = measure r1.limbs 2 + r2.factor.val*modulus + base^6*r1.carry.val →
      base*measure r3.limbs 4 + base^7*r3.carry.val = measure r2.limbs 3 + r3.factor.val*modulus + base^6*r2.carry.val →
      base*measure r4.limbs 5 + base^7*r4.carry.val = measure r3.limbs 4 + r4.factor.val*modulus + base^6*r3.carry.val →
      base*measure r5.limbs 6 + base^7*r5.carry.val = measure r4.limbs 5 + r5.factor.val*modulus + base^6*r4.carry.val →
      post r5) :
    sixRoundsWith round r ⦃ post ⦄ := by
  unfold sixRoundsWith
  step*
  rename_i out _ _ out_post
  exact finish r0 r1 r2 r3 r4 out
    (by simpa only [Nat.mul_zero, Nat.add_zero] using r0_post)
    r1_post r2_post r3_post r4_post out_post

def sixRounds := sixRoundsWith CurveG1.montgomery.square_reduction_round

@[step] theorem six_rounds_spec (a : Nat) (r : Wide) (ha : a < Fp.modulus)
    (hproduct : wideValue r = a^2) :
    sixRounds r ⦃ out => out.carry = 0#u64 ∧ value (highLimbs out.limbs) < 2*Fp.modulus ∧
      (B^6 * value (highLimbs out.limbs)) % Fp.modulus = a^2 % Fp.modulus ⦄ :=
by
  apply six_rounds_param CurveG1.montgomery.square_reduction_round B Fp.modulus suffixValue
    _ reduction_round_spec r
  intro r0 r1 r2 r3 r4 out h0 h1 h2 h3 h4 h5
  have he := rounds_equation r r0 r1 r2 r3 r4 out
    (by simpa only [suffix_zero] using h0) h1 h2 h3 h4 h5
  rw [hproduct] at he
  exact reduction_bounds a (value (factorLimbs r0 r1 r2 r3 r4 out))
    (highLimbs out.limbs) out.carry ha (value_bound _) he

/-- Copy the high half exactly as the generated Rust routine does. -/
def extractHigh (r : Wide) : Result Limbs := do
  let i ← Array.index_usize r 6#usize
  let i1 ← Array.index_usize r 7#usize
  let i2 ← Array.index_usize r 8#usize
  let i3 ← Array.index_usize r 9#usize
  let i4 ← Array.index_usize r 10#usize
  let i5 ← Array.index_usize r 11#usize
  .ok (Array.make 6#usize [i, i1, i2, i3, i4, i5])

@[step] theorem extract_high_spec (r : Wide) :
    extractHigh r ⦃ out => out = highLimbs r ⦄ := by
  unfold extractHigh
  step*
  simp_all [highLimbs, Array.getElem!_Nat_eq]

def squareTail (r : Wide) : Result Limbs := do
  let last ← sixRounds r
  let hi ← extractHigh last.limbs
  CurveG1.montgomery.reduce hi

@[step] theorem square_tail_spec (a : Nat) (r : Wide) (ha : a < Fp.modulus)
    (hproduct : wideValue r = a^2) :
    squareTail r ⦃ out => value out < Fp.modulus ∧
      (B^6 * value out) % Fp.modulus = a^2 % Fp.modulus ⦄ := by
  unfold squareTail
  step*
  constructor
  · assumption
  · simp_all only [Nat.mul_mod_mod]

/-- Monad associativity factors the extracted body without changing its calls or branches. -/
theorem square_body (a : Limbs) : CurveG1.montgomery.square a =
    (do let product ← squareProduct a; squareTail product.limbs) := by
  simp only [CurveG1.montgomery.square, squareProduct, squareTail, sixRounds,
    sixRoundsWith, extractHigh, Std.bind_assoc, bind_ok]

attribute [local step] square_product_spec

@[step] theorem square_spec (a : Limbs) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.square a ⦃ out => value out < Fp.modulus ∧
      (B^6 * value out) % Fp.modulus = (value a)^2 % Fp.modulus ⦄ := by
  rw [square_body]
  step*

/-- Canonical Montgomery output of the dedicated arkworks square schedule. -/
theorem square_value (a : Limbs) (ha : value a < Fp.modulus) :
    CurveG1.montgomery.square a ⦃ out => value out < Fp.modulus ∧
      value out = ((value a)^2 * rInverse) % Fp.modulus ⦄ := by
  apply spec_mono (square_spec a ha)
  rintro out ⟨hv, heq⟩
  exact ⟨hv, by simpa only [Nat.mod_eq_of_lt hv] using cancel_radix _ _ heq⟩

#print axioms square_value
#print axioms square_body
#print axioms square_tail_spec
#print axioms extract_high_spec

#print axioms six_rounds_spec
#print axioms reduction_bounds

#print axioms reduction_telescope

#print axioms reduction_round_spec
end MontgomerySquareReduction

import MontgomerySquareProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof MontgomeryProof MontgomerySquare

namespace MontgomeryFused

attribute [local step] adc_word_spec

/-- One source-order product accumulation, retaining both high carry words. -/
@[step] theorem accumulate_spec (a r : Limbs) (digit carry_a carry_b : U64) :
    CurveG1.montgomery.accumulate_product a digit r carry_a carry_b ⦃ out =>
      value out.limbs + B^6 * out.carry_a.val + B^7 * out.carry_b.val =
        value r + digit.val * value a + B^6 * (carry_a.val + carry_b.val) ∧
      out.carry_a.val + B*out.carry_b.val ≤ carry_a.val + carry_b.val + a[5]!.val + 1 ⦄ := by
  unfold CurveG1.montgomery.accumulate_product
  step*
  all_goals simp_all [value, Array.getElem!_Nat_eq, B, Nat.mul_add, Nat.mul_left_comm]
  all_goals omega

theorem top_bound (a : Limbs) (ha : value a < Fp.modulus) :
    a[5]!.val ≤ 0x1a0111ea397fe69a := by
  unfold value B Fp.modulus at ha
  scalar_tac

@[step] theorem round_equation (b d r : Limbs) (a_digit c_digit : U64)
    (hb : value b < Fp.modulus) (hd : value d < Fp.modulus) :
    CurveG1.montgomery.sum_product_round b a_digit d c_digit r ⦃ out =>
      B * value out.limbs = value r + a_digit.val * value b + c_digit.val * value d +
        out.factor.val * Fp.modulus ∧ out.discarded = 0#u64 ∧ out.overflow = 0#u64 ⦄ := by
  have hbtop := top_bound b hb
  have hdtop := top_bound d hd
  unfold CurveG1.montgomery.sum_product_round
  step*
  have hfirst : first.carry_b.val = 0 := by
    simp only [B] at first_post1
    omega
  have hsecond : second.carry_b.val = 0 := by
    simp only [B] at second_post1 first_post1
    omega
  have hz : discarded = 0#u64 := by
    apply MontgomeryConversion.discarded_zero i carry discarded
    simpa [k_post, i1_post, CurveG1.field.MODULUS, CurveG1.montgomery.INV,
      core.num.U64.wrapping_mul, U64.size, U64.numBits, B] using discarded_post
  have hcarry : carry5.val ≤ 0x1a0111ea397fe69a + 1 := by
    simpa [i11_post, CurveG1.field.MODULUS, Array.getElem!_Nat_eq] using o4_post2
  have hoverflow : overflow.val = 0 := by
    simp only [hsecond, B, Nat.add_zero] at o5_post
    simp only [hfirst, Nat.mul_zero, Nat.add_zero] at first_post1 second_post1
    omega
  have hov : overflow = 0#u64 := UScalar.eq_of_val_eq hoverflow
  clear k_post
  simp_all [value, CurveG1.field.MODULUS, Array.getElem!_Nat_eq, B, Fp.modulus, Nat.mul_add]
  all_goals omega

theorem telescope (b d a0 a1 a2 a3 a4 a5 c0 c1 c2 c3 c4 c5
    k0 k1 k2 k3 k4 k5 r0 r1 r2 r3 r4 r5 : Nat)
    (h0 : B*r0 = a0*b + c0*d + k0*Fp.modulus)
    (h1 : B*r1 = r0 + a1*b + c1*d + k1*Fp.modulus)
    (h2 : B*r2 = r1 + a2*b + c2*d + k2*Fp.modulus)
    (h3 : B*r3 = r2 + a3*b + c3*d + k3*Fp.modulus)
    (h4 : B*r4 = r3 + a4*b + c4*d + k4*Fp.modulus)
    (h5 : B*r5 = r4 + a5*b + c5*d + k5*Fp.modulus) :
    B^6*r5 = (a0+B*a1+B^2*a2+B^3*a3+B^4*a4+B^5*a5)*b +
      (c0+B*c1+B^2*c2+B^3*c3+B^4*c4+B^5*c5)*d +
      Fp.modulus*(k0+B*k1+B^2*k2+B^3*k3+B^4*k4+B^5*k5) := by
  linear_combination h0 + B*h1 + B^2*h2 + B^3*h3 + B^4*h4 + B^5*h5

/-- Two canonical products leave less than 2p after the six reduction steps. -/
theorem final_bound (a b c d q out : Nat)
    (ha : a < Fp.modulus) (hb : b < Fp.modulus)
    (hc : c < Fp.modulus) (hd : d < Fp.modulus) (hq : q < B^6)
    (he : B^6*out = a*b+c*d+Fp.modulus*q) : out < 2*Fp.modulus := by
  have hab : a*b < Fp.modulus*Fp.modulus :=
    lt_of_le_of_lt (Nat.mul_le_mul_right b (Nat.le_of_lt ha))
      (Nat.mul_lt_mul_of_pos_left hb Fp.modulus_pos)
  have hcd : c*d < Fp.modulus*Fp.modulus :=
    lt_of_le_of_lt (Nat.mul_le_mul_right d (Nat.le_of_lt hc))
      (Nat.mul_lt_mul_of_pos_left hd Fp.modulus_pos)
  norm_num [B, Fp.modulus] at he hab hcd hq ⊢
  omega

theorem value_digits (a : Limbs) : value a =
    (a.val[0]).val+B*(a.val[1]).val+B^2*(a.val[2]).val+B^3*(a.val[3]).val+
      B^4*(a.val[4]).val+B^5*(a.val[5]).val := by
  simp [value, Array.getElem!_Nat_eq]

theorem factors_bound (k0 k1 k2 k3 k4 k5 : U64) :
    k0.val+B*k1.val+B^2*k2.val+B^3*k3.val+B^4*k4.val+B^5*k5.val < B^6 := by
  simpa [value] using value_bound (Array.make 6#usize [k0,k1,k2,k3,k4,k5])

theorem rounds_result (a b c d : Limbs)
    (r0 r1 r2 r3 r4 r5 : CurveG1.montgomery.SumProductRound)
    (ha : value a < Fp.modulus) (hb : value b < Fp.modulus)
    (hc : value c < Fp.modulus) (hd : value d < Fp.modulus)
    (h0 : B*value r0.limbs = (a.val[0]).val*value b + (c.val[0]).val*value d + r0.factor.val*Fp.modulus)
    (h1 : B*value r1.limbs = value r0.limbs + (a.val[1]).val*value b + (c.val[1]).val*value d + r1.factor.val*Fp.modulus)
    (h2 : B*value r2.limbs = value r1.limbs + (a.val[2]).val*value b + (c.val[2]).val*value d + r2.factor.val*Fp.modulus)
    (h3 : B*value r3.limbs = value r2.limbs + (a.val[3]).val*value b + (c.val[3]).val*value d + r3.factor.val*Fp.modulus)
    (h4 : B*value r4.limbs = value r3.limbs + (a.val[4]).val*value b + (c.val[4]).val*value d + r4.factor.val*Fp.modulus)
    (h5 : B*value r5.limbs = value r4.limbs + (a.val[5]).val*value b + (c.val[5]).val*value d + r5.factor.val*Fp.modulus)
    : value r5.limbs < 2*Fp.modulus ∧
      (B^6*value r5.limbs)%Fp.modulus = (value a*value b+value c*value d)%Fp.modulus := by
  have he := telescope (value b) (value d)
    (a.val[0]).val (a.val[1]).val (a.val[2]).val (a.val[3]).val (a.val[4]).val (a.val[5]).val
    (c.val[0]).val (c.val[1]).val (c.val[2]).val (c.val[3]).val (c.val[4]).val (c.val[5]).val
    r0.factor.val r1.factor.val r2.factor.val r3.factor.val r4.factor.val r5.factor.val
    (value r0.limbs) (value r1.limbs) (value r2.limbs) (value r3.limbs) (value r4.limbs) (value r5.limbs)
    h0 h1 h2 h3 h4 h5
  rw [← value_digits a, ← value_digits c] at he
  have hq := factors_bound r0.factor r1.factor r2.factor r3.factor r4.factor r5.factor
  refine ⟨final_bound _ _ _ _ _ _ ha hb hc hd hq he, ?_⟩
  rw [he]
  simp [Nat.add_mod, Nat.mul_mod]

@[step] theorem sum_products_spec (a b c d : Limbs)
    (ha : value a < Fp.modulus) (hb : value b < Fp.modulus)
    (hc : value c < Fp.modulus) (hd : value d < Fp.modulus) :
    CurveG1.montgomery.sum_products a b c d ⦃ out => value out < Fp.modulus ∧
      (B^6 * value out) % Fp.modulus = (value a*value b+value c*value d) % Fp.modulus ⦄ := by
  unfold CurveG1.montgomery.sum_products
  step*
  all_goals simp_all only [zero_value]
  all_goals
    have result := rounds_result a b c d r0 r1 r2 r3 r4 r5 ha hb hc hd
      (by simpa only [Nat.zero_add] using r0_post) r1_post r2_post r3_post r4_post r5_post
  · exact result.1
  · exact ⟨True.intro, by simpa only [Nat.mul_mod_mod] using result.2⟩

theorem sum_products_value (a b c d : Limbs)
    (ha : value a < Fp.modulus) (hb : value b < Fp.modulus)
    (hc : value c < Fp.modulus) (hd : value d < Fp.modulus) :
    CurveG1.montgomery.sum_products a b c d ⦃ out => value out < Fp.modulus ∧
      value out = ((value a*value b+value c*value d)*rInverse) % Fp.modulus ⦄ := by
  apply spec_mono (sum_products_spec a b c d ha hb hc hd)
  rintro out ⟨hv, heq⟩
  exact ⟨hv, by simpa only [Nat.mod_eq_of_lt hv] using cancel_radix _ _ heq⟩

#print axioms sum_products_value
#print axioms telescope
#print axioms final_bound
#print axioms round_equation
#print axioms accumulate_spec
end MontgomeryFused

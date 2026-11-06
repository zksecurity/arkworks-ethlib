import AffineScalarProof
import AffinePointModel

open EthLib.Cryptography.Bls

namespace AffineScalarGroup
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing

def baseAction (base : G1) (infinity : Bool) : G1Curve.curve.toAffine.Point :=
  if infinity then 0 else G1Curve.interpret base

private theorem addBase_correct (base res : G1) (infinity : Bool)
    (hb : infinity = true ∨ G1Curve.OnCurve base) (hr : G1Curve.OnCurve res) :
    G1Curve.OnCurve (AffineScalar.addBase base infinity res) ∧
    G1Curve.interpret (AffineScalar.addBase base infinity res) =
      G1Curve.interpret res+baseAction base infinity := by
  cases infinity
  · have hc := hb.resolve_left (by decide)
    exact ⟨G1Curve.add_onCurve res base hr hc, G1Curve.interpret_add res base hr hc⟩
  · simpa [AffineScalar.addBase, baseAction] using hr

/-- Once the leading zeros are past, the accumulator follows the low-bit scalar prefix. -/
theorem loop_started (k bits : Nat) (base res : G1) (infinity : Bool)
    (hb : infinity = true ∨ G1Curve.OnCurve base) (hr : G1Curve.OnCurve res) :
    G1Curve.OnCurve (AffineScalar.loopBits k base infinity bits true res) ∧
    G1Curve.interpret (AffineScalar.loopBits k base infinity bits true res) =
      2^bits • G1Curve.interpret res+(k % 2^bits) • baseAction base infinity := by
  induction bits generalizing res with
  | zero =>
    rw [AffineScalar.loopBits]
    simpa only [↓reduceDIte, pow_zero, Nat.mod_one, one_nsmul, zero_nsmul, add_zero, eq_self, and_true] using hr
  | succ bits ih =>
    have hd := G1Curve.double_onCurve res hr
    have ha := addBase_correct base (G1.double res) infinity hb hd
    cases hs : k.testBit bits
    all_goals rw [AffineScalar.loopBits]
    all_goals simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hs]
    · refine (ih _ hd).imp_right ?_
      intro he
      rw [he, GLVGroup.low_bits_succ]
      simp only [hs, Bool.toNat_false, zero_mul, add_zero, G1Curve.interpret_double res hr,
        Nat.pow_succ, mul_nsmul, nsmul_add, two_nsmul]
    · refine (ih _ ha.1).imp_right ?_
      intro he
      rw [he, ha.2, G1Curve.interpret_double res hr, GLVGroup.low_bits_succ]
      simp only [hs, Bool.toNat_true, one_mul, add_nsmul, Nat.pow_succ, mul_nsmul, nsmul_add, two_nsmul]
      abel

/-- Skipping leading zeros preserves the zero initial accumulator. -/
theorem loop_initial (k bits : Nat) (base : G1) (infinity : Bool)
    (hb : infinity = true ∨ G1Curve.OnCurve base) :
    G1Curve.OnCurve (AffineScalar.loopBits k base infinity bits false G1.zero) ∧
    G1Curve.interpret (AffineScalar.loopBits k base infinity bits false G1.zero) =
      (k % 2^bits) • baseAction base infinity := by
  induction bits with
  | zero =>
    rw [AffineScalar.loopBits]
    simp only [↓reduceDIte, pow_zero, Nat.mod_one, zero_nsmul, G1Curve.interpret_zero]
    exact ⟨Or.inl rfl, trivial⟩
  | succ bits ih =>
    have hz : G1Curve.OnCurve G1.zero := Or.inl rfl
    have hd := G1Curve.double_onCurve G1.zero hz
    have ha := addBase_correct base (G1.double G1.zero) infinity hb hd
    cases hs : k.testBit bits
    all_goals rw [AffineScalar.loopBits]
    all_goals simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel,
      Bool.not_false, Bool.true_and, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · refine ih.imp_right ?_
      intro he
      rw [he, GLVGroup.low_bits_succ]
      simp only [hs, Bool.toNat_false, zero_mul, add_zero]
    · have hm := loop_started k bits base _ infinity hb ha.1
      refine hm.imp_right ?_
      intro he
      rw [he, ha.2, G1Curve.interpret_double G1.zero hz, G1Curve.interpret_zero, GLVGroup.low_bits_succ]
      simp only [hs, Bool.toNat_true, one_mul, zero_add, add_nsmul]
      abel

/-- Full unsigned integer multiplication, without a subgroup assumption or reduction modulo r. -/
theorem mul_affine_correct (x y : Fp) (infinity : Bool) (k : Nat)
    (hk : k < 2^256) (hb : infinity = true ∨ G1Curve.OnCurve ⟨x,y,Fp.one⟩) :
    G1Curve.OnCurve (AffineScalar.mulAffine x y infinity k) ∧
    G1Curve.interpret (AffineScalar.mulAffine x y infinity k) =
      k • baseAction ⟨x,y,Fp.one⟩ infinity := by
  simpa only [AffineScalar.mulAffine, Nat.mod_eq_of_lt hk] using
    loop_initial k 256 ⟨x,y,Fp.one⟩ infinity hb

/-- The source affine schedule and EthLib's integer multiplier represent the same full-curve point. -/
theorem ethlib_mul_equiv (x y : Fp) (infinity : Bool) (k : Nat)
    (hk : k < 2^256) (hb : infinity = true ∨ G1Curve.OnCurve ⟨x,y,Fp.one⟩) :
    G1Curve.interpret (AffineScalar.mulAffine x y infinity k) =
      G1Curve.interpret (G1.mulNat (effectiveBase x y infinity) k) := by
  have hc : G1Curve.OnCurve (effectiveBase x y infinity) := by
    cases infinity
    · exact hb.resolve_left (by decide)
    · exact Or.inl rfl
  have ha : G1Curve.interpret (effectiveBase x y infinity) = baseAction ⟨x,y,Fp.one⟩ infinity := by
    cases infinity
    · rfl
    · exact G1Curve.interpret_zero
  rw [(mul_affine_correct x y infinity k hk hb).2,
    (G1Curve.mulNat_correct _ k hc).2, ha]

open Aeneas Aeneas.Std Aeneas.Std.WP ConcreteCurve ConcreteField

/-- The extracted affine multiplier computes the full unsigned scalar action. -/
theorem mul_affine_spec (base : CurveG1.AffinePoint CurveG1.field.Fp) (k : Scalar)
    (hx : FieldProof.Valid base.x) (hy : FieldProof.Valid base.y)
    (hc : base.infinity = true ∨ G1Curve.OnCurve ⟨decode base.x,decode base.y,Fp.one⟩) :
    CurveG1.scalar.mul_affine base k ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) =
        scalarValue k • baseAction ⟨decode base.x,decode base.y,Fp.one⟩ base.infinity ⦄ := by
  apply spec_mono (ConcreteAffineScalar.mul_affine_spec base k hx hy)
  rintro out ⟨hv, he⟩
  refine ⟨hv, ?_⟩
  rw [he]
  apply mul_affine_correct _ _ _ _ _ hc
  simpa only [FieldProof.B, ← pow_mul] using ConcreteGLV.scalar_bound k

#print axioms loop_started
#print axioms loop_initial
#print axioms mul_affine_correct
#print axioms ethlib_mul_equiv
#print axioms mul_affine_spec
end
end AffineScalarGroup

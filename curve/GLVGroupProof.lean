import G1CurveProof
import GLVLoopProof

open EthLib.Cryptography.Bls

namespace GLVGroup
noncomputable section

/-- Splitting the low bits at their highest bit, in the source scan order. -/
theorem low_bits_succ (k bits : Nat) :
    k % 2^(bits+1) = k % 2^bits + (k.testBit bits).toNat * 2^bits := by
  rw [Nat.toNat_testBit, Nat.pow_succ]
  have hp : 0 < 2^bits := Nat.two_pow_pos bits
  have h1 := Nat.mod_add_div k (2^bits)
  have h2 := Nat.mod_add_div (k / 2^bits) 2
  have h3 := Nat.mod_add_div k (2^bits * 2)
  have hr1 := Nat.mod_lt k hp
  have hr2 := Nat.mod_lt (k / 2^bits) (by omega : 0 < 2)
  have hr3 := Nat.mod_lt k (Nat.mul_pos hp (by omega : 0 < 2))
  have hdiv : k / (2^bits * 2) = k / 2^bits / 2 := (Nat.div_div_eq_div_mul k (2^bits) 2).symm
  rw [hdiv] at h3
  nlinarith

/-- Once the source skip flag clears, the joint scan computes the two group actions. -/
theorem loop_false (k1 k2 bits : Nat) (p q res : G1)
    (hp : G1Curve.OnCurve p) (hq : G1Curve.OnCurve q) (hr : G1Curve.OnCurve res) :
    G1Curve.OnCurve (GLVSchedule.loopBits k1 k2 p q (G1.add p q) bits false res) ∧
    G1Curve.interpret (GLVSchedule.loopBits k1 k2 p q (G1.add p q) bits false res) =
      2^bits • G1Curve.interpret res +
        (k1 % 2^bits) • G1Curve.interpret p + (k2 % 2^bits) • G1Curve.interpret q := by
  induction bits generalizing res with
  | zero =>
    rw [GLVSchedule.loopBits]
    simp only [↓reduceDIte, pow_zero, Nat.mod_one, one_nsmul, zero_nsmul, add_zero]
    exact ⟨hr, trivial⟩
  | succ bits ih =>
    have hd := G1Curve.double_onCurve res hr
    have hpq := G1Curve.add_onCurve p q hp hq
    cases h1 : k1.testBit bits <;> cases h2 : k2.testBit bits
    all_goals rw [GLVSchedule.loopBits]
    all_goals simp only [Nat.succ_ne_zero, ↓reduceDIte,
      Nat.add_sub_cancel, Bool.false_and, Bool.false_eq_true, ↓reduceIte, h1, h2]
    all_goals first
      | refine (ih _ hd).imp_right ?_
      | refine (ih _ (G1Curve.add_onCurve _ _ hd hq)).imp_right ?_
      | refine (ih _ (G1Curve.add_onCurve _ _ hd hp)).imp_right ?_
      | refine (ih _ (G1Curve.add_onCurve _ _ hd hpq)).imp_right ?_
    all_goals intro he
    all_goals rw [he, low_bits_succ k1 bits, low_bits_succ k2 bits]
    all_goals simp only [G1Curve.interpret_add _ _ hd hq,
      G1Curve.interpret_add _ _ hd hp, G1Curve.interpret_add _ _ hd hpq,
      G1Curve.interpret_add p q hp hq, G1Curve.interpret_double res hr,
      h1, h2, Bool.toNat_false, Bool.toNat_true,
      zero_mul, one_mul, add_zero, Nat.pow_succ, mul_nsmul,
      add_nsmul, nsmul_add, two_nsmul]
    all_goals abel

/-- A leading zero pair clears the pinned skip flag before the ordinary joint scan. -/
theorem joint_scan (k1 k2 bits : Nat) (p q : G1)
    (h1 : k1 < 2^bits) (h2 : k2 < 2^bits)
    (hp : G1Curve.OnCurve p) (hq : G1Curve.OnCurve q) :
    G1Curve.OnCurve (GLVSchedule.loopBits k1 k2 p q (G1.add p q) (bits+1) true G1.zero) ∧
    G1Curve.interpret (GLVSchedule.loopBits k1 k2 p q (G1.add p q) (bits+1) true G1.zero) =
      k1 • G1Curve.interpret p + k2 • G1Curve.interpret q := by
  rw [GLVSchedule.loopBits]
  simp only [Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel,
    Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2, Bool.not_false,
    Bool.and_self, ↓reduceIte]
  have hm := loop_false k1 k2 bits p q G1.zero hp hq (Or.inl rfl)
  simpa only [G1Curve.interpret_zero, nsmul_zero, zero_add,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using hm

private theorem endomorphism_x (p : G1) :
    (G1Endomorphism.map p).x = p.x * G1Endomorphism.beta := rfl

private theorem endomorphism_eq (p : G1) :
    G1Endomorphism.map p = ⟨p.x * G1Endomorphism.beta, p.y, p.z⟩ := rfl

private theorem endomorphism_y (p : G1) : (G1Endomorphism.map p).y = p.y := by
  have h := congrArg G1.y (endomorphism_eq p)
  exact h

private theorem endomorphism_z (p : G1) : (G1Endomorphism.map p).z = p.z := by
  have h := congrArg G1.z (endomorphism_eq p)
  exact h

private theorem curve_check_of_coordinates (p q : G1) (hy : q.y = p.y) (hz : q.z = p.z)
    (hx : q.x*q.x*q.x = p.x*p.x*p.x) : ConcreteEncoding.onCurve q = ConcreteEncoding.onCurve p := by
  simp only [ConcreteEncoding.onCurve, G1.isInfinity, hy, hz, hx]
  rfl

private theorem endomorphism_curve_check (p : G1) :
    ConcreteEncoding.onCurve (G1Endomorphism.map p) = ConcreteEncoding.onCurve p := by
  have hx : (G1Endomorphism.map p).x * (G1Endomorphism.map p).x * (G1Endomorphism.map p).x =
      p.x*p.x*p.x := by
    rw [endomorphism_x]
    exact G1Endomorphism.mapped_cube p.x
  exact curve_check_of_coordinates p (G1Endomorphism.map p)
    (endomorphism_y p) (endomorphism_z p) hx

theorem endomorphism_onCurve (p : G1) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (G1Endomorphism.map p) := by
  apply (G1Curve.onCurve_iff _).mp
  rw [endomorphism_curve_check]
  exact (G1Curve.onCurve_iff p).mpr hp

/-- Signed source components act on P and its coordinate endomorphism. -/
theorem mul_decomposed (p : G1) (k1 k2 : Bool × Nat)
    (hp : G1Curve.OnCurve p) (h1 : k1.2 < 2^255) (h2 : k2.2 < 2^255) :
    G1Curve.OnCurve (GLVSchedule.mulDecomposed p k1 k2) ∧
    G1Curve.interpret (GLVSchedule.mulDecomposed p k1 k2) =
      k1.2 • (if k1.1 then G1Curve.interpret p else -G1Curve.interpret p) +
      k2.2 • (if k2.1 then G1Curve.interpret (G1Endomorphism.map p)
        else -G1Curve.interpret (G1Endomorphism.map p)) := by
  have hmap := endomorphism_onCurve p hp
  have hb1 : G1Curve.OnCurve (if k1.1 then p else G1.neg p) := by
    split
    · exact hp
    · exact G1Curve.neg_onCurve p hp
  have hb2 : G1Curve.OnCurve (if k2.1 then G1Endomorphism.map p else G1.neg (G1Endomorphism.map p)) := by
    split
    · exact hmap
    · exact G1Curve.neg_onCurve _ hmap
  have hm := joint_scan k1.2 k2.2 255 _ _ h1 h2 hb1 hb2
  have hi1 : G1Curve.interpret (if k1.1 then p else G1.neg p) =
      (if k1.1 then G1Curve.interpret p else -G1Curve.interpret p) := by
    split
    · rfl
    · exact G1Curve.interpret_neg p hp
  have hi2 : G1Curve.interpret (if k2.1 then G1Endomorphism.map p else G1.neg (G1Endomorphism.map p)) =
      (if k2.1 then G1Curve.interpret (G1Endomorphism.map p)
        else -G1Curve.interpret (G1Endomorphism.map p)) := by
    split
    · rfl
    · exact G1Curve.interpret_neg _ hmap
  rw [hi1, hi2] at hm
  exact hm

private theorem signed_action {G : Type*} [AddCommGroup G] (k : Int) (p : G) :
    (GLVDecomposition.signedMagnitude k).2 •
      (if (GLVDecomposition.signedMagnitude k).1 then p else -p) = k • p := by
  calc
    _ = (if (GLVDecomposition.signedMagnitude k).1
        then ((GLVDecomposition.signedMagnitude k).2 : Int)
        else -((GLVDecomposition.signedMagnitude k).2 : Int)) • p := by
      split_ifs <;> simp only [natCast_zsmul, neg_zsmul, smul_neg]
    _ = k • p := by rw [GLVDecomposition.signed_magnitude_value]

/-- The source model acts by its signed integer components on the two bases. -/
theorem mul_projective_components (p : G1) (k : Nat) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (GLVSchedule.mulProjective p k) ∧
    G1Curve.interpret (GLVSchedule.mulProjective p k) =
      (GLVDecomposition.components (k % Fr.modulus : Int)).1 • G1Curve.interpret p +
      (GLVDecomposition.components (k % Fr.modulus : Int)).2 •
        G1Curve.interpret (G1Endomorphism.map p) := by
  have hk : (k % Fr.modulus : Int) < GLVDecomposition.order := by
    change (k % Fr.modulus : Int) < (Fr.modulus : Int)
    exact_mod_cast Nat.mod_lt k (by decide +kernel : 0 < Fr.modulus)
  have hb := GLVDecomposition.component_bounds (k % Fr.modulus) (by omega) hk
  have hsize : (2^128 : Int) < (2^255 : Nat) := by decide +kernel
  have h1 : (GLVDecomposition.components (k % Fr.modulus : Int)).1.natAbs < 2^255 := by omega
  have h2 : (GLVDecomposition.components (k % Fr.modulus : Int)).2.natAbs < 2^255 := by omega
  have hm := mul_decomposed p
    (GLVDecomposition.signedMagnitude (GLVDecomposition.components (k % Fr.modulus : Int)).1)
    (GLVDecomposition.signedMagnitude (GLVDecomposition.components (k % Fr.modulus : Int)).2) hp h1 h2
  simpa only [GLVSchedule.mulProjective, ConcreteGLV.observeComponents, signed_action] using hm

/-- The only additional curve fact needed for the source multiplier is its eigenvalue relation. -/
theorem mul_projective_correct (p : G1) (k : Nat) (hp : G1Curve.OnCurve p)
    (hr : Fr.modulus • G1Curve.interpret p = 0)
    (he : G1Curve.interpret (G1Endomorphism.map p) =
      GLVDecomposition.eigenvalue • G1Curve.interpret p) :
    G1Curve.OnCurve (GLVSchedule.mulProjective p k) ∧
    G1Curve.interpret (GLVSchedule.mulProjective p k) = k • G1Curve.interpret p := by
  have hm := mul_projective_components p k hp
  refine ⟨hm.1, hm.2.trans ?_⟩
  rw [he]
  have hir : GLVDecomposition.order • G1Curve.interpret p = 0 := by
    simpa only [GLVDecomposition.order, natCast_zsmul] using hr
  rw [GLVDecomposition.group_reconstruction _ _ hir, ← Int.natCast_mod, natCast_zsmul]
  calc
    _ = (k % Fr.modulus + (k / Fr.modulus)*Fr.modulus) • G1Curve.interpret p := by
      rw [add_nsmul, Nat.mul_comm (k / Fr.modulus), mul_nsmul, hr, nsmul_zero, add_zero]
    _ = k • G1Curve.interpret p := by rw [Nat.mul_comm (k / Fr.modulus), Nat.mod_add_div]

#print axioms low_bits_succ
#print axioms loop_false
#print axioms joint_scan
#print axioms endomorphism_onCurve
#print axioms mul_decomposed
#print axioms mul_projective_components
#print axioms mul_projective_correct
end
end GLVGroup

import G1ParameterMultiplicationProof
import G1PointEqualityProof
import G1AffineInterpretationProof

open EthLib.Cryptography.Bls

namespace SourceFastSubgroup
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing

/-- The normalized affine input used by the source subgroup check. -/
def base (p : G1) : G1 :=
  AffineScalarGroup.effectiveBase (G1.toAffine p).1 (G1.toAffine p).2 p.isInfinity

def firstMultiple (p : G1) : G1 :=
  AffineScalar.mulAffine (G1.toAffine p).1 (G1.toAffine p).2 p.isInfinity G1FastSubgroup.parameter

def endomorphismBase (p : G1) : G1 :=
  AffineScalarGroup.effectiveBase ((G1.toAffine p).1*G1Endomorphism.beta)
    (G1.toAffine p).2 p.isInfinity

/-- The pinned early-out followed by the negative squared-parameter endomorphism test. -/
def model (p : G1) : Bool :=
  let q := base p
  let xp := firstMultiple p
  if G1PointEquality.model xp q && !p.isInfinity then false else
    G1PointEquality.model
      (G1.neg (GLVSchedule.mulProjective xp G1FastSubgroup.parameter))
      (endomorphismBase p)

theorem first_correct (p : G1) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (firstMultiple p) ∧
    G1Curve.interpret (firstMultiple p) = G1FastSubgroup.parameter • G1Curve.interpret p := by
  have h := AffineScalarGroup.mul_affine_correct
    (G1.toAffine p).1 (G1.toAffine p).2 p.isInfinity G1FastSubgroup.parameter
    (by decide +kernel) (G1AffineInterpretation.affine_data_onCurve p hp)
  simpa only [firstMultiple, G1AffineInterpretation.baseAction_toAffine p hp] using h

theorem negative_second_correct (p : G1) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (G1.neg (GLVSchedule.mulProjective (firstMultiple p) G1FastSubgroup.parameter)) ∧
    G1Curve.interpret (G1.neg (GLVSchedule.mulProjective (firstMultiple p) G1FastSubgroup.parameter)) =
      -(GLVDecomposition.a • G1Curve.interpret p) := by
  have h := G1ParameterMultiplication.glv_parameter_correct _ (first_correct p hp).1
  refine ⟨G1Curve.neg_onCurve _ h.1, ?_⟩
  rw [G1Curve.interpret_neg _ h.1, h.2, (first_correct p hp).2, ← mul_nsmul]
  have hs : ((G1FastSubgroup.parameter * G1FastSubgroup.parameter : Nat) : Int) =
      GLVDecomposition.a := by
    rw [Nat.cast_mul, ← pow_two, G1FastSubgroup.parameter_square]
  rw [← natCast_zsmul, hs]

theorem endomorphism_correct (p : G1) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (endomorphismBase p) ∧
    G1Curve.interpret (endomorphismBase p) = G1Eigenvalue.hom (G1Curve.interpret p) := by
  have hb := G1AffineInterpretation.normalized_correct p hp
  by_cases hi : p.isInfinity = true
  · have hz := (G1Curve.isZero_iff p.z).mp hi
    simp only [endomorphismBase, AffineScalarGroup.effectiveBase, hi, ↓reduceIte]
    exact ⟨Or.inl rfl, by rw [G1Curve.interpret_zero, G1Curve.interpret_infinity p hz, map_zero]⟩
  · have he : endomorphismBase p = G1Endomorphism.map (base p) := by
      simp only [endomorphismBase, base, AffineScalarGroup.effectiveBase, hi]
      rfl
    rw [he]
    exact ⟨GLVGroup.endomorphism_onCurve _ hb.1,
      (G1Eigenvalue.hom_raw _ hb.1).symm.trans (congrArg G1Eigenvalue.hom hb.2)⟩

/-- The complete source branch structure agrees with the order-r definition on every on-curve input. -/
theorem model_iff (p : G1) (hp : G1Curve.OnCurve p) :
    model p = true ↔ Fr.modulus • G1Curve.interpret p = 0 := by
  have hb := G1AffineInterpretation.normalized_correct p hp
  change G1Curve.OnCurve (base p) ∧ G1Curve.interpret (base p) = G1Curve.interpret p at hb
  have hf := first_correct p hp
  have hn := negative_second_correct p hp
  have hm := endomorphism_correct p hp
  have he : G1PointEquality.model
      (G1.neg (GLVSchedule.mulProjective (firstMultiple p) G1FastSubgroup.parameter))
      (endomorphismBase p) = true ↔ Fr.modulus • G1Curve.interpret p = 0 := by
    rw [G1PointEquality.model_iff _ _ hn.1 hm.1, hn.2, hm.2, eq_comm]
    exact G1FastSubgroup.criterion_iff _
  dsimp only [model]
  split
  · rename_i h
    have hh : G1PointEquality.model (firstMultiple p) (base p) = true ∧ (!p.isInfinity) = true := by
      simpa only [Bool.and_eq_true] using h
    have hx := (G1PointEquality.model_iff _ _ hf.1 hb.1).mp hh.1
    rw [hf.2, hb.2] at hx
    have hi : p.isInfinity = false := by
      cases hi : p.isInfinity
      · rfl
      · have hn := hh.2
        rw [hi] at hn
        exact Bool.noConfusion hn
    constructor
    · intro hfalse; exact Bool.noConfusion hfalse
    · intro hr
      have hz := G1FastSubgroup.early_out_safe _ hr hx
      have hpz := (G1Curve.interpret_eq_zero_iff p hp).mp hz
      have hit := (G1Curve.isZero_iff p.z).mpr hpz
      change p.z.isZero = false at hi
      rw [hit] at hi
      exact Bool.noConfusion hi
  · exact he

theorem ethlib_equiv (p : G1) (hp : G1Curve.OnCurve p) : model p = G1.inSubgroup p := by
  apply Bool.eq_iff_iff.mpr
  exact (model_iff p hp).trans (G1Curve.inSubgroup_iff p hp).symm

#print axioms endomorphism_correct
#print axioms model_iff
#print axioms ethlib_equiv
#print axioms first_correct
#print axioms negative_second_correct
end
end SourceFastSubgroup

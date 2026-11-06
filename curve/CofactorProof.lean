import G1AffineInterpretationProof

open EthLib.Cryptography.Bls

namespace SourceCofactor

def effectiveCofactor : Nat := 15132376222941642753

/-- The source affine multiplication followed by its canonical affine output conversion. -/
def model (p : G1) : G1 :=
  let affine := G1.toAffine p
  let multiple := AffineScalar.mulAffine affine.1 affine.2 p.isInfinity effectiveCofactor
  AffineScalarGroup.effectiveBase (G1.toAffine multiple).1 (G1.toAffine multiple).2 multiple.isInfinity

theorem model_correct (p : G1) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (model p) ∧
    G1Curve.interpret (model p) = G1Curve.interpret (G1.mulNat p effectiveCofactor) := by
  have hm := AffineScalarGroup.mul_affine_correct (G1.toAffine p).1 (G1.toAffine p).2
    p.isInfinity effectiveCofactor (by decide +kernel) (G1AffineInterpretation.affine_data_onCurve p hp)
  have hn := G1AffineInterpretation.normalized_correct _ hm.1
  refine ⟨hn.1, hn.2.trans ?_⟩
  rw [hm.2, G1AffineInterpretation.baseAction_toAffine p hp, (G1Curve.mulNat_correct p effectiveCofactor hp).2]

end SourceCofactor

open Aeneas Aeneas.Std Aeneas.Std.WP
open ConcreteCurve ConcreteField

namespace ConcreteCofactor

@[step] theorem clear_cofactor_projective_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.scalar.clear_cofactor_projective p ⦃ out =>
      ValidPoint out ∧ decodePoint out = SourceCofactor.model (decodePoint p) ⦄ := by
  unfold CurveG1.scalar.clear_cofactor_projective
  step as ⟨base, hx, hy, he, hi⟩
  have hxe := congrArg Prod.fst he
  have hye := congrArg Prod.snd he
  step*
  all_goals simp_all [SourceCofactor.model, SourceCofactor.effectiveCofactor, scalarValue, FieldProof.B]

/-- The live cofactor entry point retains its full-curve mathematical meaning. -/
theorem clear_cofactor_group_spec (p : RawPoint) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.field.clear_cofactor p ⦃ out =>
      ValidPoint out ∧ G1Curve.OnCurve (decodePoint out) ∧
      G1Curve.interpret (decodePoint out) =
        G1Curve.interpret (G1.mulNat (decodePoint p) SourceCofactor.effectiveCofactor) ⦄ := by
  unfold CurveG1.field.clear_cofactor
  apply spec_mono (clear_cofactor_projective_spec p hp)
  rintro out ⟨hv, he⟩
  refine ⟨hv, ?_⟩
  rw [he]
  exact SourceCofactor.model_correct (decodePoint p) hc

#print axioms clear_cofactor_projective_spec
#print axioms clear_cofactor_group_spec
end ConcreteCofactor

#print axioms SourceCofactor.model_correct

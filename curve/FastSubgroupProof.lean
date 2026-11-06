import G1FastSubgroupModelProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls ConcreteField ConcreteCurve

namespace ConcreteFastSubgroup

@[step] theorem points_equal_spec (p q : RawPoint) (hp : ValidPoint p) (hq : ValidPoint q) :
    CurveG1.scalar.points_equal p q ⦃ result =>
      result = G1PointEquality.model (decodePoint p) (decodePoint q) ⦄ := by
  rcases hp with ⟨hx,hy,hz⟩
  rcases hq with ⟨hqx,hqy,hqz⟩
  unfold CurveG1.scalar.points_equal
  step*
  all_goals simp_all [G1PointEquality.model, G1.isInfinity, decodePoint]

@[step] theorem source_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.scalar.in_subgroup p ⦃ result => result = SourceFastSubgroup.model (decodePoint p) ⦄ := by
  unfold CurveG1.scalar.in_subgroup
  step as ⟨affine,hx,hy,he,hi⟩
  have hxe := congrArg Prod.fst he
  have hye := congrArg Prod.snd he
  step*
  all_goals simp_all [SourceFastSubgroup.model, SourceFastSubgroup.base,
    SourceFastSubgroup.firstMultiple, G1FastSubgroup.parameter, scalarValue, FieldProof.B,
    SourceFastSubgroup.endomorphismBase]

/-- The source check agrees with EthLib on the full on-curve domain. -/
theorem ethlib_spec (p : RawPoint) (hp : ValidPoint p) (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.scalar.in_subgroup p ⦃ result => result = G1.inSubgroup (decodePoint p) ⦄ := by
  apply spec_mono (source_spec p hp)
  intro result he
  exact he.trans (SourceFastSubgroup.ethlib_equiv (decodePoint p) hc)

#print axioms ethlib_spec
#print axioms points_equal_spec
#print axioms source_spec
end ConcreteFastSubgroup

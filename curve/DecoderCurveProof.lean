import RecoveryProof

open EthLib.Cryptography.Bls

namespace DecoderCurve
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing

private theorem sqrt_square (a y : Fp) (h : (Fp.sqrt a).toOption = some y) : y*y = a := by
  dsimp only [Fp.sqrt] at h
  split at h
  · rename_i hc
    simp only [Except.toOption, Option.some.injEq] at h
    subst y
    apply Fin.ext
    simpa only [Fp.beq, beq_iff_eq] using hc
  · simp only [Except.toOption, reduceCtorEq] at h

theorem recover_onCurve (x : Fp) (greatest : Bool) (p : G1)
    (h : ConcreteRecovery.recoverSpec x greatest = some p) : G1Curve.OnCurve p := by
  unfold ConcreteRecovery.recoverSpec at h
  cases hs : (Fp.sqrt (x*x*x+Fp.ofNat 4)).toOption with
  | none => simp only [hs, Option.map_none, reduceCtorEq] at h
  | some y =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst p
    apply Or.inr
    rw [G1Curve.equation_iff]
    have hy := sqrt_square _ y hs
    have hfour : Fp.ofNat 4 = (4 : Fp) := by decide +kernel
    have hone : Fp.one = (1 : Fp) := by decide +kernel
    simp only [hone, one_pow, mul_one]
    split
    · simpa only [hfour, pow_succ, pow_zero, one_mul] using hy
    · simpa only [hfour, pow_succ, pow_zero, one_mul, neg_mul_neg] using hy

/-- Every accepted compressed point is on the full curve before the subgroup test runs. -/
theorem uncompress_onCurve (bytes : ByteArray) (p : G1)
    (h : (G1.uncompress bytes).toOption = some p) : G1Curve.OnCurve p := by
  rw [← ConcreteRecovery.uncompress_correct bytes] at h
  unfold ConcreteRecovery.uncompressSpec at h
  split_ifs at h
  · simp only [Option.some.injEq] at h
    subst p
    exact Or.inl rfl
  · cases hx : (Fp.fromBytesBE (bytes.set! 0 (bytes.get! 0 &&& 31))).toOption with
    | none => simp only [hx, Option.bind_none, reduceCtorEq] at h
    | some x =>
      simp only [hx, Option.bind_some] at h
      exact recover_onCurve x _ p h

open Aeneas Aeneas.Std Aeneas.Std.WP ConcreteCurve ConcretePoints ConcreteField

/-- The shared source reconstruction already establishes the equation; no second curve check is needed. -/
theorem from_x_onCurve_spec (x : Raw) (sign : Bool) (hx : FieldProof.Valid x) :
    CurveG1.field.from_x x sign ⦃ result =>
      CanonicalResult result ∧ ∀ p, result = some p → G1Curve.OnCurve (decodePoint p) ⦄ := by
  apply spec_mono (ConcretePoints.from_x_spec x sign hx)
  rintro result ⟨hv, he⟩
  refine ⟨hv, ?_⟩
  intro p hp
  apply recover_onCurve (decode x) sign (decodePoint p)
  change ConcretePoints.fromXSpec (decode x) sign = some (decodePoint p)
  rw [← he, hp]
  rfl

#print axioms from_x_onCurve_spec
#print axioms recover_onCurve
#print axioms uncompress_onCurve
end
end DecoderCurve

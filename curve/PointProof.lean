import EncodingProof
import CofactorProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteField ConcreteCurve ConcreteEncoding

namespace ConcretePoints

@[simp] private theorem one_constant : Fp.ofNat 1 = Fp.one := by decide

/-- Successful constructors return canonical coordinates; failure carries no point. -/
def CanonicalResult (result : Option RawPoint) : Prop :=
  ∀ p, result = some p → ValidPoint p

private theorem sqrt_candidate (a candidate : Fp)
    (hc : candidate = Fp.powNat a ((Fp.modulus + 1) / 4)) :
    (if Fp.beq (candidate * candidate) a then some candidate else none) = (Fp.sqrt a).toOption := by
  subst candidate
  unfold Fp.sqrt
  split <;> simp_all [Fp.beq, Except.toOption]

@[step] theorem sqrt_spec (a : Raw) (ha : FieldProof.Valid a) :
    CurveG1.field.Fp.sqrt a ⦃ result =>
      result.map decode = (Fp.sqrt (decode a)).toOption ∧
      ∀ root, result = some root → FieldProof.Valid root ⦄ := by
  unfold CurveG1.field.Fp.sqrt
  step*
  all_goals
    have he : FieldProof.value (Array.make 6#usize [
        17185665809301629611#u64, 552535377879302143#u64,
        15693976698673184137#u64, 15644892545385841839#u64,
        10576397981472451381#u64, 468449654411884966#u64]) = (Fp.modulus + 1) / 4 := by
      decide +kernel
    rw [he] at candidate_post1
    rw [← sqrt_candidate (decode a) (decode candidate) candidate_post1]
    simp_all


/-- This constructor accepts full-curve points; it does not impose a subgroup. -/
def fromAffineSpec (x y : Fp) : Option G1 :=
  let p : G1 := ⟨x, y, Fp.one⟩
  if onCurve p then some p else none

@[step] theorem from_affine_spec (x y : Raw)
    (hx : FieldProof.Valid x) (hy : FieldProof.Valid y) :
    CurveG1.field.from_affine x y ⦃ result =>
      CanonicalResult result ∧ result.map decodePoint = fromAffineSpec (decode x) (decode y) ⦄ := by
  unfold CurveG1.field.from_affine
  step*
  all_goals simp_all [CanonicalResult, ValidPoint, decodePoint, fromAffineSpec]

/-- The normalization target uses the pinned executable affine conversion. -/
def normalizeSpec (p : G1) : G1 :=
  if p.isInfinity then G1.zero
  else let (x, y) := p.toAffine; ⟨x, y, Fp.one⟩

private theorem normalization_eta (xy : Fp × Fp) (infinity : Bool) :
    AffineScalarGroup.effectiveBase xy.1 xy.2 infinity =
      (if infinity then G1.zero else let (x,y) := xy; (⟨x,y,Fp.one⟩ : G1)) := by
  cases xy
  rfl

@[step] theorem normalize_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.normalize p ⦃ result =>
      ValidPoint result ∧ decodePoint result = normalizeSpec (decodePoint p) ⦄ := by
  unfold CurveG1.field.normalize
  apply spec_mono (ConcreteNormalization.normalize_projective_spec p hp)
  rintro out ⟨hv, he⟩
  refine ⟨hv, he.trans ?_⟩
  exact normalization_eta (G1.toAffine (decodePoint p)) (decodePoint p).isInfinity

/-- Jacobian equality by cross-multiplication, with all z=0 points identified. -/
def pointsEqualSpec (p q : G1) : Bool :=
  if p.isInfinity then q.isInfinity
  else if q.isInfinity then false
  else
    let z1sq := p.z * p.z
    let z2sq := q.z * q.z
    Fp.beq (p.x * z2sq) (q.x * z1sq) &&
      Fp.beq (p.y * (z2sq * q.z)) (q.y * (z1sq * p.z))

@[step] theorem points_equal_spec (p q : RawPoint) (hp : ValidPoint p) (hq : ValidPoint q) :
    CurveG1.field.points_equal p q ⦃ result =>
      result = pointsEqualSpec (decodePoint p) (decodePoint q) ⦄ := by
  simpa only [CurveG1.field.points_equal, pointsEqualSpec, G1PointEquality.model] using
    ConcreteFastSubgroup.points_equal_spec p q hp hq

@[step] theorem compress_checked_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.compress_checked p ⦃ result =>
      result.map observe =
        if validSubgroupPoint (decodePoint p) then some (G1.compress (decodePoint p)) else none ⦄ := by
  unfold CurveG1.field.compress_checked
  step*
  all_goals simp_all

@[step] theorem compress_public_key_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.compress_public_key p ⦃ result =>
      result.map observe =
        if validPublicKeyPoint (decodePoint p) then some (G1.compress (decodePoint p)) else none ⦄ := by
  unfold CurveG1.field.compress_public_key
  step*
  all_goals simp_all

/-- A returned root is checked by multiplication, independent of Fermat completeness. -/
theorem sqrt_sound (a : Raw) (ha : FieldProof.Valid a) :
    CurveG1.field.Fp.sqrt a ⦃ result => ∀ root, result = some root →
      FieldProof.Valid root ∧ decode root * decode root = decode a ⦄ := by
  unfold CurveG1.field.Fp.sqrt
  step*
  all_goals simp_all [Fp.beq]
  apply Fin.ext
  simpa [decode_val a] using b_post

/-- Every successful finite constructor has canonical coordinates and passes the equation. -/
theorem from_affine_on_curve (x y : Raw)
    (hx : FieldProof.Valid x) (hy : FieldProof.Valid y) :
    CurveG1.field.from_affine x y ⦃ result => ∀ p, result = some p →
      ValidPoint p ∧ onCurve (decodePoint p) = true ⦄ := by
  unfold CurveG1.field.from_affine
  step*
  all_goals simp_all [ValidPoint, decodePoint]

/-- Source affine reconstruction, with an explicitly selected lexicographic root. -/
def fromXSpec (x : Fp) (sign : Bool) : Option G1 :=
  (Fp.sqrt (x*x*x+Fp.ofNat 4)).toOption.map fun root =>
    ⟨x, if Fp.signBit root = sign then root else -root, Fp.one⟩

/-- The RFC effective cofactor is used as an integer scalar, without reduction. -/
@[step] theorem clear_cofactor_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.clear_cofactor p ⦃ result =>
      ValidPoint result ∧ decodePoint result = SourceCofactor.model (decodePoint p) ⦄ := by
  unfold CurveG1.field.clear_cofactor
  step*

#print axioms clear_cofactor_spec
#print axioms sqrt_sound
#print axioms from_affine_on_curve
#print axioms sqrt_spec
#print axioms from_affine_spec
#print axioms normalize_spec
#print axioms points_equal_spec
#print axioms compress_checked_spec
#print axioms compress_public_key_spec

end ConcretePoints

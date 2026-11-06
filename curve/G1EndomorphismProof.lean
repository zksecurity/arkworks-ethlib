import ConcreteProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls ConcreteField ConcreteCurve

namespace G1Endomorphism

/-- The coefficient used by the pinned arkworks G1 endomorphism. -/
def beta : Fp :=
  ⟨793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350,
    by decide +kernel⟩

/-- Coordinate map before any subgroup-specific eigenvalue identification. -/
private def coordinateMap (b : Fp) (p : G1) : G1 := ⟨p.x * b, p.y, p.z⟩

def map (p : G1) : G1 := coordinateMap beta p

theorem beta_canonical :
    FieldProof.Valid CurveG1.field.G1_BETA ∧ decode CurveG1.field.G1_BETA = beta := by
  constructor
  · unfold FieldProof.Valid
    decide +kernel
  · decide +kernel

theorem beta_cube : beta ^ 3 = (1 : Fp) := by decide +kernel

theorem beta_ne_one : beta ≠ (1 : Fp) := by decide +kernel

theorem map_three (p : G1) : map (map (map p)) = p := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have h := beta_cube
  have hx : p.x * beta * beta * beta = p.x := by
    calc
      _ = p.x * beta ^ 3 := by ring
      _ = p.x := by rw [h, mul_one]
  cases p
  simp_all only [map, coordinateMap]

/-- Multiplying x by beta preserves the Jacobian equation's cubic term. -/
theorem mapped_cube (x : Fp) : (x * beta) * (x * beta) * (x * beta) = x * x * x := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  calc
    _ = (x * x * x) * beta ^ 3 := by ring
    _ = x * x * x := by rw [beta_cube, mul_one]

private theorem coordinate_equation (b : Fp) (p : G1) (t : Fp)
    (hx : (p.x * b) * (p.x * b) * (p.x * b) = p.x * p.x * p.x)
    (hp : p.y * p.y = p.x * p.x * p.x + t) :
    (coordinateMap b p).y * (coordinateMap b p).y =
      (coordinateMap b p).x * (coordinateMap b p).x * (coordinateMap b p).x + t := by
  exact hp.trans (congrArg (fun u : Fp => u + t) hx).symm

/-- Preserve `y²=x³+t` for every fixed t; the curve uses t=4z⁶, and z is unchanged. -/
theorem equation (p : G1) (t : Fp)
    (hp : p.y * p.y = p.x * p.x * p.x + t) :
    (map p).y * (map p).y = (map p).x * (map p).x * (map p).x + t :=
  coordinate_equation beta p t (mapped_cube p.x) hp

@[step] theorem projective_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.glv.endomorphism p ⦃ r => ValidPoint r ∧ decodePoint r = map (decodePoint p) ⦄ := by
  rcases hp with ⟨hx, hy, hz⟩
  have hb := beta_canonical
  unfold CurveG1.glv.endomorphism
  step*
  all_goals simp_all [ValidPoint, decodePoint, map, coordinateMap]

@[step] theorem affine_spec (p : CurveG1.AffinePoint CurveG1.field.Fp)
    (hx : FieldProof.Valid p.x) (hy : FieldProof.Valid p.y) :
    CurveG1.glv.endomorphism_affine p ⦃ r =>
      FieldProof.Valid r.x ∧ FieldProof.Valid r.y ∧
      decode r.x = decode p.x * beta ∧ r.y = p.y ∧ r.infinity = p.infinity ⦄ := by
  have hb := beta_canonical
  unfold CurveG1.glv.endomorphism_affine
  step*

#print axioms beta_canonical
#print axioms beta_cube
#print axioms beta_ne_one
#print axioms map_three
#print axioms mapped_cube
#print axioms equation
#print axioms projective_spec
#print axioms affine_spec

end G1Endomorphism

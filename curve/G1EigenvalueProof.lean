import G1TorsionProof
import CubicEndomorphismProof

open EthLib.Cryptography.Bls
open WeierstrassCurve

namespace G1Eigenvalue
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing
local instance : (CubicEndomorphism.curve (4 : Fp)).IsElliptic := G1Curve.ellipticStructure

def hom : G1Torsion.Point →+ G1Torsion.Point :=
  CubicEndomorphism.hom (4 : Fp) G1Endomorphism.beta G1Endomorphism.beta_cube

private theorem map_eq (p : G1) :
    G1Endomorphism.map p = ⟨p.x * G1Endomorphism.beta, p.y, p.z⟩ := rfl

private theorem map_x (p : G1) : (G1Endomorphism.map p).x = p.x * G1Endomorphism.beta := by
  have h := congrArg G1.x (map_eq p)
  exact h

private theorem map_y (p : G1) : (G1Endomorphism.map p).y = p.y := by
  have h := congrArg G1.y (map_eq p)
  exact h

private theorem map_z (p : G1) : (G1Endomorphism.map p).z = p.z := by
  have h := congrArg G1.z (map_eq p)
  exact h

/-- The mathematical automorphism is the existing raw-coordinate map on every on-curve input. -/
theorem hom_raw (p : G1) (hp : G1Curve.OnCurve p) :
    hom (G1Curve.interpret p) = G1Curve.interpret (G1Endomorphism.map p) := by
  have hmap := GLVGroup.endomorphism_onCurve p hp
  by_cases hz : p.z = 0
  · rw [G1Curve.interpret_infinity p hz, map_zero,
      G1Curve.interpret_infinity (G1Endomorphism.map p) ((map_z p).trans hz)]
  · have hmz : (G1Endomorphism.map p).z ≠ 0 := by rw [map_z]; exact hz
    change CubicEndomorphism.mapPoint (4 : Fp) G1Endomorphism.beta G1Endomorphism.beta_cube
      (G1Curve.interpret p) = G1Curve.interpret (G1Endomorphism.map p)
    unfold G1Curve.interpret
    rw [Jacobian.Point.toAffine_of_Z_ne_zero (G1Curve.nonsingular_finite p hp hz) hz,
      Jacobian.Point.toAffine_of_Z_ne_zero (G1Curve.nonsingular_finite _ hmap hmz) hmz]
    simp only [CubicEndomorphism.mapPoint, G1Curve.coords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      map_x, map_y, map_z]
    congr 1
    ring

theorem hom_generator : hom (G1Curve.interpret G1.generator) =
    GLVDecomposition.eigenvalue • G1Curve.interpret G1.generator :=
  (hom_raw G1.generator G1Torsion.generator_onCurve).trans G1Torsion.generator_eigenvalue

/-- The fixed-base eigenvalue relation extends to all mathematical r-torsion. -/
theorem hom_torsion (p : G1Torsion.Point) (hp : Fr.modulus • p = 0) :
    hom p = GLVDecomposition.eigenvalue • p := by
  have hm := G1Torsion.torsion_mem_generator p hp
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  rw [← hn, map_zsmul, hom_generator]
  exact smul_comm n GLVDecomposition.eigenvalue (G1Curve.interpret G1.generator)

/-- The source beta is the chosen scalar eigenvalue on the entire G1 subgroup. -/
theorem eigenvalue (p : G1) (hp : G1Curve.OnCurve p)
    (hr : Fr.modulus • G1Curve.interpret p = 0) :
    G1Curve.interpret (G1Endomorphism.map p) = GLVDecomposition.eigenvalue • G1Curve.interpret p :=
  (hom_raw p hp).symm.trans (hom_torsion (G1Curve.interpret p) hr)

#print axioms hom_raw
#print axioms hom_generator
#print axioms hom_torsion
#print axioms eigenvalue
end
end G1Eigenvalue

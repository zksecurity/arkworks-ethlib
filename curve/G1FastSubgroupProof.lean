import G1EigenvalueProof
import CubicRelationProof

open EthLib.Cryptography.Bls

namespace G1FastSubgroup
noncomputable section
local instance : Field Fp := G1Curve.fieldStructure
local instance : CommRing Fp := G1Curve.fieldStructure.toCommRing
local instance : (CubicEndomorphism.curve (4 : Fp)).IsElliptic := G1Curve.ellipticStructure

/-- The absolute BLS parameter used by the pinned subgroup algorithm. -/
def parameter : Nat := 15132376222941642752

theorem parameter_square : (parameter : Int)^2 = GLVDecomposition.a := by decide +kernel

theorem quadratic_relation (p : G1Torsion.Point) :
    p + G1Eigenvalue.hom p = -G1Eigenvalue.hom (G1Eigenvalue.hom p) :=
  CubicRelation.add_map (4 : Fp) G1Endomorphism.beta G1Endomorphism.beta_cube G1Endomorphism.beta_ne_one p

/-- The endomorphism criterion characterizes r-torsion on the entire mathematical curve. -/
theorem criterion_iff (p : G1Torsion.Point) :
    G1Eigenvalue.hom p = -(GLVDecomposition.a • p) ↔ Fr.modulus • p = 0 := by
  constructor
  · intro he
    have hh : G1Eigenvalue.hom (G1Eigenvalue.hom p) =
        (GLVDecomposition.a * GLVDecomposition.a) • p := by
      rw [he, map_neg, map_zsmul, he, smul_neg, neg_neg, ← mul_zsmul]
    have hq := quadratic_relation p
    rw [hh, he] at hq
    have hz : p-GLVDecomposition.a • p+(GLVDecomposition.a*GLVDecomposition.a) • p = 0 := by
      exact eq_neg_iff_add_eq_zero.mp (by simpa only [sub_eq_add_neg] using hq)
    have ho : GLVDecomposition.order = 1-GLVDecomposition.a+GLVDecomposition.a*GLVDecomposition.a := by
      rw [← GLVDecomposition.lattice_determinant]
      ring
    have hr : GLVDecomposition.order • p = 0 := by
      rw [ho, add_zsmul, sub_zsmul, one_zsmul]
      exact hz
    simpa only [GLVDecomposition.order, natCast_zsmul] using hr
  · intro hr
    have hir : GLVDecomposition.order • p = 0 := by
      simpa only [GLVDecomposition.order, natCast_zsmul] using hr
    rw [G1Eigenvalue.hom_torsion p hr, GLVDecomposition.eigenvalue_eq, sub_zsmul, hir, zero_add]

theorem parameter_coprime : (parameter-1).Coprime Fr.modulus := by decide +kernel

/-- The source early-out never rejects a nonzero subgroup point. -/
theorem early_out_safe (p : G1Torsion.Point) (hr : Fr.modulus • p = 0)
    (he : parameter • p = p) : p = 0 := by
  have hn : parameter-1+1 = parameter := by decide +kernel
  have hh : (parameter-1) • p+p = p := by rw [← succ_nsmul, hn, he]
  have hz : (parameter-1) • p = 0 := by
    apply add_right_cancel (b := p)
    simpa only [zero_add] using hh
  exact (nsmul_eq_zero_iff_of_coprime parameter_coprime).mp ⟨hz, hr⟩

#print axioms parameter_square
#print axioms quadratic_relation
#print axioms criterion_iff
#print axioms parameter_coprime
#print axioms early_out_safe
end
end G1FastSubgroup

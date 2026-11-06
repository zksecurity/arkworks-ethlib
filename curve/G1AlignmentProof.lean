import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring
import EthLib.Cryptography.Bls.G1

open EthLib.Cryptography.Bls

namespace G1Alignment

/-- The general and mixed formulas produce identical coordinates at z₂=1. -/
theorem general_eq_mixed (p q : G1) (hz : q.z = Fp.one) :
    G1.addGeneral p q = G1.addMixed p q := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hone : Fp.one = (1 : Fp) := by decide
  simp only [G1.addGeneral, G1.addMixed, hz, hone, mul_one]
  split
  · rfl
  · congr 1
    ring

/-- EthLib's mixed-addition dispatch is an optimization of projective addition. -/
theorem add_projective (p q : G1) : G1.add p q =
    if p.z.isZero then q else if q.z.isZero then p else G1.addGeneral p q := by
  unfold G1.add
  split
  · rfl
  · split
    · rfl
    · split
      · have hz : q.z = Fp.one := by
          apply Fin.ext
          simpa only [Fp.beq, beq_iff_eq] using ‹q.z.beq Fp.one = true›
        exact (general_eq_mixed p q hz).symm
      · rfl

#print axioms general_eq_mixed
#print axioms add_projective
end G1Alignment

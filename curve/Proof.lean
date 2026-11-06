import Mathlib.Data.ZMod.Defs
import Generated.CurveG1
import G1AlignmentProof

open Aeneas Aeneas.Std
open EthLib.Cryptography.Bls

namespace CurveProof

/-- Mathematical interpretation of the Rust Field interface. FieldRefinement and
    ConcreteProof separately establish refinement of the concrete implementation. -/
def specField : CurveG1.Field Fp where
  coremarkerCopyInst := { cloneInst := { clone := fun x => .ok x } }
  constant := fun n => .ok (Fp.ofNat n.val)
  plus := fun a b => .ok (a + b)
  minus := fun a b => .ok (a - b)
  times := fun a b => .ok (a * b)
  square := fun a => .ok (a * a)
  sum_products := fun a b c d => .ok (a*b+c*d)
  negative := fun a => .ok (-a)
  equal := fun a b => .ok (Fp.beq a b)
  is_zero := fun a => .ok (Fp.isZero a)

def embed (p : G1) : CurveG1.Point Fp := ⟨p.x, p.y, p.z⟩

def embedAffine (p : G1) : CurveG1.AffinePoint Fp := ⟨p.x, p.y, false⟩

theorem identity_refines : CurveG1.identity specField = .ok (embed G1.zero) := by
  simp [CurveG1.identity, specField, embed, G1.zero, Fp.ofNat, Fp.one, Fp.zero]
  decide

theorem negate_refines (p : G1) :
    CurveG1.negate specField (embed p) = .ok (embed (G1.neg p)) := by
  simp [CurveG1.negate, specField, embed, G1.neg]

theorem double_refines (p : G1) :
    CurveG1.double specField (embed p) = .ok (embed (G1.double p)) := by
  cases hz : p.z.isZero <;>
    simp [CurveG1.double, specField, embed, G1.double, hz]
  all_goals let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  all_goals ring_nf
  all_goals simp_all

theorem add_general_refines (p q : G1) :
    CurveG1.add_general specField (embed p) (embed q) = .ok (embed (G1.addGeneral p q)) := by
  simp [CurveG1.add_general, specField, embed, G1.addGeneral]
  split
  · split
    · exact double_refines p
    · exact identity_refines
  · let _ : CommRing Fp := Fin.instCommRing Fp.modulus
    congr 2 <;> ring

theorem add_mixed_refines (p q : G1) :
    CurveG1.add_mixed specField (embed p) (embedAffine q) = .ok (embed (G1.addMixed p q)) := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  have hs : p.z * q.y = q.y * p.z := mul_comm _ _
  simp [CurveG1.add_mixed, specField, embed, embedAffine, G1.addMixed, hs]
  split
  · split
    · exact double_refines p
    · exact identity_refines
  · let _ : CommRing Fp := Fin.instCommRing Fp.modulus
    congr 2 <;> ring

theorem add_refines (p q : G1) :
    CurveG1.add specField (embed p) (embed q) = .ok (embed (G1.add p q)) := by
  rw [G1Alignment.add_projective]
  cases hp : p.z.isZero <;> cases hq : q.z.isZero <;>
    simp [CurveG1.add, specField, embed, hp, hq]
  exact add_general_refines p q

#print axioms identity_refines
#print axioms negate_refines
#print axioms double_refines
#print axioms add_refines

#print axioms add_general_refines
#print axioms add_mixed_refines

end CurveProof

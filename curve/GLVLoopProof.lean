import GLVBitProof

open EthLib.Cryptography.Bls

namespace GLVSchedule

/-- The pinned skip flag clears only when a zero pair is encountered while set. -/
def loopBits (k1 k2 : Nat) (b1 b2 b1b2 : G1) (bits : Nat) (skip : Bool) (res : G1) : G1 :=
  if h : bits = 0 then res else
    let bit := bits - 1
    let a := k1.testBit bit
    let b := k2.testBit bit
    if skip && !a && !b then loopBits k1 k2 b1 b2 b1b2 bit false res else
      let res := G1.double res
      let res := if a then (if b then G1.add res b1b2 else G1.add res b1)
        else if b then G1.add res b2 else res
      loopBits k1 k2 b1 b2 b1b2 bit skip res
termination_by bits
decreasing_by all_goals omega

def mulDecomposed (p : G1) (k1 k2 : Bool × Nat) : G1 :=
  let b1 := if k1.1 then p else G1.neg p
  let b2 := if k2.1 then G1Endomorphism.map p else G1.neg (G1Endomorphism.map p)
  let b1b2 := G1.add b1 b2
  loopBits k1.2 k2.2 b1 b2 b1b2 256 true G1.zero

def mulProjective (p : G1) (k : Nat) : G1 :=
  let components := ConcreteGLV.observeComponents (GLVDecomposition.components (k % Fr.modulus : Int))
  mulDecomposed p components.1 components.2

end GLVSchedule

open Aeneas Aeneas.Std Aeneas.Std.WP
open ConcreteCurve ConcreteGLV

namespace ConcreteGLV

@[step] theorem loop_bits_spec (k1 k2 : Scalar) (b1 b2 b1b2 res : RawPoint)
    (bits : U32) (skip : Bool) (hbits : bits.val ≤ 256)
    (h1 : ValidPoint b1) (h2 : ValidPoint b2) (h12 : ValidPoint b1b2) (hr : ValidPoint res) :
    CurveG1.glv.loop_bits k1 k2 b1 b2 b1b2 bits skip res ⦃ out =>
      ValidPoint out ∧ decodePoint out = GLVSchedule.loopBits (scalarValue k1) (scalarValue k2)
        (decodePoint b1) (decodePoint b2) (decodePoint b1b2) bits.val skip (decodePoint res) ⦄ := by
  by_cases hz : bits = 0#u32
  · rw [CurveG1.glv.loop_bits, GLVSchedule.loopBits]
    simp_all
  · have hpos : 0 < bits.val := by scalar_tac
    have hn : bits.val ≠ 0 := by omega
    cases skip <;>
      cases ha : (scalarValue k1).testBit (bits.val - 1) <;>
      cases hb : (scalarValue k2).testBit (bits.val - 1)
    all_goals rw [CurveG1.glv.loop_bits, GLVSchedule.loopBits]
    all_goals step*
    all_goals simp_all
    all_goals step*
termination_by bits.val
decreasing_by all_goals scalar_tac

@[step] theorem mul_decomposed_spec (p : RawPoint)
    (k1 k2 : CurveG1.glv.SignedScalar) (hp : ValidPoint p) :
    CurveG1.glv.mul_decomposed p k1 k2 ⦃ out => ValidPoint out ∧ decodePoint out =
      GLVSchedule.mulDecomposed (decodePoint p)
        (k1.positive, scalarValue k1.magnitude) (k2.positive, scalarValue k2.magnitude) ⦄ := by
  cases h1 : k1.positive <;> cases h2 : k2.positive
  all_goals unfold CurveG1.glv.mul_decomposed
  all_goals simp only [h1, h2, Bool.false_eq_true, ite_eq_left]
  all_goals step*
  all_goals simp_all [GLVSchedule.mulDecomposed]
  all_goals step*

@[step] theorem mul_projective_spec (p : RawPoint) (k : Scalar) (hp : ValidPoint p) :
    CurveG1.glv.mul_projective p k ⦃ out =>
      ValidPoint out ∧ decodePoint out = GLVSchedule.mulProjective (decodePoint p) (scalarValue k) ⦄ := by
  unfold CurveG1.glv.mul_projective
  step as ⟨reduced, hred, hrange⟩
  step with scalar_decomposition_spec reduced hrange as ⟨parts, hparts⟩
  obtain ⟨⟨k1, k2⟩, hs, ho⟩ := Option.map_eq_some_iff.mp hparts
  simp only [hs]
  step*
  all_goals simp_all [observe, GLVSchedule.mulProjective]
  all_goals rw [← hparts]

#print axioms loop_bits_spec
#print axioms mul_decomposed_spec
#print axioms mul_projective_spec

end ConcreteGLV

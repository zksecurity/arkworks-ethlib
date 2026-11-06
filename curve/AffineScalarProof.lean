import GLVGroupProof

open EthLib.Cryptography.Bls

namespace AffineScalar

def addBase (base : G1) (infinity : Bool) (res : G1) : G1 :=
  if infinity then res else G1.add res base

/-- The pinned affine bit iterator skips leading zero bits before double-and-add. -/
def loopBits (k : Nat) (base : G1) (infinity : Bool) (bits : Nat)
    (started : Bool) (res : G1) : G1 :=
  if h : bits = 0 then res else
    let bit := bits-1
    let set := k.testBit bit
    if !started && !set then loopBits k base infinity bit false res else
      let doubled := G1.double res
      let next := if set then addBase base infinity doubled else doubled
      loopBits k base infinity bit true next
termination_by bits
decreasing_by all_goals omega

def mulAffine (x y : Fp) (infinity : Bool) (k : Nat) : G1 :=
  loopBits k ⟨x,y,Fp.one⟩ infinity 256 false G1.zero

end AffineScalar

open Aeneas Aeneas.Std Aeneas.Std.WP
open ConcreteCurve ConcreteField

namespace ConcreteAffineScalar

@[step] theorem affine_loop_spec (base : CurveG1.AffinePoint CurveG1.field.Fp) (k : Scalar)
    (bits : U32) (started : Bool) (res : RawPoint) (hbits : bits.val ≤ 256)
    (hx : FieldProof.Valid base.x) (hy : FieldProof.Valid base.y) (hr : ValidPoint res) :
    CurveG1.scalar.affine_loop base k bits started res ⦃ out => ValidPoint out ∧ decodePoint out =
      AffineScalar.loopBits (scalarValue k) ⟨decode base.x,decode base.y,Fp.one⟩
        base.infinity bits.val started (decodePoint res) ⦄ := by
  by_cases hz : bits = 0#u32
  · rw [CurveG1.scalar.affine_loop, AffineScalar.loopBits]
    simp_all
  · have hpos : 0 < bits.val := by scalar_tac
    have hn : bits.val ≠ 0 := by omega
    cases started <;> cases hs : (scalarValue k).testBit (bits.val-1)
    all_goals rw [CurveG1.scalar.affine_loop, AffineScalar.loopBits]
    all_goals step*
    all_goals simp_all [AffineScalar.addBase]
    all_goals step*
    all_goals simp_all
termination_by bits.val
decreasing_by all_goals scalar_tac

@[step] theorem mul_affine_spec (base : CurveG1.AffinePoint CurveG1.field.Fp) (k : Scalar)
    (hx : FieldProof.Valid base.x) (hy : FieldProof.Valid base.y) :
    CurveG1.scalar.mul_affine base k ⦃ out => ValidPoint out ∧ decodePoint out =
      AffineScalar.mulAffine (decode base.x) (decode base.y) base.infinity (scalarValue k) ⦄ := by
  unfold CurveG1.scalar.mul_affine
  step*
  all_goals simp_all [AffineScalar.mulAffine]

#print axioms affine_loop_spec
#print axioms mul_affine_spec
end ConcreteAffineScalar

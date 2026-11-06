import PreparedMillerStepProof

open EthLib.Cryptography.Bls
open PreparedLineGeometry PreparedMillerStep

namespace PreparedReferenceWalk

noncomputable section
local instance : Field Fp2 := QuadraticDomain.fieldStructure
local instance : Field Fp12 := DodecicDomain.fieldStructure

/-- Execute source double/add steps directly, before storing the prepared coefficient list. -/
def walk (qx qy : Fp2) (px py : Fp) : Nat → PreparedLine.Hom → Fp12 → Fp12
  | 0, _, f => f
  | bits+1, state, f =>
    let d := PreparedLine.double state (Fp.inverse (Fp.ofNat 2))
    let fd := f*f*PreparedMiller.lineValue d.2 px py
    if (CurveG1.pairing.BLS_X.val >>> bits)%2 = 1 then
      let a := PreparedLine.add d.1 qx qy
      walk qx qy px py bits a.1 (fd*PreparedMiller.lineValue a.2 px py)
    else walk qx qy px py bits d.1 fd

/-- The explicit local conditions needed along a walk. The curve-group invariant
must establish these conditions for valid subgroup inputs. -/
def Safe (qx qy : Fp2) : Nat → PreparedLine.Hom → Prop
  | 0, _ => True
  | bits+1, state =>
    PreparedGeometry.OnCurve state ∧ state.y ≠ 0 ∧ state.z ≠ 0 ∧
      let d := (PreparedLine.double state (Fp.inverse (Fp.ofNat 2))).1
      if (CurveG1.pairing.BLS_X.val >>> bits)%2 = 1 then
        d.x + -(qx*d.z) ≠ 0 ∧ Safe qx qy bits (PreparedLine.add d qx qy).1
      else Safe qx qy bits d

/-- The source unsigned parameter is EthLib's unchanged parameter. -/
theorem parameter_eq : CurveG1.pairing.BLS_X.val = blsX := by decide +kernel

private theorem bit_eq (n : Nat) :
    ((blsX >>> n) &&& 1 = 1) = ((CurveG1.pairing.BLS_X.val >>> n)%2 = 1) := by
  rw [Nat.and_one_is_mod, parameter_eq]

/-- Given the explicit local safety conditions, the source walk and the unchanged
EthLib Miller walk produce the same final-exponentiated value. -/
theorem walk_refines (qx qy : Fp2) (px py : Fp) (bits : Nat)
    (state : PreparedLine.Hom) (f old : Fp12) (hs : Safe qx qy bits state)
    (hf : finalExponentiation f = finalExponentiation old) :
    finalExponentiation (walk qx qy px py bits state f) =
      finalExponentiation (millerSteps blsX (untwist ⟨qx,qy,1⟩) (evaluationPoint px py)
        bits (untwist state) old) := by
  induction bits generalizing state f old with
  | zero => exact hf
  | succ bits ih =>
    rcases hs with ⟨hc, hy, hz, hn⟩
    let d := PreparedLine.double state (Fp.inverse (Fp.ofNat 2))
    let fd := f*f*PreparedMiller.lineValue d.2 px py
    generalize hd : millerDouble (untwist state) (evaluationPoint px py) old = oldD
    rcases oldD with ⟨oldT, oldF⟩
    have ht : oldT = untwist d.1 := by
      simpa only [hd] using double_state state (evaluationPoint px py) old hc hy hz
    subst oldT
    have hv : finalExponentiation fd = finalExponentiation oldF := by
      have h := double_value state (Fp.inverse (Fp.ofNat 2)) px py old hc hy hz
      rw [hd] at h
      change finalExponentiation (f*f*PreparedMiller.lineValue d.2 px py) = _
      rw [h]
      simp only [FinalScaling.final_mul]
      rw [hf]
    by_cases hb : (CurveG1.pairing.BLS_X.val >>> bits)%2 = 1
    · have hn' : d.1.x + -(qx*d.1.z) ≠ 0 ∧
          Safe qx qy bits (PreparedLine.add d.1 qx qy).1 := by
        simpa only [hb, ite_true] using hn
      have hdz := PreparedGeometry.double_z_nonzero state (Fp.inverse (Fp.ofNat 2)) hy hz
      generalize ha : millerAdd (untwist d.1) (untwist ⟨qx,qy,1⟩) (evaluationPoint px py) oldF = oldA
      rcases oldA with ⟨oldT, oldA⟩
      have ht : oldT = untwist (PreparedLine.add d.1 qx qy).1 := by
        simpa only [ha] using add_state d.1 qx qy (evaluationPoint px py) oldF hdz hn'.1
      subst oldT
      have hv' : finalExponentiation (fd*PreparedMiller.lineValue (PreparedLine.add d.1 qx qy).2 px py) =
          finalExponentiation oldA := by
        have h := add_value d.1 qx qy px py oldF hdz hn'.1
        rw [ha] at h
        rw [h]
        simp only [FinalScaling.final_mul]
        rw [hv]
      simpa only [walk, millerSteps, hd, bit_eq, hb, ite_true, ha] using
        ih (PreparedLine.add d.1 qx qy).1
          (fd*PreparedMiller.lineValue (PreparedLine.add d.1 qx qy).2 px py) oldA hn'.2 hv'
    · have hn' : Safe qx qy bits d.1 := by simpa only [hb, ite_false] using hn
      simpa only [walk, millerSteps, hd, bit_eq, hb, ite_false] using
        ih d.1 fd oldF hn' hv

#print axioms parameter_eq
#print axioms walk_refines
end
end PreparedReferenceWalk

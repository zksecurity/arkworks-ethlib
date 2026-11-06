import PreparedReferenceWalkProof
import PreparedChunkAlgebraProof

open EthLib.Cryptography.Bls

namespace PreparedCoefficientWalk

private theorem coeffAt_from_drop (p : PreparedMiller.Pair) (i : Nat)
    (c : PreparedLine.Coeff) (cs : List PreparedLine.Coeff)
    (h : p.coeffs.drop i = c::cs) : PreparedMiller.coeffAt p i = c := by
  have hh := congrArg List.head? h
  simp only [List.head?_drop, List.head?_cons] at hh
  simp only [PreparedMiller.coeffAt, hh, Option.getD_some]

private theorem drop_next (cs : List PreparedLine.Coeff) (i : Nat)
    (c : PreparedLine.Coeff) (tail : List PreparedLine.Coeff)
    (h : cs.drop i = c::tail) : cs.drop (i+1) = tail := by
  have ht := congrArg (List.drop 1) h
  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using ht

/-- Reading the stored coefficient suffix executes exactly the direct source walk
for a single pair, including both double/add cursor advances. -/
theorem chunk_eq_walk (p : PreparedMiller.Pair) (qx qy : Fp2) (bits line : Nat)
    (state : PreparedLine.Hom) (f : Fp12)
    (hs : p.coeffs.drop line =
      PreparedLine.lines qx qy (Fp.inverse (Fp.ofNat 2)) state bits) :
    PreparedMiller.chunk [p] bits line f =
      PreparedReferenceWalk.walk qx qy p.px p.py bits state f := by
  induction bits generalizing line state f with
  | zero => rw [PreparedMiller.chunk]; simp only [dite_true, PreparedReferenceWalk.walk]
  | succ bits ih =>
    let d := PreparedLine.double state (Fp.inverse (Fp.ofNat 2))
    by_cases hb : (CurveG1.pairing.BLS_X.val >>> bits)%2 = 1
    · have hs' : p.coeffs.drop line = d.2 :: (PreparedLine.add d.1 qx qy).2 ::
          PreparedLine.lines qx qy (Fp.inverse (Fp.ofNat 2)) (PreparedLine.add d.1 qx qy).1 bits := by
        rw [PreparedLine.lines] at hs
        simpa only [Nat.succ_ne_zero, Nat.add_one_sub_one, dite_false,
          hb, ite_true] using hs
      have hd := coeffAt_from_drop p line _ _ hs'
      have haDrop := drop_next p.coeffs line _ _ hs'
      have ha := coeffAt_from_drop p (line+1) _ _ haDrop
      have htail := drop_next p.coeffs (line+1) _ _ haDrop
      rw [PreparedMiller.chunk]
      simp only [Nat.succ_ne_zero, Nat.add_one_sub_one, dite_false,
        hb, ite_true, PreparedMiller.evalLines, hd, ha, PreparedReferenceWalk.walk]
      exact ih (line+1+1) (PreparedLine.add d.1 qx qy).1 _ htail
    · have hs' : p.coeffs.drop line = d.2 ::
          PreparedLine.lines qx qy (Fp.inverse (Fp.ofNat 2)) d.1 bits := by
        rw [PreparedLine.lines] at hs
        simpa only [Nat.succ_ne_zero, Nat.add_one_sub_one, dite_false,
          hb, ite_false] using hs
      have hd := coeffAt_from_drop p line _ _ hs'
      have htail := drop_next p.coeffs line _ _ hs'
      rw [PreparedMiller.chunk]
      simp only [Nat.succ_ne_zero, Nat.add_one_sub_one, dite_false,
        hb, ite_false, PreparedMiller.evalLines, hd, PreparedReferenceWalk.walk]
      exact ih (line+1) d.1 _ htail

/-- The single-pair prepared consumer agrees with the unchanged EthLib Miller walk
when the explicit walk safety conditions hold. -/
theorem chunk_refines_ethlib (qx qy : Fp2) (px py : Fp) (bits : Nat)
    (state : PreparedLine.Hom) (f : Fp12)
    (hs : PreparedReferenceWalk.Safe qx qy bits state) :
    finalExponentiation (PreparedMiller.chunk
      [⟨px,py,PreparedLine.lines qx qy (Fp.inverse (Fp.ofNat 2)) state bits⟩] bits 0 f) =
      finalExponentiation (millerSteps blsX (PreparedLineGeometry.untwist ⟨qx,qy,Fp2.one⟩)
        (PreparedMillerStep.evaluationPoint px py) bits (PreparedLineGeometry.untwist state) f) := by
  rw [chunk_eq_walk _ qx qy bits 0 state f (by rw [List.drop_zero])]
  exact PreparedReferenceWalk.walk_refines qx qy px py bits state f f hs rfl

#print axioms chunk_eq_walk
#print axioms chunk_refines_ethlib
end PreparedCoefficientWalk

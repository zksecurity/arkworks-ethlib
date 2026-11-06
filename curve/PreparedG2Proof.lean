import PreparedLineProof

open EthLib.Cryptography.Bls

namespace PreparedLine

/-- Source bit loop, returning the same ordered coefficient list as G2Prepared. -/
def lines (qx qy : Fp2) (half : Fp) (state : Hom) (bits : Nat) : List Coeff :=
  if h : bits = 0 then [] else
    let bit := bits-1
    let d := double state half
    if (CurveG1.pairing.BLS_X.val >>> bit)%2 = 1 then
      let a := add d.1 qx qy
      d.2 :: a.2 :: lines qx qy half a.1 bit
    else d.2 :: lines qx qy half d.1 bit
termination_by bits
decreasing_by all_goals omega

def remainingLines : Nat → Nat
  | 0 => 0
  | bit+1 => 1+(if (CurveG1.pairing.BLS_X.val >>> bit)%2 = 1 then 1 else 0)+remainingLines bit

/-- Producer and consumer advance by the same double/add line count. -/
theorem remaining_step (bits : Nat) (h : 0 < bits) :
    remainingLines bits = 1+(if (CurveG1.pairing.BLS_X.val >>> (bits-1))%2 = 1 then 1 else 0)+
      remainingLines (bits-1) := by
  cases bits with
  | zero => omega
  | succ n => rfl

theorem remaining_positive (bits : Nat) (h : 0 < bits) : 0 < remainingLines bits := by
  rw [remaining_step bits h]
  omega

theorem remaining_full : remainingLines 63 = 68 := by decide +kernel

theorem lines_length (qx qy : Fp2) (half : Fp) (state : Hom) (bits : Nat) :
    (lines qx qy half state bits).length = remainingLines bits := by
  induction bits generalizing state with
  | zero => rw [lines]; simp [remainingLines]
  | succ n ih =>
    rw [lines]
    simp only [Nat.succ_ne_zero, Nat.add_one_sub_one]
    split_ifs <;> simp_all [remainingLines] <;> omega

/-- The fixed BLS parameter produces 63 double lines and five addition lines. -/
theorem prepared_length (qx qy : Fp2) (half : Fp) (state : Hom) :
    (lines qx qy half state 63).length = 68 := by
  rw [lines_length, remaining_full]

/-- The affine producer includes the infinity branch and the source half constant. -/
def prepare (qx qy : Fp2) (infinity : Bool) : List Coeff :=
  if infinity then [] else
    lines qx qy (Fp.inverse (Fp.ofNat 2)) ⟨qx,qy,Fp2.one⟩ 63

theorem prepare_length (qx qy : Fp2) (infinity : Bool) :
    (prepare qx qy infinity).length = if infinity then 0 else 68 := by
  cases infinity <;> simp [prepare, prepared_length]

end PreparedLine

open Aeneas Aeneas.Std Aeneas.Std.WP
open ConcreteExtension ConcretePreparedLine

namespace ConcretePreparedG2

def ValidCoeffs (cs : List RawCoeff) : Prop := ∀ c ∈ cs, ValidCoeff c

def decodeCoeffs (cs : List RawCoeff) : List PreparedLine.Coeff := cs.map decodeCoeff

@[local step] private theorem push_spec (cs : alloc.vec.Vec RawCoeff) (c : RawCoeff)
    (hs : ValidCoeffs cs.val) (hc : ValidCoeff c) (hlen : cs.val.length < Usize.max) :
    alloc.vec.Vec.push cs c ⦃ out => out.val = cs.val ++ [c] ∧ ValidCoeffs out.val ⦄ := by
  apply spec_mono (alloc.vec.Vec.push_spec cs c hlen)
  rintro out he
  refine ⟨he,?_⟩
  rw [he]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hs x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hc

@[local step] private theorem double_parts_spec (p : RawHom) (half : ConcreteField.Raw)
    (hp : ValidHom p) (hh : FieldProof.Valid half) :
    CurveG1.pairing.prepared.HomG2.double p half ⦃ r =>
      ValidHom r.1 ∧ ValidCoeff r.2 ∧
      decodeHom r.1 = (PreparedLine.double (decodeHom p) (ConcreteField.decode half)).1 ∧
      decodeCoeff r.2 = (PreparedLine.double (decodeHom p) (ConcreteField.decode half)).2 ⦄ := by
  apply spec_mono (double_spec p half hp hh)
  rintro r ⟨hr,hc,he⟩
  exact ⟨hr,hc,congrArg Prod.fst he,congrArg Prod.snd he⟩

@[local step] private theorem add_parts_spec (p : RawHom) (qx qy : Raw2)
    (hp : ValidHom p) (hx : Valid2 qx) (hy : Valid2 qy) :
    CurveG1.pairing.prepared.HomG2.add p qx qy ⦃ r =>
      ValidHom r.1 ∧ ValidCoeff r.2 ∧
      decodeHom r.1 = (PreparedLine.add (decodeHom p) (decode2 qx) (decode2 qy)).1 ∧
      decodeCoeff r.2 = (PreparedLine.add (decodeHom p) (decode2 qx) (decode2 qy)).2 ⦄ := by
  apply spec_mono (add_spec p qx qy hp hx hy)
  rintro r ⟨hr,hc,he⟩
  exact ⟨hr,hc,congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- Vector pushes preserve canonical coefficients, exact order, and the bounded allocation length. -/
@[step] theorem bits_spec (qx qy : Raw2) (half : ConcreteField.Raw) (state : RawHom)
    (cs : alloc.vec.Vec RawCoeff) (bits : U32) (hx : Valid2 qx) (hy : Valid2 qy)
    (hh : FieldProof.Valid half) (hs : ValidHom state) (hc : ValidCoeffs cs.val)
    (hb : bits.val ≤ 63) (hcap : cs.val.length+2*bits.val ≤ Usize.max) :
    CurveG1.pairing.prepared.prepare_bits qx qy half state cs bits ⦃ out =>
      ValidCoeffs out.val ∧ out.val.length ≤ cs.val.length+2*bits.val ∧
      decodeCoeffs out.val = decodeCoeffs cs.val ++
        PreparedLine.lines (decode2 qx) (decode2 qy) (ConcreteField.decode half) (decodeHom state) bits.val ⦄ := by
  rw [CurveG1.pairing.prepared.prepare_bits, PreparedLine.lines]
  step*
  all_goals (try (split <;> step*))
  all_goals (try (rcases x with ⟨state3,line1⟩; step*))
  all_goals simp_all [decodeCoeffs, CurveG1.pairing.BLS_X, Nat.and_one_is_mod, List.append_assoc]
  all_goals omega
termination_by bits.val
decreasing_by all_goals scalar_tac

private theorem prepare_refines (qx qy : Raw2) (infinity : Bool)
    (hx : Valid2 qx) (hy : Valid2 qy) :
    CurveG1.pairing.prepared.prepare_affine qx qy infinity ⦃ out =>
      out.infinity = infinity ∧ ValidCoeffs out.ell_coeffs.val ∧
      decodeCoeffs out.ell_coeffs.val = PreparedLine.prepare (decode2 qx) (decode2 qy) infinity ⦄ := by
  have ⟨ho,he⟩ := ConcreteField.montgomery_one
  have hn : ValidCoeffs [] := by simp [ValidCoeffs]
  have hcap : 2*63 ≤ Usize.max := by scalar_tac
  have ht : Fp.one+Fp.one = Fp.ofNat 2 := by decide +kernel
  unfold CurveG1.pairing.prepared.prepare_affine
  cases infinity <;> step*
  all_goals simp_all [PreparedLine.prepare, decodeHom, ValidHom, decode2, Valid2, decodeCoeffs,
    Fp2.one]

/-- Full extracted affine preparation terminates and returns exactly the ordered source coefficients. -/
@[step] theorem prepare_spec (qx qy : Raw2) (infinity : Bool)
    (hx : Valid2 qx) (hy : Valid2 qy) :
    CurveG1.pairing.prepared.prepare_affine qx qy infinity ⦃ out =>
      out.infinity = infinity ∧ ValidCoeffs out.ell_coeffs.val ∧
      decodeCoeffs out.ell_coeffs.val = PreparedLine.prepare (decode2 qx) (decode2 qy) infinity ∧
      out.ell_coeffs.val.length = if infinity then 0 else 68 ⦄ := by
  apply spec_mono (prepare_refines qx qy infinity hx hy)
  rintro out ⟨hi,hc,he⟩
  refine ⟨hi,hc,he,?_⟩
  have hlen := congrArg List.length he
  simpa only [decodeCoeffs, List.length_map, PreparedLine.prepare_length] using hlen

#print axioms PreparedLine.remaining_step
#print axioms PreparedLine.remaining_positive
#print axioms PreparedLine.remaining_full
#print axioms PreparedLine.lines_length
#print axioms PreparedLine.prepared_length
#print axioms PreparedLine.prepare_length
#print axioms bits_spec
#print axioms prepare_spec
end ConcretePreparedG2

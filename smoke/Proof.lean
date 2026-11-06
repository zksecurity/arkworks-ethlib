import Generated.Smoke
open Aeneas Aeneas.Std

-- This theorem is about the actual Aeneas-generated function.
theorem compression_flag_is_set (b : U8) :
    ∃ out, ToolSmoke.set_compression_flag b = .ok out ∧
      out &&& 128#u8 = 128#u8 := by
  refine ⟨b ||| 128#u8, rfl, ?_⟩
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  change (b.bv ||| 128#8) &&& 128#8 = 128#8
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases b.bv[i] <;> cases (128#8)[i] <;> rfl

#print axioms compression_flag_is_set

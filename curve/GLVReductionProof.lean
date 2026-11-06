import GLVScalarProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteCurve GLVArithmetic

namespace ConcreteGLV

theorem scalar_bound (k : Scalar) : scalarValue k < B^4 := by
  unfold scalarValue B
  scalar_tac

@[step] theorem reduce_scalar_spec (k : Scalar) :
    CurveG1.glv.reduce_scalar k ⦃ out =>
      scalarValue out = scalarValue k % Fr.modulus ∧ scalarValue out < Fr.modulus ⦄ := by
  have hk := scalar_bound k
  have hr : 0 < Fr.modulus := by decide +kernel
  have hrbound : Fr.modulus < 2^255 := by decide +kernel
  have hm := Nat.mod_lt (scalarValue k) hr
  unfold CurveG1.glv.reduce_scalar
  step*
  all_goals simp_all only [order_value]
  all_goals simp_all [scalarValue, value, B]
  all_goals omega

#print axioms scalar_bound
#print axioms reduce_scalar_spec

end ConcreteGLV

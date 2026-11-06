import GLVArithmeticProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteCurve GLVArithmetic

namespace ConcreteGLV

def rounded (k : Nat) : Nat :=
  roundDivNat (k * 228988810152649578064853576960394133503) Fr.modulus

private theorem round_cast (n d : Nat) :
    GLVDecomposition.roundDiv (n : Int) (d : Int) = (roundDivNat n d : Int) := by
  unfold GLVDecomposition.roundDiv roundDivNat
  rw [← Int.ofNat_tdiv, ← Int.ofNat_tmod]
  by_cases h : d < 2 * (n % d)
  · have hi : (d : Int) < 2 * ((n % d : Nat) : Int) := by exact_mod_cast h
    simp only [ite_eq_left h, ite_eq_left hi, Int.natCast_add, Int.natCast_one]
  · have hi : ¬(d : Int) < 2 * ((n % d : Nat) : Int) := by exact_mod_cast h
    simp only [ite_eq_right h, ite_eq_right hi, Nat.add_zero, Int.add_zero]

private theorem numerator_cast (k : Nat) :
    ((k * 228988810152649578064853576960394133503 : Nat) : Int) =
      (k : Int) * (GLVDecomposition.a - 1) := by
  simp [GLVDecomposition.a]

theorem rounded_eq (k : Nat) :
    GLVDecomposition.roundedQuotient ((k : Int) * (GLVDecomposition.a - 1)) =
      (rounded k : Int) := by
  change GLVDecomposition.roundDiv ((k : Int) * (GLVDecomposition.a - 1)) _ = _
  rw [← numerator_cast]
  exact round_cast _ _

theorem rounded_bounds (k : Nat) (hk : k < Fr.modulus) :
    rounded k < 2^128 ∧
    k - rounded k * 228988810152649578064853576960394133504 < 2^128 ∧
    rounded k * 228988810152649578064853576960394133504 - k < 2^128 := by
  have h := GLVDecomposition.component_bounds (k : Int) (by omega) (by change (k : Int) < (Fr.modulus : Int); exact_mod_cast hk)
  rw [GLVDecomposition.canonical_components (k : Int) (by omega) (by change (k : Int) < (Fr.modulus : Int); exact_mod_cast hk),
    rounded_eq] at h
  simp only [GLVDecomposition.a] at h
  push_cast at h
  omega

def observe (p : CurveG1.glv.SignedScalar × CurveG1.glv.SignedScalar) :
    (Bool × Nat) × (Bool × Nat) :=
  ((p.1.positive, scalarValue p.1.magnitude), (p.2.positive, scalarValue p.2.magnitude))

def observeComponents (c : Int × Int) : (Bool × Nat) × (Bool × Nat) :=
  (GLVDecomposition.signedMagnitude c.1, GLVDecomposition.signedMagnitude c.2)

def natObservation (k q A : Nat) : (Bool × Nat) × (Bool × Nat) :=
  ((decide (q * A < k), k - q * A + (q * A - k)), (false, q))

private theorem canonical_observation (k q A : Nat) :
    observeComponents ((k : Int) - (q : Int) * (A : Int), -(q : Int)) =
      natObservation k q A := by
  unfold observeComponents natObservation GLVDecomposition.signedMagnitude
  simp only [← Int.natCast_mul]
  apply Prod.ext <;> apply Prod.ext
  all_goals simp
  all_goals omega

@[step] theorem signed_difference_spec (a b : Limbs) (ha : value a < B^4) (hb : value b < B^4) :
    CurveG1.glv.signed_difference a b ⦃ out =>
      out.positive = decide (value b < value a) ∧
      scalarValue out.magnitude = value a - value b + (value b - value a) ⦄ := by
  unfold CurveG1.glv.signed_difference
  step
  step
  split_ifs <;> step*
  all_goals simp_all [value, scalarValue, B]
  all_goals omega

@[step] theorem scalar_decomposition_nat_spec (k : Scalar) (hk : scalarValue k < Fr.modulus) :
    CurveG1.glv.scalar_decomposition k ⦃ out => out.map observe =
      some (natObservation (scalarValue k) (rounded (scalarValue k))
        228988810152649578064853576960394133504) ⦄ := by
  have hb := rounded_bounds (scalarValue k) hk
  have hrbound : Fr.modulus < 2^255 := by decide +kernel
  unfold CurveG1.glv.scalar_decomposition
  step*
  all_goals simp_all only [order_value]
  all_goals simp_all [observe, natObservation, value, scalarValue, B, rounded]
  all_goals omega

theorem model_observation (k : Nat) (hk : k < Fr.modulus) :
    observeComponents (GLVDecomposition.components (k : Int)) =
      natObservation k (rounded k) 228988810152649578064853576960394133504 := by
  rw [GLVDecomposition.canonical_components (k : Int) (by omega)
    (by change (k : Int) < (Fr.modulus : Int); exact_mod_cast hk), rounded_eq]
  exact canonical_observation k (rounded k) _

@[step] theorem scalar_decomposition_spec (k : Scalar) (hk : scalarValue k < Fr.modulus) :
    CurveG1.glv.scalar_decomposition k ⦃ out => out.map observe = some
      (observeComponents (GLVDecomposition.components (scalarValue k : Int))) ⦄ := by
  apply spec_mono (scalar_decomposition_nat_spec k hk)
  intro out ho
  rw [model_observation (scalarValue k) hk]
  exact ho

@[step] theorem scalar_decomposition_reject (k : Scalar) (hk : Fr.modulus ≤ scalarValue k) :
    CurveG1.glv.scalar_decomposition k ⦃ out => out = none ⦄ := by
  unfold CurveG1.glv.scalar_decomposition
  step*
  all_goals simp_all only [order_value]
  all_goals simp_all [value, scalarValue, B]
  all_goals omega

def result (k : Nat) : Option ((Bool × Nat) × (Bool × Nat)) :=
  if k < Fr.modulus then some (observeComponents (GLVDecomposition.components (k : Int))) else none

/-- Complete public contract, including canonical-input validation. -/
theorem scalar_decomposition_total_spec (k : Scalar) :
    CurveG1.glv.scalar_decomposition k ⦃ out => out.map observe = result (scalarValue k) ⦄ := by
  by_cases hk : scalarValue k < Fr.modulus
  · apply spec_mono (scalar_decomposition_spec k hk)
    intro out ho
    simpa only [result, ite_eq_left hk] using ho
  · apply spec_mono (scalar_decomposition_reject k (by omega))
    intro out ho
    simp only [ho, Option.map_none, result, ite_eq_right hk]

#print axioms rounded_eq
#print axioms rounded_bounds
#print axioms signed_difference_spec
#print axioms scalar_decomposition_nat_spec
#print axioms model_observation
#print axioms scalar_decomposition_spec
#print axioms scalar_decomposition_reject
#print axioms scalar_decomposition_total_spec

end ConcreteGLV

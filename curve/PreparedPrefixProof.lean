import PreparedG2Proof
import Mathlib.Data.Int.GCD

open EthLib.Cryptography.Bls

namespace PreparedPrefix

/-- At each bit, exclude twice the current point; an addition also excludes
its equality with either sign of the original point. -/
def factors : Nat → Nat → List Nat
  | 0, _ => []
  | bits+1, k =>
    let doubled := 2*k
    if (CurveG1.pairing.BLS_X.val >>> bits)%2 = 1 then
      doubled :: (doubled-1) :: (doubled+1) :: factors bits (doubled+1)
    else doubled :: factors bits doubled

/-- Every factor needed by the actual unsigned source loop is coprime to r. -/
theorem factors_coprime : ∀ n ∈ factors 63 1, n.Coprime Fr.modulus := by
  have h : (factors 63 1).all (fun n => decide (n.Coprime Fr.modulus)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

/-- A nonzero point killed by r cannot be killed by a scalar coprime to r. -/
theorem nsmul_nonzero {G : Type*} [AddMonoid G] (q : G) (n r : Nat)
    (hc : n.Coprime r) (hr : r • q = 0) (hq : q ≠ 0) : n • q ≠ 0 := by
  intro hn
  exact hq ((nsmul_eq_zero_iff_of_coprime hc).mp ⟨hn, hr⟩)

/-- The source loop's forbidden multiples are nonzero on every nonzero r-torsion point. -/
theorem factors_nonzero {G : Type*} [AddMonoid G] (q : G)
    (hr : Fr.modulus • q = 0) (hq : q ≠ 0) :
    ∀ n ∈ factors 63 1, n • q ≠ 0 := by
  intro n hn
  exact nsmul_nonzero q n Fr.modulus (factors_coprime n hn) hr hq

#print axioms factors_coprime
#print axioms nsmul_nonzero
#print axioms factors_nonzero
end PreparedPrefix

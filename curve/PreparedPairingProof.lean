import PreparedMillerProof
import PairingCheckProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open ConcreteExtension

namespace PreparedMiller

/-- Final identity test over the complete prepared source field schedule. -/
def check (pairs : List (G1 × G2)) : Bool := (finalExponentiation (multiMiller pairs)).isOne

end PreparedMiller

namespace ConcretePreparedMiller

private theorem beq_one (a : Fp12) : Fp12.beq a Fp12.one = a.isOne := by rfl

/-- The source-scheduled Rust endpoint terminates and computes its exact prepared pairing predicate. -/
@[step] theorem pairing_check_spec (pairs : Slice RawInput) (hp : ValidInputs pairs.val) :
    CurveG1.pairing.prepared_miller.pairing_check pairs ⦃ r =>
      r = PreparedMiller.check (decodeInputs pairs.val) ⦄ := by
  unfold CurveG1.pairing.prepared_miller.pairing_check
  step*
  all_goals simp_all [PreparedMiller.check, beq_one, HardExponent.final_cube_isOne]

#print axioms pairing_check_spec
end ConcretePreparedMiller

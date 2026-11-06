import Fp12FieldProof
import EthLib.Cryptography.Bls.Pairing

open EthLib.Cryptography.Bls

namespace ConcretePairing

/-- One transition of EthLib's pairing-product loop. -/
def pairingStep (acc : Fp12) (pq : G1 × G2) : Fp12 :=
  if pq.1.isInfinity || pq.2.isInfinity then acc
  else acc * (millerLoop blsX (Embedded.ofG2 pq.2) (Embedded.ofG1 pq.1)).conjugate

/-- A Miller contribution before the product's final exponentiation. -/
def millerTerm (p : G1) (q : G2) : Fp12 :=
  if p.isInfinity || q.isInfinity then Fp12.one
  else (millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)).conjugate

theorem pairing_check_fold (pairs : List (G1 × G2)) :
    pairingCheck pairs.toArray = (finalExponentiation (pairs.foldl pairingStep Fp12.one)).isOne := by
  simp [pairingCheck]
  have body (pq : G1 × G2) (acc : Fp12) :
      (if pq.1.isInfinity = true ∨ pq.2.isInfinity = true then pure (ForInStep.yield acc)
       else pure (ForInStep.yield (acc *
         (millerLoop blsX (Embedded.ofG2 pq.2) (Embedded.ofG1 pq.1)).conjugate)) :
         Id (ForInStep Fp12)) = pure (ForInStep.yield (pairingStep acc pq)) := by
    unfold pairingStep
    simp only [Bool.or_eq_true]
    split <;> rfl
  simp only [body, List.forIn_pure_yield_eq_foldl]
  rfl

#print axioms pairing_check_fold
end ConcretePairing

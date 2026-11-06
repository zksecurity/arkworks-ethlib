import EthLib.Cryptography.Bls.Compress

open EthLib.Cryptography.Bls

namespace ConcreteEncoding

/-- Projective curve equation over EthLib's field; infinity is represented by z=0. -/
def onCurve (p : G1) : Bool :=
  if p.isInfinity then true else
    let z2 := p.z * p.z
    let z6 := z2 * z2 * z2
    Fp.beq (p.y * p.y) (p.x * p.x * p.x + Fp.ofNat 4 * z6)

def validSubgroupPoint (p : G1) : Bool := onCurve p && G1.inSubgroup p

def validPublicKeyPoint (p : G1) : Bool := !p.isInfinity && validSubgroupPoint p

end ConcreteEncoding

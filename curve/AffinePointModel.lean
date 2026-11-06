import EthLib.Cryptography.Bls.G1

open EthLib.Cryptography.Bls

namespace AffineScalarGroup

def effectiveBase (x y : Fp) (infinity : Bool) : G1 :=
  if infinity then G1.zero else ⟨x,y,Fp.one⟩

end AffineScalarGroup

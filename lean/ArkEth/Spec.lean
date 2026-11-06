import EthLib.Cryptography.Bls.Compress

namespace ArkEth
open EthLib.Cryptography.Bls

/-- Mathematical observation of arkworks' affine representation.
    Relating actual Montgomery limbs to these fields remains a proof obligation. -/
structure AffineInput where
  x : Fp
  y : Fp
  infinity : Bool

def AffineInput.toEthLib (p : AffineInput) : G1 :=
  if p.infinity then G1.zero else ⟨p.x, p.y, Fp.one⟩

def AffineInput.onCurve (p : AffineInput) : Prop :=
  p.infinity = true ∨ p.y * p.y = p.x * p.x * p.x + Fp.ofNat 4

/-- The independent encoding target is the actual vendored EthLib function. -/
def encodeSpec (p : AffineInput) : ByteArray := G1.compress p.toEthLib

/-- Exact compressed framing, curve reconstruction, and subgroup validation.
    Identity is allowed, matching arkworks' group decoder rather than BLS KeyValidate. -/
def decodeSpec (bytes : ByteArray) : Except BlsError G1 := do
  let p ← G1.uncompress bytes
  if G1.inSubgroup p then return p else throw .notInSubgroup

/-- A target proposition, NOT a theorem or an assumed axiom.
    `rustEncode` must eventually be an observation of Aeneas-generated code. -/
def EncoderRefinesEthLib (rustEncode : AffineInput → Option ByteArray) : Prop :=
  ∀ p, p.onCurve → rustEncode p = some (encodeSpec p)

/-- Both decoders must reject the same inputs and return the same canonical bytes.
    Point-representation refinement is an additional obligation. -/
def decodeObservation (bytes : ByteArray) : Option ByteArray :=
  match decodeSpec bytes with
  | .ok p => some (G1.compress p)
  | .error _ => none

theorem infinity_encoding (x y : Fp) :
    encodeSpec ⟨x, y, true⟩ = G1.infinityBytes := by
  simp [encodeSpec, AffineInput.toEthLib, G1.compress, G1.isInfinity,
    G1.zero, Fp.isZero, Fp.zero]

end ArkEth

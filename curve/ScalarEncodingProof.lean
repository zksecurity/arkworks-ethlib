import G1CompressionProof
import GLVCorrectnessProof

open EthLib.Cryptography.Bls

namespace ScalarEncoding

/-- The affine source path is full integer multiplication, with no reduction modulo r. -/
def mulInteger (p : G1) (k : Nat) : G1 :=
  AffineScalar.mulAffine (G1.toAffine p).1 (G1.toAffine p).2 p.isInfinity k

theorem integer_correct (p : G1) (k : Nat) (hp : G1Curve.OnCurve p) (hk : k < 2^256) :
    G1Curve.OnCurve (mulInteger p k) ∧
    G1Curve.interpret (mulInteger p k) = k • G1Curve.interpret p := by
  have h := AffineScalarGroup.mul_affine_correct (G1.toAffine p).1 (G1.toAffine p).2
    p.isInfinity k hk (G1AffineInterpretation.affine_data_onCurve p hp)
  simpa only [mulInteger, G1AffineInterpretation.baseAction_toAffine p hp] using h

/-- Source affine multiplication preserves the existing full-curve encoded result. -/
theorem integer_compressed (p : G1) (k : Nat) (hp : G1Curve.OnCurve p) (hk : k < 2^256) :
    G1.compress (mulInteger p k) = G1.compress (G1.mulNat p k) := by
  have hs := integer_correct p k hp hk
  have hm := G1Curve.mulNat_correct p k hp
  exact G1Compression.compress_eq _ _ hs.1 hm.1 (hs.2.trans hm.2.symm)

/-- Source projective GLV multiplication preserves the encoded result on subgroup inputs. -/
theorem glv_compressed (p : G1) (k : Nat) (hp : G1Curve.OnCurve p)
    (hr : Fr.modulus • G1Curve.interpret p = 0) :
    G1.compress (GLVSchedule.mulProjective p k) = G1.compress (G1.mulNat p k) := by
  have hs := GLVCorrectness.mul_projective_correct p k hp hr
  have hm := G1Curve.mulNat_correct p k hp
  exact G1Compression.compress_eq _ _ hs.1 hm.1 (hs.2.trans hm.2.symm)

#print axioms integer_correct
#print axioms integer_compressed
#print axioms glv_compressed
end ScalarEncoding

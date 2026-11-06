import ArkEth.Spec

namespace ArkEth
open EthLib.Cryptography.Bls

private theorem one_mul_one : Fp.one * Fp.one = Fp.one := by decide

private theorem powNat_one (n : Nat) : Fp.powNat Fp.one n = Fp.one := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Fp.powNat.eq_1]
    split
    · rfl
    · rw [one_mul_one, ih (n / 2) (by omega)]
      split <;> simp only [one_mul_one]

theorem inverse_one : Fp.inverse Fp.one = Fp.one := powNat_one _

/-- The affine representation used at our boundary needs no coordinate change. -/
theorem affine_coordinates (x y : Fp) : G1.toAffine ⟨x, y, Fp.one⟩ = (x, y) := by
  have hz : Fp.isZero Fp.one = false := by decide
  simp only [G1.toAffine, hz, Bool.false_eq_true, ↓reduceIte, inverse_one, one_mul_one]
  change (x * 1, y * 1) = (x, y)
  apply Prod.ext <;> apply Fin.ext
  · change (x.val * 1) % Fp.modulus = x.val
    simp [Nat.mod_eq_of_lt x.isLt]
  · change (y.val * 1) % Fp.modulus = y.val
    simp [Nat.mod_eq_of_lt y.isLt]

/-- A reusable reduction of the REAL EthLib compressor to its byte operations.
    This is not a statement about Rust or an Aeneas-extracted implementation. -/
theorem finite_encoding (x y : Fp) :
    encodeSpec ⟨x, y, false⟩ =
      let bytes := x.toBytesBE
      let tagged := bytes.set! 0 ((bytes.get! 0) ||| 0x80)
      if Fp.signBit y then tagged.set! 0 ((tagged.get! 0) ||| 0x20) else tagged := by
  have hz : Fp.isZero Fp.one = false := by decide
  cases hs : Fp.signBit y <;>
    simp [encodeSpec, AffineInput.toEthLib, G1.compress, G1.isInfinity,
      hz, affine_coordinates, hs]

end ArkEth

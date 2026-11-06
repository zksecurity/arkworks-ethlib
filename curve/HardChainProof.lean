import CyclotomicParameterProof

open EthLib.Cryptography.Bls

namespace HardChain
local instance : CommRing Fp12 := DodecicField.ringStructure
open CyclotomicParameter

def signed (a : Fp12) : Fp12 := (a^CurveG1.pairing.BLS_X.val).conjugate

/-- The hard chain's mathematical operations in the pinned arkworks temporary order. -/
def chain (r : Fp12) : Fp12 :=
  let y0 := r*r
  let y1 := signed r
  let y2 := r.conjugate
  let y1 := y1*y2
  let y2 := signed y1
  let y1 := y1.conjugate
  let y1 := y1*y2
  let y2 := signed y1
  let y1 := y1^Fp.modulus
  let y1 := y1*y2
  let r := r*y0
  let y0 := signed y1
  let y2 := signed y0
  let y0 := y1^(Fp.modulus^2)
  let y1 := y1.conjugate
  let y1 := y1*y2
  let y1 := y1*y0
  r*y1

private def xExponent : Nat := CurveG1.pairing.BLS_X.val*(order-1)

private def exponent : Nat :=
  let y0 := 2
  let y1 := xExponent
  let y2 := order-1
  let y1 := y1+y2
  let y2 := y1*xExponent
  let y1 := y1*(order-1)
  let y1 := y1+y2
  let y2 := y1*xExponent
  let y1 := y1*Fp.modulus
  let y1 := y1+y2
  let r := 1+y0
  let y0 := y1*xExponent
  let y2 := y0*xExponent
  let y0 := y1*(Fp.modulus^2)
  let y1 := y1*(order-1)
  let y1 := y1+y2
  let y1 := y1+y0
  r+y1

/-- The actual operation chain's exponent has the required residue modulo Phi_12(p). -/
theorem exponent_residue : exponent % order = 3*finalExpHard := by decide +kernel

private theorem conjugate_power_of_power (a : Fp12) (ha : a^order = 1) (e : Nat) :
    (a^e).conjugate = a^(e*(order-1)) := by
  rw [conjugate_power _ (power_root a ha e), pow_mul]

private theorem signed_power (a : Fp12) (ha : a^order = 1) (e : Nat) :
    signed (a^e) = a^(e*xExponent) := by
  rw [signed, ←pow_mul, conjugate_power_of_power a ha]
  simp only [xExponent, Nat.mul_assoc]

private theorem chain_power (a : Fp12) (ha : a^order = 1) : chain a = a^exponent := by
  conv_lhs => arg 1; rw [←pow_one a]
  simp only [chain, signed_power a ha, conjugate_power_of_power a ha, ←pow_add,
    ←pow_mul, Nat.one_mul]
  apply congrArg (fun n : Nat => a^n)
  unfold exponent
  decide +kernel

private theorem reduce_power (a : Fp12) (ha : a^order = 1) (n : Nat) :
    a^n = a^(n % order) := by
  conv_lhs => rw [←Nat.mod_add_div n order]
  rw [pow_add, pow_mul, ha, one_pow, mul_one]

private theorem conjugate_zero : Fp12.conjugate 0 = 0 := by
  rw [←Cyclotomic.power_six, zero_pow (by decide +kernel : Fp.modulus^6 ≠ 0)]

private theorem chain_zero : chain 0 = 0 := by
  have hx : CurveG1.pairing.BLS_X.val ≠ 0 := by decide +kernel
  have hp : Fp.modulus ≠ 0 := by decide +kernel
  have hp2 : Fp.modulus^2 ≠ 0 := by decide +kernel
  simp only [chain, signed, zero_mul, zero_pow hx, zero_pow hp, zero_pow hp2, conjugate_zero]

/-- The complete hard chain computes EthLib's cubed hard power, including zero. -/
theorem chain_correct (a : Fp12) (ha : CyclotomicSquare.Admissible a) :
    chain a = (a^finalExpHard)^3 := by
  rcases ha with hz | hr
  · rw [hz, chain_zero, zero_pow (by decide +kernel : finalExpHard ≠ 0), zero_pow (by decide)]
  · rw [chain_power a hr, reduce_power a hr, exponent_residue, Nat.mul_comm 3 finalExpHard, pow_mul]

#print axioms exponent_residue
#print axioms chain_correct
end HardChain

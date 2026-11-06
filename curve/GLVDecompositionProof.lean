import G1EndomorphismProof
import Mathlib.Data.Int.ModEq

open EthLib.Cryptography.Bls

namespace GLVDecomposition

/-- The pinned BLS12-381 lattice basis is (A,1),(-1,A-1). -/
def a : Int := 228988810152649578064853576960394133504

def order : Int := Fr.modulus

def eigenvalue : Int :=
  52435875175126190479447740508185965837461563690374988244538805122978187051009

/-- num-bigint `div_rem` truncates toward zero; rounding uses a strict comparison. -/
def roundDiv (n d : Int) : Int :=
  n.tdiv d + if 2 * n.tmod d > d then 1 else 0

def roundedQuotient (n : Int) : Int := roundDiv n order

/-- Signed components before their absolute values are converted to the scalar field. -/
def components (k : Int) : Int × Int :=
  let beta1 := roundedQuotient (k * (a - 1))
  let beta2 := roundedQuotient (k * (-1))
  let b11 := beta1 * a
  let b12 := beta2 * (-1)
  let b1 := b11 + b12
  let b21 := beta1 * 1
  let b22 := beta2 * (a - 1)
  let b2 := b21 + b22
  (k - b1, -b2)

theorem lattice_determinant : a * (a - 1) + 1 = order := by decide +kernel

theorem eigenvalue_eq : eigenvalue = order - a := by decide +kernel

theorem order_pos : 0 < order := by decide +kernel

/-- The lattice identity holds independently of the quotient approximation. -/
private theorem lattice_identity (k b1 b2 A r : Int) (hr : A * (A - 1) + 1 = r) :
    (k - (b1 * A + b2 * (-1))) + (r - A) * (-(b1 * 1 + b2 * (A - 1))) =
      k + r * (-b1 + b2 * (2 - A)) := by
  rw [← hr]
  ring

/-- The signed result reconstructs k modulo r, before any subgroup reasoning. -/
theorem reconstruction (k : Int) :
    (components k).1 + eigenvalue * (components k).2 ≡ k [ZMOD order] := by
  unfold components
  rw [eigenvalue_eq, lattice_identity _ _ _ _ _ lattice_determinant]
  exact Int.modEq_iff_dvd.mpr ⟨roundedQuotient (k * (a - 1)) -
    roundedQuotient (k * (-1)) * (2 - a), by ring⟩

/-- The negative numerator must not be interpreted using floor division. -/
theorem second_quotient_zero (k : Int) (hk : 0 ≤ k) (hkr : k < order) :
    roundedQuotient (k * (-1)) = 0 := by
  have hd : k.tdiv order = 0 := Int.tdiv_eq_zero_of_lt hk hkr
  have hn : (-k).tdiv order = 0 := by simp only [Int.neg_tdiv, hd, neg_zero]
  have hm : (-k).tmod order = -k := by rw [Int.tmod_def, hn]; ring
  unfold roundedQuotient roundDiv
  simp only [mul_neg_one, hn, hm]
  have hr := order_pos
  split_ifs <;> omega

theorem canonical_components (k : Int) (hk : 0 ≤ k) (hkr : k < order) :
    components k = (k - roundedQuotient (k * (a - 1)) * a,
      -roundedQuotient (k * (a - 1))) := by
  simp only [components, second_quotient_zero k hk hkr, zero_mul, add_zero, mul_one]

/-- Both output magnitudes fit the two-limb backend planned for the source adapter. -/
theorem component_bounds (k : Int) (hk : 0 ≤ k) (hkr : k < order) :
    -(2 ^ 128 : Int) < (components k).1 ∧ (components k).1 < 2 ^ 128 ∧
    -(2 ^ 128 : Int) < (components k).2 ∧ (components k).2 ≤ 0 := by
  rw [canonical_components k hk hkr]
  have ha : 0 ≤ a - 1 := by decide +kernel
  have hn := mul_nonneg hk ha
  have hd := Int.emod_nonneg (k * (a - 1)) (ne_of_gt order_pos)
  have hr := Int.emod_lt_of_pos (k * (a - 1)) order_pos
  have he := Int.emod_add_mul_ediv (k * (a - 1)) order
  unfold roundedQuotient roundDiv
  rw [Int.tdiv_eq_ediv_of_nonneg hn, Int.tmod_eq_emod_of_nonneg hn]
  simp only [a, order, Fr.modulus] at *
  split_ifs <;> omega

/-- num-bigint reports `Sign::Plus` only for strictly positive integers. -/
def signedMagnitude (k : Int) : Bool × Nat := (decide (0 < k), k.natAbs)

theorem signed_magnitude_value (k : Int) :
    (if (signedMagnitude k).1 then ((signedMagnitude k).2 : Int)
      else -((signedMagnitude k).2 : Int)) = k := by
  unfold signedMagnitude
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

/-- Conversion of either absolute value into Fr cannot change it. -/
theorem magnitude_bounds (k : Int) (hk : 0 ≤ k) (hkr : k < order) :
    (components k).1.natAbs < Fr.modulus ∧ (components k).2.natAbs < Fr.modulus := by
  have h := component_bounds k hk hkr
  have hsize : (2 ^ 128 : Int) < (Fr.modulus : Int) := by decide +kernel
  omega

/-- The decomposition is sufficient in any group killed by r, once the
endomorphism's subgroup eigenvalue relation has been established separately. -/
theorem group_reconstruction {G : Type*} [AddCommGroup G] (p : G) (k : Int)
    (hr : order • p = 0) :
    (components k).1 • p + (components k).2 • (eigenvalue • p) = k • p := by
  rcases (reconstruction k).dvd with ⟨q, hq⟩
  have hz : (k - ((components k).1 + eigenvalue * (components k).2)) • p = 0 := by
    rw [hq, mul_comm order q, mul_zsmul, hr, zsmul_zero]
  have he : ((components k).1 + eigenvalue * (components k).2) • p = k • p := by
    exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg, add_zsmul, neg_zsmul] using hz)).symm
  calc
    _ = ((components k).1 + eigenvalue * (components k).2) • p := by
      rw [add_zsmul, mul_comm eigenvalue _, mul_zsmul]
    _ = k • p := he

#print axioms lattice_determinant
#print axioms eigenvalue_eq
#print axioms order_pos
#print axioms reconstruction
#print axioms second_quotient_zero
#print axioms canonical_components
#print axioms component_bounds
#print axioms signed_magnitude_value
#print axioms magnitude_bounds
#print axioms group_reconstruction

end GLVDecomposition

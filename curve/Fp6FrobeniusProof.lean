import Fp6FieldProof
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.IntervalCases

open EthLib.Cryptography.Bls

namespace CubicFrobenius


private theorem ext (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- The first cubic Frobenius coefficient in the pinned arkworks table. -/
def eta : Fp2 := ⟨0,Fp.ofNat 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436⟩

private theorem base_power : (-4 : ZMod 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787)^333534129601805616118149152144658679713073568328250657111004844677002637540903155370223969094084638669824522713315 = 2001204777610833696312155217503344321967751559152793219135585697921485578740190688507702990026769679208567770469718 := by
  reduce_mod_char

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
local instance : CommRing Fp2 := QuadraticField.ringStructure

/-- The table coefficient is the actual nonresidue power, not a fitted constant. -/
theorem xi_power : Fp2.powNat CubicField.xi ((Fp.modulus-1)/3) = eta := by
  rw [QuadraticField.powNat_eq_pow]
  have hfour : CubicField.xi^4 = QuadraticField.ofFpHom (-4) := by
    apply ext <;> decide +kernel
  have he : (Fp.modulus-1)/3 = 4*((Fp.modulus-1)/3/4)+2 := by decide +kernel
  calc
    CubicField.xi^((Fp.modulus-1)/3) =
      CubicField.xi^(4*((Fp.modulus-1)/3/4)+2) := by rw [←he]
    _ = QuadraticField.ofFpHom ((-4 : Fp)^((Fp.modulus-1)/3/4))*CubicField.xi^2 := by
      rw [pow_add, pow_mul, hfour, ←map_pow]
    _ = eta := by
      have hb : (-4 : Fp)^((Fp.modulus-1)/3/4) = (2001204777610833696312155217503344321967751559152793219135585697921485578740190688507702990026769679208567770469718 : Fp) := by
        exact base_power
      rw [hb]
      apply ext <;> decide +kernel

/-- The six coefficients from arkworks' cubic Frobenius table. -/
def coefficient (k : Nat) : Fp2 :=
  match k%6 with
  | 0 => ⟨1,0⟩
  | 1 => eta
  | 2 => ⟨Fp.ofNat 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350,0⟩
  | 3 => ⟨0,1⟩
  | 4 => ⟨Fp.ofNat 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436,0⟩
  | _ => ⟨0,Fp.ofNat 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350⟩

private theorem coefficient_step_small (k : Nat) (hk : k < 6) :
    coefficient (k+1) = (coefficient k).conjugate*eta := by
  interval_cases k
  all_goals apply ext
  all_goals decide +kernel +revert

/-- The table follows the actual p-power recurrence, including its wraparound. -/
theorem coefficient_step (k : Nat) :
    coefficient (k+1) = (coefficient k).conjugate*eta := by
  have hnext : (k+1)%6 = (k%6+1)%6 := by omega
  have h := coefficient_step_small (k%6) (Nat.mod_lt _ (by decide))
  simpa only [coefficient, hnext, Nat.mod_mod] using h

/-- The source coefficient map on the cubic tower. -/
def map (a : Fp6) (k : Nat) : Fp6 :=
  ⟨Fp2.powNat a.c0 (Fp.modulus^k),
   Fp2.powNat a.c1 (Fp.modulus^k)*coefficient k,
   Fp2.powNat a.c2 (Fp.modulus^k)*(coefficient k*coefficient k)⟩

local instance : CommRing Fp6 := CubicField.ringStructure

private theorem cubic_ext (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl

/-- The coefficient map equals the full modulus power on all cubic-ring inputs. -/
theorem map_eq_power (a : Fp6) (k : Nat) : map a k = a^(Fp.modulus^k) := by
  induction k with
  | zero =>
    have hcoeff : coefficient 0 = (1 : Fp2) := rfl
    have hpower (x : Fp2) : Fp2.powNat x 1 = x := by
      rw [QuadraticField.powNat_eq_pow, pow_one]
    apply cubic_ext
    all_goals simp [map, hcoeff, hpower]
  | succ k ih =>
    rw [pow_succ, pow_mul, ←ih, CubicField.pow_modulus]
    unfold map CubicField.frobenius
    rw [xi_power, coefficient_step]
    apply cubic_ext
    · exact QuadraticField.power_step a.c0 k
    · rw [QuadraticField.power_step a.c1 k,
        QuadraticField.conjugate_mul (Fp2.powNat a.c1 (Fp.modulus^k)) (coefficient k)]
      dsimp only
      ring
    · rw [QuadraticField.power_step a.c2 k,
        QuadraticField.conjugate_mul (Fp2.powNat a.c2 (Fp.modulus^k)) (coefficient k*coefficient k),
        QuadraticField.conjugate_mul (coefficient k) (coefficient k)]
      dsimp only
      ring

#print axioms coefficient_step
#print axioms map_eq_power
#print axioms xi_power
end CubicFrobenius

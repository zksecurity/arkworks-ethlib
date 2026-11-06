import Fp12FieldProof
import Fp6FrobeniusProof

open EthLib.Cryptography.Bls

namespace DodecicFrobenius

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- The twelve coefficients from the pinned arkworks table. -/
def coefficient (k : Nat) : Fp2 :=
  match k%12 with
  | 0 => ⟨Fp.ofNat 1,Fp.ofNat 0⟩
  | 1 => ⟨Fp.ofNat 3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760,Fp.ofNat 151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027⟩
  | 2 => ⟨Fp.ofNat 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351,Fp.ofNat 0⟩
  | 3 => ⟨Fp.ofNat 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530,Fp.ofNat 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257⟩
  | 4 => ⟨Fp.ofNat 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350,Fp.ofNat 0⟩
  | 5 => ⟨Fp.ofNat 3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557,Fp.ofNat 877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230⟩
  | 6 => ⟨Fp.ofNat 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786,Fp.ofNat 0⟩
  | 7 => ⟨Fp.ofNat 151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027,Fp.ofNat 3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760⟩
  | 8 => ⟨Fp.ofNat 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436,Fp.ofNat 0⟩
  | 9 => ⟨Fp.ofNat 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257,Fp.ofNat 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530⟩
  | 10 => ⟨Fp.ofNat 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437,Fp.ofNat 0⟩
  | _ => ⟨Fp.ofNat 877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230,Fp.ofNat 3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557⟩

private theorem base_power : (-4 : ZMod 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787)^166767064800902808059074576072329339856536784164125328555502422338501318770451577685111984547042319334912261356657 = 2077032370203082887441716287710222127977479109453666665994032874817217438881019001906596280572484275092099519347407 := by
  reduce_mod_char

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
local instance : CommRing Fp2 := QuadraticField.ringStructure
local instance : CommRing Fp6 := CubicField.ringStructure
local instance : CommRing Fp12 := DodecicField.ringStructure

/-- The first table entry is the actual tower nonresidue power. -/
theorem xi_power : Fp2.powNat CubicField.xi ((Fp.modulus-1)/6) = coefficient 1 := by
  rw [QuadraticField.powNat_eq_pow]
  have hfour : CubicField.xi^4 = QuadraticField.ofFpHom (-4) := by
    apply ext2 <;> decide +kernel
  have he : (Fp.modulus-1)/6 = 4*((Fp.modulus-1)/6/4)+3 := by decide +kernel
  calc
    CubicField.xi^((Fp.modulus-1)/6) =
      CubicField.xi^(4*((Fp.modulus-1)/6/4)+3) := by rw [←he]
    _ = QuadraticField.ofFpHom ((-4 : Fp)^((Fp.modulus-1)/6/4))*CubicField.xi^3 := by
      rw [pow_add, pow_mul, hfour, ←map_pow]
    _ = coefficient 1 := by
      have hb : (-4 : Fp)^((Fp.modulus-1)/6/4) = (2077032370203082887441716287710222127977479109453666665994032874817217438881019001906596280572484275092099519347407 : Fp) := by exact base_power
      rw [hb]
      apply ext2 <;> decide +kernel

private theorem coefficient_step_small (k : Nat) (hk : k < 12) :
    coefficient (k+1) = (coefficient k).conjugate*coefficient 1 := by
  interval_cases k
  all_goals apply ext2
  all_goals decide +kernel +revert

/-- All table entries satisfy the p-power recurrence, including wraparound. -/
theorem coefficient_step (k : Nat) :
    coefficient (k+1) = (coefficient k).conjugate*coefficient 1 := by
  have hnext : (k+1)%12 = (k%12+1)%12 := by omega
  have h := coefficient_step_small (k%12) (Nat.mod_lt _ (by decide))
  simpa only [coefficient, hnext, Nat.mod_mod] using h

/-- The full coefficient map over unchanged EthLib arithmetic. -/
def map (a : Fp12) (k : Nat) : Fp12 :=
  ⟨a.c0^(Fp.modulus^k), a.c1^(Fp.modulus^k)*CubicField.ofFp2Hom (coefficient k)⟩

private theorem ext (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- The source coefficient map agrees with the pinned executable modulus power. -/
theorem map_eq_power (a : Fp12) (k : Nat) : map a k = Fp12.powNat a (Fp.modulus^k) := by
  rw [DodecicField.powNat_eq_pow]
  induction k with
  | zero =>
    have hcoeff : coefficient 0 = (1 : Fp2) := rfl
    apply ext
    all_goals simp [map, hcoeff]
  | succ k ih =>
    rw [pow_succ, pow_mul, ←ih, DodecicField.pow_modulus]
    unfold map DodecicField.frobenius
    rw [xi_power, coefficient_step]
    apply ext
    · simp only [pow_succ, pow_mul]
    · dsimp only
      rw [mul_pow, ←map_pow, ←QuadraticField.powNat_eq_pow, QuadraticField.pow_modulus,
        map_mul, pow_succ, pow_mul]
      ring

#print axioms xi_power
#print axioms coefficient_step
#print axioms map_eq_power
end DodecicFrobenius

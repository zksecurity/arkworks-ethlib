import CubicNonresidueProof
import Mathlib.RingTheory.AdjoinRoot

open EthLib.Cryptography.Bls

namespace CubicDomain

noncomputable section

noncomputable local instance : Field Fp2 := QuadraticDomain.fieldStructure
local instance : CommRing Fp6 := CubicField.ringStructure

/-- The defining polynomial for EthLib’s cubic tower. -/
def polynomial : Polynomial Fp2 :=
  Polynomial.X^3 - Polynomial.C CubicField.xi

local instance : Fact (Irreducible polynomial) := ⟨CubicNonresidue.irreducible⟩

private theorem root_relation :
    polynomial.eval₂ CubicField.ofFp2Hom Fp6.v = 0 := by
  simp only [polynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, CubicField.v_cube, sub_self]

private def evaluation : AdjoinRoot polynomial →+* Fp6 :=
  AdjoinRoot.lift CubicField.ofFp2Hom Fp6.v root_relation

private theorem ext6 (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl

private theorem evaluation_surjective : Function.Surjective evaluation := by
  intro a
  refine ⟨AdjoinRoot.of polynomial a.c0 +
    AdjoinRoot.of polynomial a.c1 * AdjoinRoot.root polynomial +
    AdjoinRoot.of polynomial a.c2 * AdjoinRoot.root polynomial^2, ?_⟩
  simp only [map_add, map_mul, map_pow, evaluation,
    AdjoinRoot.lift_of, AdjoinRoot.lift_root]
  apply ext6
  all_goals norm_num [pow_succ, Fp6.v]

local instance : Nontrivial Fp6 := ⟨⟨0, 1, by
  intro h
  have hc := congrArg (fun a : Fp6 => a.c0.c0) h
  have hn : Fp.zero ≠ Fp.one := by decide +kernel
  exact hn hc⟩⟩

/-- The executable cubic ring is the field defined by its irreducible polynomial. -/
noncomputable def quotientEquiv : AdjoinRoot polynomial ≃+* Fp6 :=
  RingEquiv.ofBijective evaluation ⟨evaluation.injective, evaluation_surjective⟩

/-- No zero divisors are introduced by the executable cubic representation. -/
abbrev domainStructure : IsDomain Fp6 := quotientEquiv.symm.toMulEquiv.isDomain _

attribute [local instance] domainStructure

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

local instance : Finite Fp2 := Finite.of_injective (fun a : Fp2 => (a.c0, a.c1)) (by
  intro a b h
  exact ext2 a b (congrArg Prod.fst h) (congrArg Prod.snd h))

local instance : Finite Fp6 :=
  Finite.of_injective (fun a : Fp6 => (a.c0, a.c1, a.c2)) (by
    intro a b h
    exact ext6 a b (congrArg Prod.fst h)
      (congrArg (fun p => p.2.1) h) (congrArg (fun p => p.2.2) h))

local instance : Fintype Fp6 := Fintype.ofFinite Fp6

/-- A field structure preserving the executable cubic ring arithmetic. -/
@[instance_reducible] def fieldStructure : Field Fp6 := by
  classical
  exact Fintype.fieldOfDomain Fp6

#print axioms fieldStructure
#print axioms quotientEquiv
#print axioms domainStructure
end
end CubicDomain

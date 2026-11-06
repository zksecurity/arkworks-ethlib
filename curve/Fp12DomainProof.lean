import DodecicNonresidueProof
import Mathlib.RingTheory.AdjoinRoot

open EthLib.Cryptography.Bls

namespace DodecicDomain

noncomputable section

noncomputable local instance : Field Fp6 := CubicDomain.fieldStructure
local instance : CommRing Fp12 := DodecicField.ringStructure

/-- The defining polynomial for EthLib’s degree-twelve tower. -/
def polynomial : Polynomial Fp6 :=
  Polynomial.X^2 - Polynomial.C Fp6.v

local instance : Fact (Irreducible polynomial) := ⟨DodecicNonresidue.irreducible⟩

private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

private theorem w_square : DodecicField.w^2 = DodecicField.ofFp6Hom Fp6.v := by
  apply ext12 <;> simp [DodecicField.w, pow_succ]

private theorem root_relation :
    polynomial.eval₂ DodecicField.ofFp6Hom DodecicField.w = 0 := by
  simp only [polynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, w_square, sub_self]

private def evaluation : AdjoinRoot polynomial →+* Fp12 :=
  AdjoinRoot.lift DodecicField.ofFp6Hom DodecicField.w root_relation

private theorem evaluation_surjective : Function.Surjective evaluation := by
  intro a
  refine ⟨AdjoinRoot.of polynomial a.c0 +
    AdjoinRoot.of polynomial a.c1 * AdjoinRoot.root polynomial, ?_⟩
  simp only [map_add, map_mul, evaluation,
    AdjoinRoot.lift_of, AdjoinRoot.lift_root]
  apply ext12
  all_goals simp [DodecicField.w]

local instance : Nontrivial Fp12 := ⟨⟨0, 1, by
  intro h
  have hc := congrArg (fun a : Fp12 => a.c0.c0.c0) h
  have hn : Fp.zero ≠ Fp.one := by decide +kernel
  exact hn hc⟩⟩

/-- The executable degree-twelve ring is the field defined by its irreducible polynomial. -/
noncomputable def quotientEquiv : AdjoinRoot polynomial ≃+* Fp12 :=
  RingEquiv.ofBijective evaluation ⟨evaluation.injective, evaluation_surjective⟩

/-- No zero divisors are introduced by the executable degree-twelve representation. -/
abbrev domainStructure : IsDomain Fp12 := quotientEquiv.symm.toMulEquiv.isDomain _

attribute [local instance] domainStructure

private theorem ext6 (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl

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

local instance : Finite Fp12 :=
  Finite.of_injective (fun a : Fp12 => (a.c0, a.c1)) (by
    intro a b h
    exact ext12 a b (congrArg Prod.fst h) (congrArg Prod.snd h))

local instance : Fintype Fp12 := Fintype.ofFinite Fp12

/-- A field structure preserving the executable degree-twelve ring arithmetic. -/
@[instance_reducible] def fieldStructure : Field Fp12 := by
  classical
  exact Fintype.fieldOfDomain Fp12

#print axioms fieldStructure
#print axioms quotientEquiv
#print axioms domainStructure
end
end DodecicDomain

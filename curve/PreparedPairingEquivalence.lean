import PreparedSafetyProof
import PreparedCoefficientWalkProof
import PreparedPairingProof

open EthLib.Cryptography.Bls
open PreparedCurve

namespace PreparedPairingEquivalence

noncomputable section
local instance : Field Fp2 := QuadraticDomain.fieldStructure
local instance : Field Fp6 := CubicDomain.fieldStructure
local instance : Field Fp12 := DodecicDomain.fieldStructure
local instance : Mul Fp12 := Fp12.instMul
local instance : DecidableEq Fp2 := Classical.decEq _
local instance : curve.IsElliptic := ellipticStructure

/-- Finite G2 inputs normalize to an on-curve point killed by the subgroup order.
Infinity inputs contribute the identity and need no affine witness. -/
def ValidG2 (q : G2) : Prop := q.isInfinity = false →
  ∃ hq : curve.toAffine.Equation q.toAffine.1 q.toAffine.2,
    Fr.modulus • affinePoint q.toAffine.1 q.toAffine.2 hq = 0

/-- The declared pairing input domain: every finite G2 input is in the mathematical subgroup. -/
def ValidInputs (pairs : List (G1 × G2)) : Prop := ∀ pq ∈ pairs, ValidG2 pq.2

private theorem untwist_g2 (q : G2) (hq : q.isInfinity = false) :
    PreparedLineGeometry.untwist ⟨q.toAffine.1,q.toAffine.2,Fp2.one⟩ = Embedded.ofG2 q := by
  simp only [PreparedLineGeometry.untwist, show Fp2.one = (1 : Fp2) from rfl, inv_one, mul_one, Embedded.ofG2, hq,
    Bool.false_eq_true, ite_false, PreparedLineGeometry.embed, RingHom.comp_apply]
  rfl

private theorem evaluation_g1 (p : G1) (hp : p.isInfinity = false) :
    PreparedMillerStep.evaluationPoint p.toAffine.1 p.toAffine.2 = Embedded.ofG1 p := by
  simp only [PreparedMillerStep.evaluationPoint, Embedded.ofG1, hp, Bool.false_eq_true,
    ite_false, PreparedLineGeometry.embed, RingHom.comp_apply]
  rfl

private theorem hom_one (x y : Fp2) :
    (⟨x,y,1⟩ : PreparedLine.Hom) = ⟨x,y,Fp2.one⟩ := rfl

/-- The exact source loop bit count matches the unchanged EthLib Miller loop. -/
theorem bit_count : blsX.log2 = 63 := by decide +kernel

/-- One finite prepared pair has the same final value as the unchanged EthLib Miller loop,
using an on-curve subgroup contract rather than per-step safety assumptions. -/
theorem finite_pair (p : G1) (q : G2) (hp : p.isInfinity = false) (hq : q.isInfinity = false)
    (hcurve : curve.toAffine.Equation q.toAffine.1 q.toAffine.2)
    (hr : Fr.modulus • affinePoint q.toAffine.1 q.toAffine.2 hcurve = 0) :
    finalExponentiation (PreparedChunkAlgebra.pairValue
      ⟨p.toAffine.1,p.toAffine.2,
        PreparedLine.prepare q.toAffine.1 q.toAffine.2 q.isInfinity⟩) =
      finalExponentiation (millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)) := by
  have hs := PreparedSafety.safe_affine q.toAffine.1 q.toAffine.2 hcurve hr
  simp only [hom_one] at hs
  have he := PreparedCoefficientWalk.chunk_refines_ethlib q.toAffine.1 q.toAffine.2
    p.toAffine.1 p.toAffine.2 63 ⟨q.toAffine.1,q.toAffine.2,Fp2.one⟩ Fp12.one hs
  simp only [untwist_g2 q hq, evaluation_g1 p hp] at he
  unfold PreparedChunkAlgebra.pairValue
  rw [PreparedLine.prepare]
  simp only [hq, Bool.false_eq_true, ite_false]
  rw [millerLoop, bit_count]
  exact he

private theorem filterMap_product {A B M : Type*} [Monoid M]
    (prepare : A → Option B) (value : B → M) (xs : List A) :
    ((xs.filterMap prepare).map value).prod =
      (xs.map (fun x => (prepare x).elim 1 value)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : prepare x
    all_goals simp only [List.filterMap_cons, hp, Option.elim_none, Option.elim_some,
      List.map_cons, List.prod_cons, one_mul, ih]

private theorem fold_product {A M : Type*} [Monoid M]
    (term : A → M) (step : M → A → M) (hstep : ∀ a x, step a x = a*term x)
    (xs : List A) (acc : M) : xs.foldl step acc = acc*(xs.map term).prod := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons x xs ih =>
    rw [List.foldl_cons, hstep, ih]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

private def contribution (pq : G1 × G2) : Fp12 :=
  (PreparedMiller.preparePair pq).elim Fp12.one PreparedChunkAlgebra.pairValue

private def finalHom : Fp12 →* Fp12 where
  toFun := finalExponentiation
  map_one' := FinalScaling.final_one
  map_mul' := FinalScaling.final_mul

private def finalConjugateHom : Fp12 →* Fp12 where
  toFun a := finalExponentiation a.conjugate
  map_one' := by rw [Cyclotomic.conjugate_one, FinalScaling.final_one]
  map_mul' a b := by rw [Cyclotomic.conjugate_mul, FinalScaling.final_mul]

private theorem one_eq : Fp12.one = (1 : Fp12) := rfl

private theorem contribution_final (pq : G1 × G2) (hq : ValidG2 pq.2) :
    finalConjugateHom (contribution pq) = finalHom (ConcretePairing.millerTerm pq.1 pq.2) := by
  change finalExponentiation (contribution pq).conjugate =
    finalExponentiation (ConcretePairing.millerTerm pq.1 pq.2)
  by_cases hi : (pq.1.isInfinity || pq.2.isInfinity) = true
  · simp only [contribution, PreparedMiller.preparePair, ConcretePairing.millerTerm,
      hi, ite_true, Option.elim_none]
    rw [one_eq, Cyclotomic.conjugate_one]
  · have hp : pq.1.isInfinity = false := by cases h : pq.1.isInfinity <;> simp_all
    have hqf : pq.2.isInfinity = false := by cases h : pq.2.isInfinity <;> simp_all
    obtain ⟨hcurve, hr⟩ := hq hqf
    simp only [contribution, PreparedMiller.preparePair, ConcretePairing.millerTerm,
      hi, Bool.false_eq_true, ite_false, Option.elim_some, FinalScaling.final_conjugate]
    rw [finite_pair pq.1 pq.2 hp hqf hcurve hr]

private theorem source_product (pairs : List (G1 × G2)) :
    ((PreparedMiller.prepareAll pairs).map PreparedChunkAlgebra.pairValue).prod =
      (pairs.map contribution).prod := filterMap_product _ _ pairs

private theorem reference_product (pairs : List (G1 × G2)) (acc : Fp12) :
    pairs.foldl ConcretePairing.pairingStep acc =
      acc*(pairs.map (fun pq => ConcretePairing.millerTerm pq.1 pq.2)).prod := by
  apply fold_product
  intro a pq
  unfold ConcretePairing.pairingStep ConcretePairing.millerTerm
  split_ifs <;> simp only [one_eq, mul_one]

private theorem source_final_product (pairs : List (G1 × G2)) :
    finalExponentiation (PreparedMiller.multiMiller pairs) =
      (pairs.map (fun pq => finalConjugateHom (contribution pq))).prod := by
  rw [PreparedMiller.multiMiller, PreparedChunkAlgebra.chunks_product]
  simp only [List.drop_zero, one_eq, one_mul]
  rw [source_product]
  change finalConjugateHom ((pairs.map contribution).prod) = _
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def]

private theorem reference_final_product (pairs : List (G1 × G2)) :
    finalExponentiation (pairs.foldl ConcretePairing.pairingStep Fp12.one) =
      (pairs.map (fun pq => finalHom (ConcretePairing.millerTerm pq.1 pq.2))).prod := by
  rw [reference_product, one_eq, one_mul]
  change finalHom ((pairs.map (fun pq => ConcretePairing.millerTerm pq.1 pq.2)).prod) = _
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def]

/-- The complete prepared source Miller schedule has the same final value as the
unchanged EthLib pairing-product loop on the declared mathematical subgroup domain. -/
theorem final_product (pairs : List (G1 × G2)) (hp : ValidInputs pairs) :
    finalExponentiation (PreparedMiller.multiMiller pairs) =
      finalExponentiation (pairs.foldl ConcretePairing.pairingStep Fp12.one) := by
  rw [source_final_product, reference_final_product]
  apply congrArg List.prod
  apply List.map_congr_left
  intro pq hn
  exact contribution_final pq (hp pq hn)

/-- The complete prepared pairing predicate agrees with unchanged EthLib pairingCheck
for finite G2 inputs that are on the twist and killed by the subgroup order. -/
theorem check_eq_ethlib (pairs : List (G1 × G2)) (hp : ValidInputs pairs) :
    PreparedMiller.check pairs = pairingCheck pairs.toArray := by
  rw [PreparedMiller.check, ConcretePairing.pairing_check_fold, final_product pairs hp]

#print axioms final_product
#print axioms check_eq_ethlib
#print axioms bit_count
#print axioms finite_pair
end
end PreparedPairingEquivalence

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace ConcretePreparedMiller

/-- The extracted prepared Rust endpoint terminates and agrees with unchanged EthLib
on canonical inputs whose finite G2 values satisfy the mathematical subgroup contract. -/
theorem pairing_check_ethlib_spec (pairs : Slice RawInput) (hp : ValidInputs pairs.val)
    (hg : PreparedPairingEquivalence.ValidInputs (decodeInputs pairs.val)) :
    CurveG1.pairing.prepared_miller.pairing_check pairs ⦃ r =>
      r = pairingCheck (decodeInputs pairs.val).toArray ⦄ := by
  apply spec_mono (pairing_check_spec pairs hp)
  intro r hr
  exact hr.trans (PreparedPairingEquivalence.check_eq_ethlib _ hg)

/-- The default extracted Rust endpoint uses the proved prepared path directly. -/
theorem default_pairing_check_ethlib_spec (pairs : Slice RawInput) (hp : ValidInputs pairs.val)
    (hg : PreparedPairingEquivalence.ValidInputs (decodeInputs pairs.val)) :
    CurveG1.pairing.pairing_check pairs ⦃ r =>
      r = pairingCheck (decodeInputs pairs.val).toArray ⦄ := by
  unfold CurveG1.pairing.pairing_check
  exact pairing_check_ethlib_spec pairs hp hg

#print axioms default_pairing_check_ethlib_spec
#print axioms pairing_check_ethlib_spec
end ConcretePreparedMiller

import PreparedMillerProof
import Fp12DomainProof

open EthLib.Cryptography.Bls

namespace PreparedChunkAlgebra

noncomputable local instance : Field Fp12 := DodecicDomain.fieldStructure
local instance : Mul Fp12 := Fp12.instMul

private theorem chunk_zero (pairs : List PreparedMiller.Pair) (line : Nat) (f : Fp12) :
    PreparedMiller.chunk pairs 0 line f = f := by
  rw [PreparedMiller.chunk]
  simp only [dite_true]

private theorem chunk_succ (pairs : List PreparedMiller.Pair) (bits line : Nat) (f : Fp12) :
    PreparedMiller.chunk pairs (bits+1) line f =
      let fd := PreparedMiller.evalLines pairs line (f*f)
      if (CurveG1.pairing.BLS_X.val >>> bits)%2 = 1 then
        PreparedMiller.chunk pairs bits (line+1+1) (PreparedMiller.evalLines pairs (line+1) fd)
      else PreparedMiller.chunk pairs bits (line+1) fd := by
  rw [PreparedMiller.chunk]
  simp only [Nat.succ_ne_zero, Nat.add_one_sub_one, dite_false]

private theorem fold_scale {M : Type*} [CommMonoid M] (xs : List M) (a b : M) :
    xs.foldl (fun f c => f*c) (a*b) = a*xs.foldl (fun f c => f*c) b := by
  induction xs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [mul_assoc, ih]

private theorem eval_fold (pairs : List PreparedMiller.Pair) (line : Nat) (f : Fp12) :
    PreparedMiller.evalLines pairs line f =
      (pairs.map (fun p => PreparedMiller.lineValue (PreparedMiller.coeffAt p line) p.px p.py)).foldl
        Fp12.mul f := by
  induction pairs generalizing f with
  | nil => rfl
  | cons p ps ih =>
    simp only [PreparedMiller.evalLines, List.map_cons, List.foldl_cons]
    exact ih _

private theorem eval_scale (pairs : List PreparedMiller.Pair) (line : Nat) (a b : Fp12) :
    PreparedMiller.evalLines pairs line (a*b) = a*PreparedMiller.evalLines pairs line b := by
  rw [eval_fold, eval_fold]
  exact fold_scale _ a b

private theorem eval_append (left right : List PreparedMiller.Pair) (line : Nat) (f : Fp12) :
    PreparedMiller.evalLines (left++right) line f =
      PreparedMiller.evalLines right line (PreparedMiller.evalLines left line f) := by
  induction left generalizing f with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.cons_append, PreparedMiller.evalLines]
    exact ih _

/-- Evaluating all lines distributes over splitting the pair list and the accumulator. -/
theorem eval_append_product (left right : List PreparedMiller.Pair) (line : Nat) (a b : Fp12) :
    PreparedMiller.evalLines (left++right) line (a*b) =
      PreparedMiller.evalLines left line a * PreparedMiller.evalLines right line b := by
  rw [eval_append, mul_comm a b, eval_scale,
    mul_comm b (PreparedMiller.evalLines left line a), eval_scale]

/-- Shared squaring and line evaluation give exactly the product of two independent chunks. -/
theorem chunk_append_product (left right : List PreparedMiller.Pair) (bits line : Nat) (a b : Fp12) :
    PreparedMiller.chunk (left++right) bits line (a*b) =
      PreparedMiller.chunk left bits line a * PreparedMiller.chunk right bits line b := by
  induction bits generalizing line a b with
  | zero => simp only [chunk_zero]
  | succ bits ih =>
    simp only [chunk_succ]
    rw [show (a*b)*(a*b) = (a*a)*(b*b) by ring, eval_append_product]
    split_ifs
    · rw [eval_append_product, ih]
    · rw [ih]

private theorem chunk_empty_one (bits line : Nat) :
    PreparedMiller.chunk [] bits line (1 : Fp12) = 1 := by
  induction bits generalizing line with
  | zero => simp only [chunk_zero]
  | succ bits ih =>
    simp only [chunk_succ, PreparedMiller.evalLines, one_mul]
    split_ifs <;> exact ih _

/-- A shared chunk is the exact raw product of its single-pair chunks. -/
theorem chunk_product (pairs : List PreparedMiller.Pair) (bits line : Nat) :
    PreparedMiller.chunk pairs bits line (1 : Fp12) =
      (pairs.map (fun p => PreparedMiller.chunk [p] bits line 1)).prod := by
  induction pairs with
  | nil => simpa only [List.map_nil, List.prod_nil] using chunk_empty_one bits line
  | cons p ps ih =>
    have h := chunk_append_product [p] ps bits line 1 1
    simpa only [List.singleton_append, one_mul, List.map_cons, List.prod_cons, ih] using h

/-- The value associated with one prepared pair before the negative-parameter conjugation. -/
def pairValue (p : PreparedMiller.Pair) : Fp12 := PreparedMiller.chunk [p] 63 0 Fp12.one

/-- Four-pair batching is exactly the raw product of all independent prepared pair values. -/
theorem chunks_product (pairs : List PreparedMiller.Pair) (start : Nat) (acc : Fp12) :
    PreparedMiller.chunks pairs start acc =
      acc*((pairs.drop start).map pairValue).prod := by
  by_cases hs : start < pairs.length
  · let stop := if pairs.length-start > 4 then start+4 else pairs.length
    let window := (pairs.drop start).take (stop-start)
    have hprogress : start < stop := by dsimp only [stop]; split_ifs <;> omega
    have hbound : stop ≤ pairs.length := by dsimp only [stop]; split_ifs <;> omega
    have hsplit : pairs.drop start = window ++ pairs.drop stop := by
      have h := (List.take_append_drop (stop-start) (pairs.drop start)).symm
      have he : start+(stop-start) = stop := by omega
      simpa only [List.drop_drop, he] using h
    rw [PreparedMiller.chunks]
    simp only [hs, dite_true]
    change PreparedMiller.chunks pairs stop (acc*PreparedMiller.chunk window 63 0 Fp12.one) = _
    rw [chunks_product pairs stop (acc*PreparedMiller.chunk window 63 0 Fp12.one)]
    have hw : PreparedMiller.chunk window 63 0 Fp12.one = (window.map pairValue).prod :=
      chunk_product window 63 0
    rw [hw, hsplit, List.map_append, List.prod_append, mul_assoc]
  · rw [PreparedMiller.chunks]
    simp only [hs, dite_false, List.drop_eq_nil_of_le (Nat.le_of_not_gt hs),
      List.map_nil, List.prod_nil, mul_one]
termination_by pairs.length-start
decreasing_by
  split_ifs <;> omega

#print axioms chunks_product
#print axioms eval_append_product
#print axioms chunk_append_product
#print axioms chunk_product
end PreparedChunkAlgebra

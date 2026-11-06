import PreparedProjectiveProof
import CyclotomicExponentRefinement

open EthLib.Cryptography.Bls

namespace PreparedMiller

structure Pair where
  px : Fp
  py : Fp
  coeffs : List PreparedLine.Coeff

def coeffAt (p : Pair) (i : Nat) : PreparedLine.Coeff :=
  p.coeffs[i]?.getD ⟨Fp2.zero,Fp2.zero,Fp2.zero⟩

def lineValue (c : PreparedLine.Coeff) (px py : Fp) : Fp12 :=
  ExtensionAlignment.sparseElement014 c.c0 (c.c1*Fp2.ofFp px) (c.c2*Fp2.ofFp py)

/-- One source line position, in pair order across a chunk. -/
def evalLines (pairs : List Pair) (line : Nat) (f : Fp12) : Fp12 :=
  match pairs with
  | [] => f
  | p::ps => evalLines ps line (f*lineValue (coeffAt p line) p.px p.py)

/-- Squaring is shared by a chunk; each bit consumes the next one or two lines. -/
def chunk (pairs : List Pair) (bits line : Nat) (f : Fp12) : Fp12 :=
  if h : bits = 0 then f else
    let bit := bits-1
    let f := evalLines pairs line (f*f)
    let line := line+1
    if (CurveG1.pairing.BLS_X.val >>> bit)%2 = 1 then
      chunk pairs bit (line+1) (evalLines pairs line f)
    else chunk pairs bit line f
termination_by bits
decreasing_by all_goals omega

/-- Source product of four-active-pair chunks, retaining the initial identity factor. -/
def chunks (pairs : List Pair) (start : Nat) (acc : Fp12) : Fp12 :=
  if _h : start < pairs.length then
    let stop := if pairs.length-start > 4 then start+4 else pairs.length
    let f := chunk ((pairs.drop start).take (stop-start)) 63 0 Fp12.one
    chunks pairs stop (acc*f)
  else acc
termination_by pairs.length-start
decreasing_by all_goals dsimp; split_ifs <;> omega

/-- Both source conversions happen before the infinity filter. -/
def preparePair (pq : G1 × G2) : Option Pair :=
  if pq.1.isInfinity || pq.2.isInfinity then none else
    some ⟨(pq.1.toAffine).1,(pq.1.toAffine).2,
      PreparedLine.prepare (pq.2.toAffine).1 (pq.2.toAffine).2 pq.2.isInfinity⟩

def prepareAll (pairs : List (G1 × G2)) : List Pair := pairs.filterMap preparePair

/-- Complete sequential prepared Miller schedule with the fixed negative-X convention. -/
def multiMiller (pairs : List (G1 × G2)) : Fp12 :=
  (chunks (prepareAll pairs) 0 Fp12.one).conjugate

end PreparedMiller

open Aeneas Aeneas.Std Aeneas.Std.WP
open ConcreteField ConcreteCurve ConcreteExtension ConcretePreparedLine ConcretePreparedG2

namespace ConcretePreparedMiller

abbrev RawPair := CurveG1.pairing.prepared_miller.PreparedPair

def ValidPair (p : RawPair) : Prop :=
  FieldProof.Valid p.p.x ∧ FieldProof.Valid p.p.y ∧ ValidCoeffs p.q.ell_coeffs.val ∧
  p.q.ell_coeffs.val.length = 68

def ValidPairs (ps : List RawPair) : Prop := ∀ p ∈ ps, ValidPair p

def decodePair (p : RawPair) : PreparedMiller.Pair :=
  ⟨decode p.p.x,decode p.p.y,decodeCoeffs p.q.ell_coeffs.val⟩

def decodePairs (ps : List RawPair) : List PreparedMiller.Pair := ps.map decodePair

private theorem coefficient_decode (p : RawPair) (hp : ValidPair p) (i : Nat) (hi : i < 68) :
    PreparedMiller.coeffAt (decodePair p) i =
      decodeCoeff (p.q.ell_coeffs.val[i]'(by rw [hp.2.2.2]; exact hi)) := by
  have hb : i < p.q.ell_coeffs.val.length := by rw [hp.2.2.2]; exact hi
  simp [PreparedMiller.coeffAt, decodePair, decodeCoeffs, hb]

private theorem window_cons {α : Type} (xs : List α) (i e : Nat) (hi : i < e) (he : e ≤ xs.length) :
    (xs.drop i).take (e-i) = xs[i]'(by omega) :: (xs.drop (i+1)).take (e-(i+1)) := by
  rw [List.drop_eq_getElem_cons (i := i) (by omega)]
  rw [show e-i = (e-(i+1))+1 by omega]
  rfl

/-- Each line read is in bounds and the extracted traversal follows the source pair order. -/
@[step] theorem eval_lines_spec (pairs : Slice RawPair) (index stop line : Usize) (f : Raw12)
    (hp : ValidPairs pairs.val) (hi : index.val ≤ stop.val) (he : stop.val ≤ pairs.length)
    (hl : line.val < 68) (hf : Valid12 f) :
    CurveG1.pairing.prepared_miller.eval_lines pairs index stop line f ⦃ r =>
      Valid12 r ∧ decode12 r = PreparedMiller.evalLines
        (decodePairs ((pairs.val.drop index.val).take (stop.val-index.val))) line.val (decode12 f) ⦄ := by
  by_cases heq : index = stop
  · rw [CurveG1.pairing.prepared_miller.eval_lines]
    simp_all [decodePairs, PreparedMiller.evalLines]
  · have hlt : index.val < stop.val := by scalar_tac
    have hib : index.val < pairs.val.length := by scalar_tac
    have hc := hp pairs.val[index.val] (List.getElem_mem hib)
    have hcl : line.val < pairs.val[index.val].q.ell_coeffs.val.length := by rw [hc.2.2.2]; exact hl
    have hv := hc.2.2.1 _ (List.getElem_mem hcl)
    have hd := coefficient_decode pairs.val[index.val] hc line.val hl
    have hx := hc.1
    have hy := hc.2.1
    rw [CurveG1.pairing.prepared_miller.eval_lines]
    simp only [ite_eq_right heq]
    step*
    rw [window_cons pairs.val index.val stop.val hlt he]
    simp_all [decodePairs, PreparedMiller.evalLines, PreparedMiller.lineValue, decodePair, decodeCoeff]
termination_by stop.val-index.val
decreasing_by all_goals scalar_tac

/-- The extracted bit driver consumes all 68 coefficients in order without out-of-bounds reads. -/
@[step] theorem chunk_bits_spec (pairs : Slice RawPair) (start stop : Usize) (bits : U32)
    (line : Usize) (f : Raw12) (hp : ValidPairs pairs.val)
    (hi : start.val ≤ stop.val) (he : stop.val ≤ pairs.length) (hb : bits.val ≤ 63)
    (hl : line.val + PreparedLine.remainingLines bits.val = 68) (hf : Valid12 f) :
    CurveG1.pairing.prepared_miller.chunk_bits pairs start stop bits line f ⦃ r =>
      Valid12 r ∧ decode12 r = PreparedMiller.chunk
        (decodePairs ((pairs.val.drop start.val).take (stop.val-start.val))) bits.val line.val (decode12 f) ⦄ := by
  by_cases hz : bits = 0#u32
  · rw [CurveG1.pairing.prepared_miller.chunk_bits, PreparedMiller.chunk]
    simp_all
  · have hpos : 0 < bits.val := by scalar_tac
    have hn : bits.val ≠ 0 := by omega
    have hs := PreparedLine.remaining_step bits.val hpos
    have hc := PreparedLine.remaining_positive bits.val hpos
    by_cases hbit : (CurveG1.pairing.BLS_X.val >>> (bits.val-1))%2 = 1
    all_goals rw [CurveG1.pairing.prepared_miller.chunk_bits, PreparedMiller.chunk]
    all_goals step*
    all_goals simp_all [CurveG1.pairing.BLS_X, Nat.and_one_is_mod]
    all_goals step*
    all_goals (try (split <;> step*))
termination_by bits.val
decreasing_by all_goals scalar_tac

/-- Chunk boundaries and the initial product factor follow arkworks' sequential schedule. -/
@[step] theorem chunks_spec (pairs : Slice RawPair) (start : Usize) (acc : Raw12)
    (hp : ValidPairs pairs.val) (hi : start.val ≤ pairs.length) (ha : Valid12 acc) :
    CurveG1.pairing.prepared_miller.chunks pairs start acc ⦃ r =>
      Valid12 r ∧ decode12 r = PreparedMiller.chunks (decodePairs pairs.val) start.val (decode12 acc) ⦄ := by
  have hc := PreparedLine.remaining_full
  by_cases heq : start = Slice.len pairs
  · rw [CurveG1.pairing.prepared_miller.chunks, PreparedMiller.chunks]
    simp_all [decodePairs]
  · have hlt : start.val < pairs.length := by scalar_tac
    rw [CurveG1.pairing.prepared_miller.chunks, PreparedMiller.chunks]
    simp only [ite_eq_right heq]
    step*
    all_goals (try (split <;> step*))
    all_goals simp_all [decodePairs, List.map_take, List.map_drop]
    all_goals (split_ifs <;> (try simp_all); omega)
termination_by pairs.length-start.val
decreasing_by all_goals scalar_tac

abbrev RawInput := RawPoint × RawG2

def ValidInputs (ps : List RawInput) : Prop :=
  ∀ p ∈ ps, ValidPoint p.1 ∧ ValidG2 p.2

def decodeInputs (ps : List RawInput) : List (G1 × G2) :=
  ps.map (fun p => (decodePoint p.1,decodeG2 p.2))

@[local step] private theorem push_pair_spec (ps : alloc.vec.Vec RawPair) (p : RawPair)
    (hs : ValidPairs ps.val) (hp : ValidPair p) (hb : ps.val.length < Usize.max) :
    alloc.vec.Vec.push ps p ⦃ out => out.val = ps.val ++ [p] ∧ ValidPairs out.val ⦄ := by
  apply spec_mono (alloc.vec.Vec.push_spec ps p hb)
  rintro out he
  refine ⟨he,?_⟩
  rw [he]
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hs q hq
  · simp only [List.mem_singleton] at hq
    subst q
    exact hp

/-- Source preparation/filtering preserves canonicality, vector bounds, and pair order. -/
@[step] theorem collect_spec (pairs : Slice RawInput) (index : Usize) (active : alloc.vec.Vec RawPair)
    (hp : ValidInputs pairs.val) (hi : index.val ≤ pairs.length)
    (ha : ValidPairs active.val) (hb : active.val.length ≤ index.val) :
    CurveG1.pairing.prepared_miller.collect pairs index active ⦃ out =>
      ValidPairs out.val ∧ out.val.length ≤ active.val.length+pairs.length-index.val ∧
      decodePairs out.val = decodePairs active.val ++
        PreparedMiller.prepareAll (decodeInputs (pairs.val.drop index.val)) ⦄ := by
  by_cases heq : index = Slice.len pairs
  · rw [CurveG1.pairing.prepared_miller.collect]
    simp_all [decodePairs, decodeInputs, PreparedMiller.prepareAll]
  · have hlt : index.val < pairs.length := by scalar_tac
    have hcur := hp pairs.val[index.val] (List.getElem_mem hlt)
    rcases hcur with ⟨hpx,hqy⟩
    rw [CurveG1.pairing.prepared_miller.collect]
    simp only [ite_eq_right heq]
    step*
    rcases p with ⟨rawp,rawq⟩
    step*
    all_goals (try (split <;> step*))
    all_goals (try (split <;> step*))
    all_goals
      have hpxy0 := congrArg Prod.fst p2_post2
      have hpxy1 := congrArg Prod.snd p2_post2
    all_goals (try simp_all [ValidPair])
    all_goals rw [List.drop_eq_getElem_cons (i := index.val) hlt, ←p_post]
    all_goals clear p_post
    all_goals simp_all [decodePairs, decodeInputs, decodePair, PreparedMiller.prepareAll,
      PreparedMiller.preparePair, List.append_assoc]
    all_goals scalar_tac
termination_by pairs.length-index.val
decreasing_by all_goals scalar_tac

@[simp] private theorem deref_val (v : alloc.vec.Vec RawPair) : v.deref.val = v.val := by
  simp [alloc.vec.Vec.deref]

/-- The complete extracted prepared Miller pipeline terminates and refines its source field schedule. -/
@[step] theorem multi_miller_loop_spec (pairs : Slice RawInput) (hp : ValidInputs pairs.val) :
    CurveG1.pairing.prepared_miller.multi_miller_loop pairs ⦃ r =>
      Valid12 r ∧ decode12 r = PreparedMiller.multiMiller (decodeInputs pairs.val) ⦄ := by
  have hn : ValidPairs [] := by simp [ValidPairs]
  unfold CurveG1.pairing.prepared_miller.multi_miller_loop
  step*
  all_goals simp_all [PreparedMiller.multiMiller, decodePairs]

#print axioms eval_lines_spec
#print axioms chunk_bits_spec
#print axioms chunks_spec
#print axioms collect_spec
#print axioms multi_miller_loop_spec
end ConcretePreparedMiller

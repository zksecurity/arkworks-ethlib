import PointProof

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof ConcreteField ConcreteCurve ConcreteEncoding ConcretePoints

namespace ConcreteRecovery

/-- The same sign comparison expressed using the canonical additive inverse. -/
theorem sign_inverse (y : Fp) : Fp.signBit y = decide ((-y).val < y.val) := by
  by_cases hz : y = 0
  · simp [hz, Fp.signBit]
  · simp only [Fp.signBit, Fin.val_neg, hz, ↓reduceIte]

theorem select_sorted (y : Fp) (greatest : Bool) :
    (if y.val < (-y).val then (if greatest then -y else y)
      else (if greatest then y else -y)) =
      (if Fp.signBit y = greatest then y else -y) := by
  rw [sign_inverse]
  cases greatest <;> simp only [Bool.false_eq_true, ↓reduceIte,
    decide_eq_false_iff_not, decide_eq_true_eq]
  all_goals split_ifs <;> first | rfl | (apply Fin.ext; omega)

def decodeYs (ys : Raw × Raw) : Fp × Fp := (decode ys.1, decode ys.2)

def ysSpec (x : Fp) : Option (Fp × Fp) :=
  (Fp.sqrt (x * x * x + Fp.ofNat 4)).toOption.map fun y =>
    if y.val < (-y).val then (y, -y) else (-y, y)

@[step] theorem ys_spec (x : Raw) (hx : Valid x) :
    CurveG1.decoder.ys_from_x_unchecked x ⦃ out =>
      (∀ ys, out = some ys → Valid ys.1 ∧ Valid ys.2) ∧
      out.map decodeYs = ysSpec (decode x) ⦄ := by
  have hb := ConcreteField.curve_b_canonical
  unfold CurveG1.decoder.ys_from_x_unchecked
  step*
  all_goals
    have hrhs : decode rhs = decode x * decode x * decode x + Fp.ofNat 4 := by
      rw [rhs_post1, f1_post1, f_post1, hb.2]
    simp only [ysSpec, ← hrhs, ← o_post]
    clear o_post
  all_goals try simp only [← decode_val] at a_post a1_post
  all_goals simp_all [decodeYs, -Fin.val_fin_lt]


def recoverSpec (x : Fp) (greatest : Bool) : Option G1 :=
  (Fp.sqrt (x * x * x + Fp.ofNat 4)).toOption.map fun y =>
    ⟨x, if Fp.signBit y = greatest then y else -y, Fp.one⟩

private theorem recover_sorted (x : Fp) (greatest : Bool) :
    (ysSpec x).map (fun ys => (⟨x, if greatest then ys.2 else ys.1, Fp.one⟩ : G1)) =
      recoverSpec x greatest := by
  unfold ysSpec recoverSpec
  rw [Option.map_map]
  congr 1
  funext y
  by_cases hl : y.val < (-y).val
  all_goals simpa only [Function.comp_apply, hl, ↓reduceIte] using
    congrArg (fun z : Fp => (⟨x, z, Fp.one⟩ : G1)) (select_sorted y greatest)

@[step] theorem point_spec (x : Raw) (greatest : Bool) (hx : Valid x) :
    CurveG1.decoder.point_from_x_unchecked x greatest ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = recoverSpec (decode x) greatest ⦄ := by
  unfold CurveG1.decoder.point_from_x_unchecked
  step*
  all_goals rw [← recover_sorted, ← o_post1]
  all_goals clear o_post1
  · simp_all [CanonicalResult]
  · rcases p with ⟨smaller, larger⟩
    have hv := o_post (smaller, larger) (by assumption)
    split <;> step*
    all_goals
      have hone : Fp.ofNat 1 = Fp.one := by decide +kernel
      simp_all [CanonicalResult, ValidPoint, decodePoint, decodeYs]


private theorem sign_decide (b : Bool) (p : Prop) [Decidable p] :
    (b = decide p) ↔ ((b = true) ↔ p) := by
  cases b <;> by_cases hp : p <;> simp_all

/-- Match the proposition-valued sign test in EthLib without unfolding a concrete field value. -/
theorem recover_prop (x : Fp) (sign : Prop) [Decidable sign] :
    recoverSpec x (decide sign) =
      (match Fp.sqrt (x * x * x + Fp.ofNat 4) with
      | .error _ => Except.error BlsError.invalidG1Point
      | .ok root => Except.ok (⟨x, if (Fp.signBit root = true) ↔ sign then root else -root, Fp.one⟩ : G1)).toOption := by
  unfold recoverSpec
  cases h : Fp.sqrt (x * x * x + Fp.ofNat 4) <;> simp only [Except.toOption, Option.map_none, Option.map_some]
  simp only [sign_decide]

def uncompressSpec (bytes : ByteArray) : Option G1 :=
  if bytes.size ≠ 48 then none
  else if bytes.get! 0 &&& 128 = 0 then none
  else if bytes.get! 0 &&& 64 ≠ 0 then
    if (bytes.get! 0 &&& 32 ≠ 0) || bytes.get! 0 ≠ 192 || !tailAllZero bytes 1
    then none else some G1.zero
  else
    (Fp.fromBytesBE (bytes.set! 0 (bytes.get! 0 &&& 31))).toOption.bind fun x =>
      recoverSpec x (decide (bytes.get! 0 &&& 32 ≠ 0))

theorem uncompress_correct (bytes : ByteArray) :
    uncompressSpec bytes = (G1.uncompress bytes).toOption := by
  unfold uncompressSpec G1.uncompress
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, ne_eq, not_not]
  split_ifs <;> try rfl
  all_goals cases hf : Fp.fromBytesBE (bytes.set! 0 (bytes.get! 0 &&& 31))
  all_goals simp only [Except.toOption, Option.bind_none, Option.bind_some, eq_iff_iff]
  exact recover_prop _ (bytes.get! 0 &&& 32 ≠ 0)

#print axioms sign_inverse
#print axioms select_sorted
#print axioms ys_spec
#print axioms point_spec
end ConcreteRecovery

namespace ConcretePoints

@[step] theorem from_x_spec (x : Raw) (sign : Bool) (hx : FieldProof.Valid x) :
    CurveG1.field.from_x x sign ⦃ result =>
      CanonicalResult result ∧ result.map decodePoint = fromXSpec (decode x) sign ⦄ := by
  simpa only [CurveG1.field.from_x, fromXSpec, ConcreteRecovery.recoverSpec] using
    ConcreteRecovery.point_spec x sign hx

#print axioms from_x_spec
end ConcretePoints

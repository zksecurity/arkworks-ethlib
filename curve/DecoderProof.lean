import DecoderCurveProof
import RecoveryProof
import Mathlib.Tactic.IntervalCases
import ArkEth.Spec

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls
open FieldProof ConcreteField ConcreteCurve ConcreteEncoding ConcretePoints ConcreteRecovery

namespace ConcreteDecoder

@[step] theorem word_spec (a b c d e f g h : U8) :
    CurveG1.decoder.word a b c d e f g h ⦃ out =>
      out.val = ((((((a.val * 256 + b.val) * 256 + c.val) * 256 + d.val) * 256 +
        e.val) * 256 + f.val) * 256 + g.val) * 256 + h.val ⦄ := by
  unfold CurveG1.decoder.word
  step*

@[step] theorem from_limbs_spec (a : Limbs) :
    CurveG1.field.Fp.from_limbs a ⦃ out =>
      (∀ f, out = some f → Valid f) ∧
      out.map decode = if value a < Fp.modulus then some (Fp.ofNat (value a)) else none ⦄ := by
  apply spec_mono (FieldProof.from_limbs_spec a)
  rintro out ⟨hvalid, hvalue⟩
  refine ⟨hvalid, ?_⟩
  cases out with
  | none => simpa using hvalue
  | some f =>
    split_ifs at hvalue with h
    · simp only [Option.map_some, Option.some.injEq] at hvalue
      simp only [Option.map_some, ite_eq_left h, Option.some.injEq, decode, hvalue]
      apply Fin.ext
      simpa only [Fp.ofNat, Fin.val_ofNat, Nat.mod_mul_mod] using
        MontgomeryConversion.radix_shift (value a)
    · simp at hvalue

@[simp] theorem byte_value (b : U8) : (byte b).toNat = b.val := by rfl

theorem bytes_list (bytes : Bytes48) : bytes.val = [bytes[0]!, bytes[1]!, bytes[2]!, bytes[3]!, bytes[4]!, bytes[5]!, bytes[6]!, bytes[7]!, bytes[8]!, bytes[9]!, bytes[10]!, bytes[11]!, bytes[12]!, bytes[13]!, bytes[14]!, bytes[15]!, bytes[16]!, bytes[17]!, bytes[18]!, bytes[19]!, bytes[20]!, bytes[21]!, bytes[22]!, bytes[23]!, bytes[24]!, bytes[25]!, bytes[26]!, bytes[27]!, bytes[28]!, bytes[29]!, bytes[30]!, bytes[31]!, bytes[32]!, bytes[33]!, bytes[34]!, bytes[35]!, bytes[36]!, bytes[37]!, bytes[38]!, bytes[39]!, bytes[40]!, bytes[41]!, bytes[42]!, bytes[43]!, bytes[44]!, bytes[45]!, bytes[46]!, bytes[47]!] := by
  apply List.ext_getElem
  · simp only [Array.length_eq]
    rfl
  · intro i hi hj
    have hlen : bytes.val.length = 48 := by rw [Array.length_eq]; rfl
    have h : i < 48 := by simpa only [hlen] using hi
    interval_cases i <;> simp [Array.getElem!_Nat_eq]

def beValue (bytes : Bytes48) : Nat := bytes.val.foldl (fun n b => n * 256 + b.val) 0

theorem shift_or_byte (n : Nat) (b : U8) :
    (n <<< 8) ||| b.val = n * 256 + b.val := by
  have hb : b.val < 2^8 := by scalar_tac
  simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.mul_comm] using
    (Nat.two_pow_add_eq_or_of_lt hb n).symm

set_option maxRecDepth 4096 in
theorem bytes_nat (bytes : Bytes48) : Fp.bytesBEToNat (observe bytes) = beValue bytes := by
  conv_lhs => unfold observe; rw [bytes_list]
  conv_rhs => unfold beValue; rw [bytes_list]
  simp [Fp.bytesBEToNat, ByteArray.size, -ByteArray.size_data, shift_or_byte, List.range'_succ, getElem!_pos, ByteArray.getElem_eq_getElem_data]

def wordValue (a b c d e f g h : U8) : Nat :=
  ((((((a.val * 256 + b.val) * 256 + c.val) * 256 + d.val) * 256 + e.val) * 256 + f.val) * 256 + g.val) * 256 + h.val

def packedValue (bytes : Bytes48) : Nat :=
  (wordValue bytes[40]! bytes[41]! bytes[42]! bytes[43]! bytes[44]! bytes[45]! bytes[46]! bytes[47]!) +
  B^1 * (wordValue bytes[32]! bytes[33]! bytes[34]! bytes[35]! bytes[36]! bytes[37]! bytes[38]! bytes[39]!) +
  B^2 * (wordValue bytes[24]! bytes[25]! bytes[26]! bytes[27]! bytes[28]! bytes[29]! bytes[30]! bytes[31]!) +
  B^3 * (wordValue bytes[16]! bytes[17]! bytes[18]! bytes[19]! bytes[20]! bytes[21]! bytes[22]! bytes[23]!) +
  B^4 * (wordValue bytes[8]! bytes[9]! bytes[10]! bytes[11]! bytes[12]! bytes[13]! bytes[14]! bytes[15]!) +
  B^5 * (wordValue bytes[0]! bytes[1]! bytes[2]! bytes[3]! bytes[4]! bytes[5]! bytes[6]! bytes[7]!)

set_option maxRecDepth 4096 in
theorem packed_value (bytes : Bytes48) : packedValue bytes = beValue bytes := by
  unfold beValue
  rw [bytes_list]
  simp only [List.foldl_cons, List.foldl_nil]
  unfold packedValue wordValue B
  ring

@[step] theorem field_from_packed_spec (bytes : Bytes48) :
    CurveG1.decoder.field_from_bytes bytes ⦃ out =>
      (∀ f, out = some f → Valid f) ∧
      out.map decode = if packedValue bytes < Fp.modulus then some (Fp.ofNat (packedValue bytes)) else none ⦄ := by
  unfold CurveG1.decoder.field_from_bytes
  step*
  all_goals simp_all [value, packedValue, wordValue, B]

@[simp] theorem observe_size (bytes : Bytes48) : (observe bytes).size = 48 := by
  simp [observe, ByteArray.size, -ByteArray.size_data]

@[step] theorem field_from_bytes_spec (bytes : Bytes48) :
    CurveG1.decoder.field_from_bytes bytes ⦃ out =>
      (∀ f, out = some f → Valid f) ∧
      out.map decode = (Fp.fromBytesBE (observe bytes)).toOption ⦄ := by
  apply spec_mono (field_from_packed_spec bytes)
  rintro out ⟨hv, heq⟩
  refine ⟨hv, ?_⟩
  rw [heq, packed_value]
  simp only [Fp.fromBytesBE, observe_size, ne_eq, not_true_eq_false, ite_false, bytes_nat]
  split <;> simp_all [Except.toOption, Fp.ofNat]
  apply Fin.ext
  simp_all [Nat.mod_eq_of_lt]

@[simp] theorem byte_eq (a b : U8) : byte a = byte b ↔ a = b := by
  cases a
  cases b
  simp [byte]

@[simp] theorem byte_zero_iff (a : U8) : byte a = (0 : UInt8) ↔ a = 0#u8 :=
  byte_eq a 0#u8

theorem byte_and (a b : U8) : byte (a &&& b) = byte a &&& byte b := rfl

@[step] theorem tail_zero_spec (bytes : Bytes48) (index : Usize) (hi : index.val ≤ 48) :
    CurveG1.decoder.tail_zero bytes index ⦃ out =>
      out = (bytes.val.drop index.val).all (fun b => b == 0#u8) ⦄ := by
  by_cases heq : index = 48#usize
  · rw [CurveG1.decoder.tail_zero]
    simp_all
  · have hlt : index.val < bytes.val.length := by rw [Array.length_eq]; scalar_tac
    rw [CurveG1.decoder.tail_zero]
    step*
    all_goals
      rw [List.drop_eq_getElem_cons (i := index.val) hlt, List.all_cons]
      simp_all
    all_goals scalar_tac
termination_by 48 - index.val
decreasing_by all_goals scalar_tac

theorem tail_all_zero_fold (bytes : ByteArray) (start : Nat) :
    tailAllZero bytes start =
      (List.range' start (bytes.size - start)).foldl (fun ok i => ok && (bytes.get! i == 0)) true := by
  have body (v : UInt8) (ok : Bool) :
      (if v = 0 then pure (ForInStep.yield ok) else pure (ForInStep.yield false) : Id (ForInStep Bool)) =
        pure (ForInStep.yield (ok && (v == 0))) := by
    by_cases hv : v = 0
    · subst v; simp
    · have hb : (v == 0) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        exact hv (by simpa only [beq_iff_eq] using h)
      simp only [hv, ite_false, hb, Bool.and_false]
  unfold tailAllZero
  simp [body]

@[simp] theorem byte_beq_zero (b : U8) : (byte b == 0) = (b == 0#u8) := by
  apply Bool.eq_iff_iff.mpr
  simp

set_option maxRecDepth 4096 in
theorem tail_zero_observe (bytes : Bytes48) :
    tailAllZero (observe bytes) 1 = (bytes.val.drop 1).all (fun b => b == 0#u8) := by
  rw [tail_all_zero_fold]
  conv_lhs => unfold observe; rw [bytes_list]
  conv_rhs => rw [bytes_list]
  simp [ByteArray.size, -ByteArray.size_data, ByteArray.get!, List.range'_succ,
    getElem!_pos, Bool.and_assoc]

@[simp] theorem byte_mask_zero (a mask : U8) :
    (byte a &&& byte mask) = 0 ↔ (a &&& mask) = 0#u8 := by
  rw [← byte_and, byte_zero_iff]

@[simp] theorem mask128 (a : U8) : byte a &&& 128 = 0 ↔ a &&& 128#u8 = 0#u8 := byte_mask_zero a 128#u8
@[simp] theorem mask64 (a : U8) : byte a &&& 64 = 0 ↔ a &&& 64#u8 = 0#u8 := byte_mask_zero a 64#u8
@[simp] theorem mask32 (a : U8) : byte a &&& 32 = 0 ↔ a &&& 32#u8 = 0#u8 := byte_mask_zero a 32#u8
@[simp] theorem head192 (a : U8) : byte a = 192 ↔ a = 192#u8 := byte_eq a 192#u8
@[simp] theorem mask31 (a : U8) : byte a &&& 31 = byte (a &&& 31#u8) := rfl

def flagsFor (head : U8) : Option CurveG1.decoder.EncodingFlags :=
  let compressed := head &&& 128#u8 != 0#u8
  let infinity := head &&& 64#u8 != 0#u8
  let largest := head &&& 32#u8 != 0#u8
  if largest && (!compressed || infinity) then none
  else some ⟨compressed, infinity, largest⟩

private theorem flag_bits : ∀ b : BitVec 8,
    (((b >>> 7) &&& 1) = 1 ↔ b &&& 128 ≠ 0) ∧
    (((b >>> 6) &&& 1) = 1 ↔ b &&& 64 ≠ 0) ∧
    (((b >>> 5) &&& 1) = 1 ↔ b &&& 32 ≠ 0) := by decide +kernel

def nativeFlags (head : U8) : Option CurveG1.decoder.EncodingFlags :=
  let compressed := decide ((head.bv >>> 7) &&& 1 = 1)
  let infinity := decide ((head.bv >>> 6) &&& 1 = 1)
  let largest := decide ((head.bv >>> 5) &&& 1 = 1)
  if largest && (!compressed || infinity) then none
  else some ⟨compressed, infinity, largest⟩

private theorem native_flags_masks (head : U8) : nativeFlags head = flagsFor head := by
  have hc : decide ((head.bv >>> 7) &&& 1 = 1) = (head &&& 128#u8 != 0#u8) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq,
      UScalar.bv_and, UScalar.ofNatCore_bv]
    exact (flag_bits head.bv).1
  have hi : decide ((head.bv >>> 6) &&& 1 = 1) = (head &&& 64#u8 != 0#u8) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq,
      UScalar.bv_and, UScalar.ofNatCore_bv]
    exact (flag_bits head.bv).2.1
  have hl : decide ((head.bv >>> 5) &&& 1 = 1) = (head &&& 32#u8 != 0#u8) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq,
      UScalar.bv_and, UScalar.ofNatCore_bv]
    exact (flag_bits head.bv).2.2
  simp only [nativeFlags, flagsFor, hc, hi, hl]

theorem flags_total (bytes : Bytes48) :
    CurveG1.decoder.EncodingFlags.get_flags bytes = .ok (nativeFlags bytes[0]!) := by
  simp [CurveG1.decoder.EncodingFlags.get_flags, nativeFlags,
    Aeneas.Std.Array.index_usize, HShiftRight.hShiftRight, UScalar.shiftRight_IScalar,
    UScalar.shiftRight, lift, UScalar.eq_equiv_bv_eq, -BitVec.ushiftRight_eq]
  split_ifs <;> simp_all

@[step] theorem flags_spec (bytes : Bytes48) :
    CurveG1.decoder.EncodingFlags.get_flags bytes ⦃ out => out = flagsFor bytes[0]! ⦄ := by
  rw [flags_total, native_flags_masks]
  exact (spec_ok _).mpr rfl

@[step] theorem remove_flags_spec (bytes : Bytes48) :
    CurveG1.decoder.EncodingFlags.remove_flags bytes ⦃ out =>
      out = bytes.set 0#usize (bytes[0]! &&& 31#u8) ⦄ := by
  unfold CurveG1.decoder.EncodingFlags.remove_flags
  step*
  have he : i1 = i &&& 31#u8 := by
    apply U8.bv_eq_imp_eq
    exact i1_post1
  simp_all

private theorem masked_all_zero (bytes : Bytes48) :
    (bytes.set 0#usize (bytes[0]! &&& 31#u8)).val.all (fun b => b == 0#u8) =
      ((bytes[0]! &&& 31#u8 == 0#u8) && (bytes.val.drop 1).all (fun b => b == 0#u8)) := by
  have hlen : bytes.val.length = 48 := by rw [Array.length_eq]; rfl
  cases h : bytes.val with
  | nil => simp only [h, List.length_nil] at hlen; contradiction
  | cons head tail => simp [Aeneas.Std.Array.set, h, Array.getElem!_Nat_eq]

private theorem infinity_header_bits : ∀ b : BitVec 8,
    b &&& 128 ≠ 0 → b &&& 64 ≠ 0 → b &&& 32 = 0 →
      (b &&& 31 = 0 ↔ b = 192) := by decide +kernel

private theorem infinity_header (head : U8)
    (hc : head &&& 128#u8 ≠ 0#u8) (hi : head &&& 64#u8 ≠ 0#u8)
    (hs : head &&& 32#u8 = 0#u8) : (head &&& 31#u8 = 0#u8 ↔ head = 192#u8) := by
  have h := infinity_header_bits head.bv
  simp only [ne_eq, UScalar.eq_equiv_bv_eq, UScalar.bv_and, UScalar.ofNatCore_bv] at *
  exact h hc hi hs

private theorem infinity_zero (bytes : Bytes48)
    (hc : (bytes[0]! &&& 128#u8 != 0#u8) = true)
    (hi : (bytes[0]! &&& 64#u8 != 0#u8) = true)
    (hv : ¬(bytes[0]! &&& 32#u8 != 0#u8 &&
      (!(bytes[0]! &&& 128#u8 != 0#u8) || bytes[0]! &&& 64#u8 != 0#u8)) = true) :
    (bytes.set 0#usize (bytes[0]! &&& 31#u8)).val.all (fun b => b == 0#u8) =
      ((bytes[0]! == 192#u8) && tailAllZero (observe bytes) 1) := by
  have hs : bytes[0]! &&& 32#u8 = 0#u8 := by
    simpa only [hi, Bool.or_true, Bool.and_true, bne_iff_ne, not_not] using hv
  have hc' : bytes[0]! &&& 128#u8 ≠ 0#u8 := by simpa only [bne_iff_ne] using hc
  have hi' : bytes[0]! &&& 64#u8 ≠ 0#u8 := by simpa only [bne_iff_ne] using hi
  rw [masked_all_zero, tail_zero_observe]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, infinity_header bytes[0]! hc' hi' hs]

private theorem sign_flag (head : U8) :
    (head &&& 32#u8 != 0#u8) = decide (¬head.val &&& 32 = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv, UScalar.val_and,
    UScalar.ofNatCore_val_eq, decide_eq_true_eq]

def readerSpecWith (recover : Fp → Bool → Option G1)
    (bytes : Bytes48) (flags : CurveG1.decoder.EncodingFlags) : Option G1 :=
  if !flags.is_compressed then none
  else
    let masked := bytes.set 0#usize (bytes[0]! &&& 31#u8)
    if flags.is_infinity then
      if masked.val.all (fun b => b == 0#u8) then some G1.zero else none
    else
      (Fp.fromBytesBE (observe masked)).toOption.bind fun x =>
        recover x flags.is_lexographically_largest

def readerSpec := readerSpecWith recoverSpec

/-- A definitionally equal factor of the generated decoder body after flag parsing. -/
def readWithFlags (bytes : Bytes48) (flags : CurveG1.decoder.EncodingFlags) :
    Result (Option RawPoint) := do
  if flags.is_compressed then
    let x_bytes ← CurveG1.decoder.EncodingFlags.remove_flags bytes
    if flags.is_infinity then
      let b ← CurveG1.decoder.tail_zero x_bytes 0#usize
      if b then
        let p ← CurveG1.identity CurveG1.field.Fp.Insts.Curve_g1Field
        .ok (some p)
      else .ok none
    else
      let o ← CurveG1.decoder.field_from_bytes x_bytes
      match o with
      | none => .ok none
      | some x => CurveG1.decoder.point_from_x_unchecked x flags.is_lexographically_largest
  else .ok none

private theorem uncompress48_body (bytes : Bytes48) :
    CurveG1.decoder.uncompress48 bytes = (do
      let o ← CurveG1.decoder.EncodingFlags.get_flags bytes
      match o with
      | none => .ok none
      | some flags => readWithFlags bytes flags) := rfl

attribute [-step] ConcreteRecovery.point_spec in
private theorem read_flags_param (recover : Fp → Bool → Option G1)
    (recover_correct : ∀ (x : Raw) (greatest : Bool), Valid x →
      CurveG1.decoder.point_from_x_unchecked x greatest ⦃ out =>
        CanonicalResult out ∧ out.map decodePoint = recover (decode x) greatest ⦄)
    (bytes : Bytes48) (flags : CurveG1.decoder.EncodingFlags) :
    readWithFlags bytes flags ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = readerSpecWith recover bytes flags ⦄ := by
  unfold readWithFlags
  step*
  all_goals simp_all [CanonicalResult, readerSpecWith]
  all_goals try (intro v hv; rw [b_post v hv]; rfl)
  all_goals rw [← o_post1]
  all_goals rfl

@[step] theorem read_flags_spec (bytes : Bytes48) (flags : CurveG1.decoder.EncodingFlags) :
    readWithFlags bytes flags ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = readerSpec bytes flags ⦄ :=
  read_flags_param recoverSpec (fun x greatest hx => ConcreteRecovery.point_spec x greatest hx) bytes flags

private theorem flag_pipeline (head : U8) (tail : Bool) (finite : Bool → Option G1) :
    (flagsFor head).bind (fun flags =>
      if !flags.is_compressed then none
      else if flags.is_infinity then
        if (head &&& 31#u8 == 0#u8) && tail then some G1.zero else none
      else finite flags.is_lexographically_largest) =
    (if head &&& 128#u8 = 0#u8 then none
      else if head &&& 64#u8 ≠ 0#u8 then
        if (head &&& 32#u8 != 0#u8) || head != 192#u8 || !tail then none else some G1.zero
      else finite (head &&& 32#u8 != 0#u8)) := by
  have hhead := infinity_header head
  by_cases hc : head &&& 128#u8 = 0#u8 <;>
    by_cases hi : head &&& 64#u8 = 0#u8 <;>
    by_cases hs : head &&& 32#u8 = 0#u8 <;> simp_all [flagsFor]
  all_goals by_cases hh : head = 192#u8 <;> cases tail <;> simp_all

private theorem flags_reader (bytes : Bytes48) :
    (flagsFor bytes[0]!).bind (readerSpec bytes) = uncompressSpec (observe bytes) := by
  unfold readerSpec readerSpecWith
  simp_rw [masked_all_zero, ← tail_zero_observe]
  rw [flag_pipeline bytes[0]! (tailAllZero (observe bytes) 1)
    (fun sign => (Fp.fromBytesBE (observe (bytes.set 0#usize (bytes[0]! &&& 31#u8)))).toOption.bind
      fun x => recoverSpec x sign)]
  simp [uncompressSpec, sign_flag]

/-- Compose the extracted reader before applying the pure EthLib parser equivalence. -/
theorem uncompress48_model (bytes : Bytes48) :
    CurveG1.decoder.uncompress48 bytes ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = uncompressSpec (observe bytes) ⦄ := by
  rw [uncompress48_body]
  step*
  all_goals rw [← flags_reader, ← o_post]
  all_goals clear o_post
  all_goals simp_all [CanonicalResult]

@[step] theorem uncompress48_spec (bytes : Bytes48) :
    CurveG1.decoder.uncompress48 bytes ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = (G1.uncompress (observe bytes)).toOption ⦄ := by
  apply spec_mono (uncompress48_model bytes)
  rintro out ⟨hv, he⟩
  exact ⟨hv, he.trans (uncompress_correct (observe bytes))⟩

def observeSlice (bytes : Slice U8) : ByteArray := ⟨(bytes.val.map byte).toArray⟩

@[simp] theorem observeSlice_size (bytes : Slice U8) : (observeSlice bytes).size = bytes.val.length := by
  simp [observeSlice, ByteArray.size, -ByteArray.size_data]

@[step] theorem copy48_spec (bytes : Slice U8) (hlen : bytes.val.length = 48) :
    CurveG1.decoder.copy48 bytes ⦃ out => out.val = bytes.val ⦄ := by
  unfold CurveG1.decoder.copy48
  step*
  simp_all only
  apply List.ext_getElem
  · simpa using hlen.symm
  · intro i hi hj
    have h : i < 48 := by simpa using hi
    interval_cases i <;> rfl

@[step] theorem uncompress_spec (bytes : Slice U8) :
    CurveG1.decoder.uncompress_g1 bytes ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = (G1.uncompress (observeSlice bytes)).toOption ⦄ := by
  unfold CurveG1.decoder.uncompress_g1
  step*
  · simp_all [CanonicalResult, G1.uncompress, Except.toOption]
  · constructor
    · exact out_post
    · simpa only [observe, observeSlice, a_post] using out_post1

/-- Byte inputs need no coordinate preconditions; subgroup rejection is part of the result. -/
@[step] theorem decode_spec (bytes : Slice U8) :
    CurveG1.decoder.decode_g1 bytes ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = (ArkEth.decodeSpec (observeSlice bytes)).toOption ⦄ := by
  unfold CurveG1.decoder.decode_g1
  step as ⟨o, hv, he⟩
  cases o with
  | none =>
    step*
    all_goals cases hu : G1.uncompress (observeSlice bytes)
    all_goals simp only [hu, Except.toOption] at he
    all_goals simp_all [ArkEth.decodeSpec, Except.toOption, CanonicalResult, Bind.bind,
      Except.bind]
  | some p =>
    have hc : G1Curve.OnCurve (decodePoint p) :=
      DecoderCurve.uncompress_onCurve (observeSlice bytes) (decodePoint p) he.symm
    step*
    all_goals cases hu : G1.uncompress (observeSlice bytes)
    all_goals simp only [hu, Except.toOption] at he
    all_goals subst_vars
    all_goals simp_all [ArkEth.decodeSpec, Except.toOption, CanonicalResult, Bind.bind,
      Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem keyValidate_option (bytes : ByteArray) :
    (G1.keyValidatePoint bytes).toOption =
      ((ArkEth.decodeSpec bytes).toOption).filter (fun p => !p.isInfinity) := by
  unfold G1.keyValidatePoint ArkEth.decodeSpec
  cases G1.uncompress bytes with
  | error e => rfl
  | ok p =>
    by_cases hi : p.isInfinity = true <;> by_cases hs : p.inSubgroup = true <;>
      simp [hi, hs, Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Except.toOption, Option.filter]

@[step] theorem decode_public_key_spec (bytes : Slice U8) :
    CurveG1.decoder.decode_public_key bytes ⦃ out =>
      CanonicalResult out ∧ out.map decodePoint = (G1.keyValidatePoint (observeSlice bytes)).toOption ⦄ := by
  unfold CurveG1.decoder.decode_public_key
  step*
  all_goals try (exact (o_post p (by assumption)).2.2)
  all_goals subst o
  all_goals rw [keyValidate_option, ← o_post1]
  all_goals clear o_post1
  all_goals simp_all [CanonicalResult, Option.filter, G1.isInfinity, decodePoint]

#print axioms flags_spec
#print axioms remove_flags_spec
#print axioms field_from_bytes_spec
#print axioms uncompress_spec
#print axioms decode_spec
#print axioms decode_public_key_spec
end ConcreteDecoder

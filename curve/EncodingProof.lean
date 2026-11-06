import ScalarEncodingProof
import FieldPowerProof
import FastSubgroupProof
import CurvePredicates
import ConcreteProof
import BinaryInverseProof
import ScalarNormalizationProof
import EthLib.Cryptography.Bls.Compress

open Aeneas Aeneas.Std Aeneas.Std.WP
open EthLib.Cryptography.Bls FieldProof ConcreteField ConcreteCurve

namespace ConcreteEncoding

@[step] theorem pow_spec (a : Raw) (e : Limbs) (ha : Valid a) :
    CurveG1.field.pow a e ⦃ r => Valid r ∧ decode r = Fp.powNat (decode a) (value e) ⦄ :=
  ConcreteFieldPower.pow_spec a e ha

@[step] theorem sign_spec (a : Raw) (ha : Valid a) :
    CurveG1.field.Fp.sign_bit a ⦃ r => r = Fp.signBit (decode a) ⦄ := by
  unfold CurveG1.field.Fp.sign_bit
  step*
  rw [r_post, positive_limbs_post, negative_limbs_post, ← decode_val a,
    ← decode_val negative, negative_post1]
  simp only [Fp.signBit, Fin.val_neg]
  split <;> simp_all

@[step] theorem affine_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.to_affine p ⦃ r =>
      Valid r.1 ∧ Valid r.2 ∧ (decode r.1, decode r.2) = G1.toAffine (decodePoint p) ⦄ := by
  unfold CurveG1.field.to_affine
  step*

abbrev Bytes48 := Aeneas.Std.Array U8 48#usize

def byte (b : U8) : UInt8 := UInt8.ofBitVec b.bv

def observe (a : Bytes48) : ByteArray := ⟨(a.val.map byte).toArray⟩

def limbByte (x : U64) (n : Nat) : U8 := ⟨(x.bv >>> n).setWidth 8⟩

@[simp] theorem limbByte_val (x : U64) (n : Nat) :
    (limbByte x n).val = (x.val / 2^n) % 256 := by
  change ((x.bv >>> n).setWidth 8).toNat = _
  simp [Nat.shiftRight_eq_div_pow]

def rawBytes (a : Limbs) : Bytes48 := Aeneas.Std.Array.make 48#usize [
  limbByte a[5]! 56, limbByte a[5]! 48, limbByte a[5]! 40, limbByte a[5]! 32, limbByte a[5]! 24, limbByte a[5]! 16, limbByte a[5]! 8, limbByte a[5]! 0,
  limbByte a[4]! 56, limbByte a[4]! 48, limbByte a[4]! 40, limbByte a[4]! 32, limbByte a[4]! 24, limbByte a[4]! 16, limbByte a[4]! 8, limbByte a[4]! 0,
  limbByte a[3]! 56, limbByte a[3]! 48, limbByte a[3]! 40, limbByte a[3]! 32, limbByte a[3]! 24, limbByte a[3]! 16, limbByte a[3]! 8, limbByte a[3]! 0,
  limbByte a[2]! 56, limbByte a[2]! 48, limbByte a[2]! 40, limbByte a[2]! 32, limbByte a[2]! 24, limbByte a[2]! 16, limbByte a[2]! 8, limbByte a[2]! 0,
  limbByte a[1]! 56, limbByte a[1]! 48, limbByte a[1]! 40, limbByte a[1]! 32, limbByte a[1]! 24, limbByte a[1]! 16, limbByte a[1]! 8, limbByte a[1]! 0,
  limbByte a[0]! 56, limbByte a[0]! 48, limbByte a[0]! 40, limbByte a[0]! 32, limbByte a[0]! 24, limbByte a[0]! 16, limbByte a[0]! 8, limbByte a[0]! 0]

set_option maxRecDepth 4096 in
theorem bytes_total (a : Raw) :
    CurveG1.field.Fp.to_bytes_be a = (do
      let limbs ← CurveG1.field.Fp.to_limbs a
      .ok (rawBytes limbs)) := by
  simp [CurveG1.field.Fp.to_bytes_be, rawBytes, limbByte,
    Aeneas.Std.Array.index_usize, HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    UScalar.cast, lift, -BitVec.ushiftRight_eq]

set_option exponentiation.threshold 512 in
set_option maxHeartbeats 2000000 in
theorem rawBytes_values (a : Limbs) (i : Fin 48) :
    (rawBytes a)[i.val]!.val = (value a / 2^((47-i.val)*8)) % 256 := by
  fin_cases i <;> simp [rawBytes, value, B] <;> scalar_tac

@[step] theorem bytes_spec (a : Raw) (ha : Valid a) :
    CurveG1.field.Fp.to_bytes_be a ⦃ r => observe r = Fp.toBytesBE (decode a) ⦄ := by
  rw [bytes_total]
  step*
  apply ByteArray.ext
  apply _root_.Array.ext
  · simp [observe, Fp.toBytesBE]
  · intro i hi hj
    have hi48 : i < 48 := by simpa [Fp.toBytesBE] using hj
    apply UInt8.toNat_inj.mp
    have hv := rawBytes_values limbs ⟨i, hi48⟩
    have mask (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
    simpa [observe, Fp.toBytesBE, byte, Nat.shiftRight_eq_div_pow, mask,
      decode_val, getElem!_pos, hi48, limbs_post] using hv

def formatted (x : Bytes48) (sign infinity : Bool) : Bytes48 :=
  if infinity then (Aeneas.Std.Array.repeat 48#usize 0#u8).set 0#usize 192#u8
  else
    let tagged := x.set 0#usize (x[0]! ||| 128#u8)
    if sign then tagged.set 0#usize (tagged[0]! ||| 32#u8) else tagged

def flagsModel (bytes : Bytes48) (compressed infinity largest : Bool) : Bytes48 :=
  let bytes := if compressed then bytes.set 0#usize (bytes[0]! ||| 128#u8) else bytes
  let bytes := if infinity then bytes.set 0#usize (bytes[0]! ||| 64#u8) else bytes
  if compressed && !infinity && largest then bytes.set 0#usize (bytes[0]! ||| 32#u8) else bytes

/-- The source flag stages are total on every fixed-size byte array and Boolean combination. -/
theorem encode_flags_total (bytes : Bytes48) (compressed infinity largest : Bool) :
    CurveG1.minimal_g1.encode_flags bytes compressed infinity largest = .ok (flagsModel bytes compressed infinity largest) := by
  cases compressed <;> cases infinity <;> cases largest <;>
    simp [CurveG1.minimal_g1.encode_flags, flagsModel, Aeneas.Std.Array.index_usize,
      Aeneas.Std.Array.update,
      Aeneas.Std.Array.set, lift]

#print axioms encode_flags_total

/-- Totality and exact output of the actual generated Rust model. -/
theorem compress_total (x : Bytes48) (sign infinity : Bool) :
    CurveG1.minimal_g1.compress_g1 x sign infinity = .ok (formatted x sign infinity) := by
  cases infinity <;> cases sign <;>
    simp [CurveG1.minimal_g1.compress_g1, CurveG1.minimal_g1.encode_flags, formatted, Aeneas.Std.Array.index_usize,
      Aeneas.Std.Array.update,
      Aeneas.Std.Array.set, lift, show (128#u8 ||| 64#u8) = 192#u8 by decide +kernel]

@[simp] theorem byte_or (a b : U8) : byte (a ||| b) = byte a ||| byte b := by
  rfl

@[simp] theorem observe_set (a : Bytes48) (b : U8) :
    observe (a.set 0#usize b) = (observe a).set! 0 (byte b) := by
  simp [observe, Aeneas.Std.Array.set, ByteArray.set!, List.map_set]

@[simp] theorem observe_head (a : Bytes48) :
    (observe a).get! 0 = byte a[0]! := by
  simp [observe, ByteArray.get!]

@[simp] theorem observe_set_head (a : Bytes48) (b : UInt8) :
    ((observe a).set! 0 b).get! 0 = b := by
  simp [ByteArray.get!, ByteArray.set!, observe]

@[step] theorem formatter_spec (x : Bytes48) (sign infinity : Bool) :
    CurveG1.minimal_g1.compress_g1 x sign infinity ⦃ r => r = formatted x sign infinity ⦄ := by
  rw [compress_total]
  exact (spec_ok _).mpr rfl

private theorem formatted_compress (p : G1) (x y : Fp) (a : Bytes48) (b infinity : Bool)
    (hxy : (x, y) = G1.toAffine p) (hbytes : observe a = Fp.toBytesBE x)
    (hsign : b = Fp.signBit y) (hinf : infinity = G1.isInfinity p) :
    observe (formatted a b infinity) = G1.compress p := by
  have hx := congrArg Prod.fst hxy.symm
  have hy := congrArg Prod.snd hxy.symm
  dsimp only at hx hy
  cases hi : infinity <;> cases hs : b <;>
    simp_all [formatted, G1.compress, byte]
  all_goals first | (rw [← hbytes]; simp [byte]) | decide

@[step] theorem compress_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.compress p ⦃ r => observe r = G1.compress (decodePoint p) ⦄ := by
  unfold CurveG1.field.compress
  step as ⟨affine, hx, hy, he, hi⟩
  step*
  rw [r_post]
  exact formatted_compress (decodePoint p) (decode affine.x) (decode affine.y) bytes largest
    affine.infinity he bytes_post largest_post hi

/-- Exact source affine multiplication and compression, for all canonical inputs. -/
theorem mul_compressed_source_spec (p : RawPoint) (s : Scalar) (hp : ValidPoint p) :
    CurveG1.field.mul_compressed p s ⦃ r =>
      observe r = G1.compress (ScalarEncoding.mulInteger (decodePoint p) (scalarValue s)) ⦄ := by
  unfold CurveG1.field.mul_compressed
  step as ⟨base, hx, hy, he, hi⟩
  have hxe := congrArg Prod.fst he
  have hye := congrArg Prod.snd he
  step*
  all_goals simp_all [ScalarEncoding.mulInteger]

/-- Full-curve encoded agreement with EthLib, without a subgroup assumption. -/
theorem mul_compressed_correct (p : RawPoint) (s : Scalar) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.field.mul_compressed p s ⦃ r =>
      observe r = G1.compress (G1.mulNat (decodePoint p) (scalarValue s)) ⦄ := by
  apply spec_mono (mul_compressed_source_spec p s hp)
  intro out he
  refine he.trans (ScalarEncoding.integer_compressed _ _ hc ?_)
  simpa only [FieldProof.B, ← pow_mul] using ConcreteGLV.scalar_bound s

/-- The source fast check refines the order-r test on on-curve inputs. -/
@[step] theorem subgroup_spec (p : RawPoint) (hp : ValidPoint p)
    (hc : G1Curve.OnCurve (decodePoint p)) :
    CurveG1.field.in_subgroup p ⦃ r => r = G1.inSubgroup (decodePoint p) ⦄ := by
  simpa only [CurveG1.field.in_subgroup] using ConcreteFastSubgroup.ethlib_spec p hp hc

@[step] theorem on_curve_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.is_on_curve p ⦃ r => r = onCurve (decodePoint p) ⦄ := by
  rcases hp with ⟨hx, hy, hz⟩
  have hb := ConcreteField.curve_b_canonical
  unfold CurveG1.field.is_on_curve
  step*
  all_goals simp_all [onCurve, G1.isInfinity, decodePoint]

@[step] theorem valid_subgroup_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.is_valid_subgroup_point p ⦃ r => r = validSubgroupPoint (decodePoint p) ⦄ := by
  unfold CurveG1.field.is_valid_subgroup_point
  by_cases hc : onCurve (decodePoint p) = true
  · have hg := (G1Curve.onCurve_iff (decodePoint p)).mp hc
    step*
    all_goals simp_all [validSubgroupPoint]
  · step*
    all_goals simp_all [validSubgroupPoint]

@[step] theorem public_key_spec (p : RawPoint) (hp : ValidPoint p) :
    CurveG1.field.is_valid_public_key_point p ⦃ r => r = validPublicKeyPoint (decodePoint p) ⦄ := by
  have hz := hp.2.2
  unfold CurveG1.field.is_valid_public_key_point
  step*
  all_goals simp_all [validPublicKeyPoint, G1.isInfinity, decodePoint]

#print axioms on_curve_spec
#print axioms valid_subgroup_spec
#print axioms public_key_spec
#print axioms subgroup_spec
#print axioms pow_spec
#print axioms sign_spec
#print axioms affine_spec
#print axioms bytes_spec
#print axioms compress_spec
#print axioms mul_compressed_source_spec
#print axioms mul_compressed_correct

end ConcreteEncoding


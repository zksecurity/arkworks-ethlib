import Generated.MinimalG1
import ArkEth.SpecLemmas

open Aeneas Aeneas.Std
open EthLib.Cryptography.Bls

namespace MinimalProof

abbrev Bytes48 := Aeneas.Std.Array U8 48#usize

/-- Observe Aeneas' Rust bytes as the byte type used by EthLib. -/
def byte (b : U8) : UInt8 := UInt8.ofBitVec b.bv

def observe (a : Bytes48) : ByteArray := ⟨(a.val.map byte).toArray⟩

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
    MinimalG1.encode_flags bytes compressed infinity largest = .ok (flagsModel bytes compressed infinity largest) := by
  cases compressed <;> cases infinity <;> cases largest <;>
    simp [MinimalG1.encode_flags, flagsModel, Aeneas.Std.Array.index_usize,
      Aeneas.Std.Array.update,
      Aeneas.Std.Array.set, lift]

#print axioms encode_flags_total

/-- Totality and exact output of the actual generated Rust model. -/
theorem compress_total (x : Bytes48) (sign infinity : Bool) :
    MinimalG1.compress_g1 x sign infinity = .ok (formatted x sign infinity) := by
  cases infinity <;> cases sign <;>
    simp [MinimalG1.compress_g1, MinimalG1.encode_flags, formatted, Aeneas.Std.Array.index_usize,
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

/-- The complete extracted formatter agrees with the actual EthLib compressor,
    provided its boundary inputs represent the same affine coordinates.
    No Montgomery-conversion or arkworks-equivalence assumption is hidden here. -/
theorem compress_refines_ethlib (x : Bytes48) (p : ArkEth.AffineInput)
    (hx : observe x = p.x.toBytesBE) :
    ∃ out, MinimalG1.compress_g1 x (Fp.signBit p.y) p.infinity = .ok out ∧
      observe out = ArkEth.encodeSpec p := by
  refine ⟨formatted x (Fp.signBit p.y) p.infinity, compress_total _ _ _, ?_⟩
  rcases p with ⟨px, py, infinity⟩
  cases infinity with
  | true =>
      rw [ArkEth.infinity_encoding]
      simp [formatted, observe, Aeneas.Std.Array.set, G1.infinityBytes,
        byte, Aeneas.Std.Array.repeat]
      decide
  | false =>
      rw [ArkEth.finite_encoding]
      cases Fp.signBit py <;>
        simp [formatted, ← hx, byte]

#print axioms compress_total
#print axioms compress_refines_ethlib

end MinimalProof

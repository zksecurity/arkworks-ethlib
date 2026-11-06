import ArkEth
import ArkEth.CodecUtil
import EthLib.Cryptography.Bls.Pairing

open EthLib.Cryptography.Bls ArkEth.CodecUtil

namespace PairingExample

def readFp (b : ByteArray) (start : Nat) : Option Fp :=
  if b.size < start + 64 then none else
    let n := Fp.bytesBEToNat (b.extract start (start + 64))
    if h : n < Fp.modulus then some ⟨n, h⟩ else none

def readG1 (b : ByteArray) (start : Nat) : Option G1 := do
  let x ← readFp b start
  let y ← readFp b (start + 64)
  if x.isZero && y.isZero then return G1.zero
  let p : G1 := ⟨x, y, Fp.one⟩
  if !(y*y).beq (x*x*x + Fp.ofNat 4) || !G1.inSubgroup p then none else some p

def readG2 (b : ByteArray) (start : Nat) : Option G2 := do
  let x0 ← readFp b start
  let x1 ← readFp b (start + 64)
  let y0 ← readFp b (start + 128)
  let y1 ← readFp b (start + 192)
  let x : Fp2 := ⟨x0, x1⟩
  let y : Fp2 := ⟨y0, y1⟩
  if x.isZero && y.isZero then return G2.zero
  let p : G2 := ⟨x, y, Fp2.one⟩
  if !(y*y).beq (x*x*x + G2.bTwist) || !G2.inSubgroup p then none else some p

def pointHex (p : G1) : String :=
  if p.isInfinity then String.ofList (List.replicate 256 '0') else
    let (x,y) := p.toAffine
    let pad := String.ofList (List.replicate 32 '0')
    pad ++ hex x.toBytesBE ++ pad ++ hex y.toBytesBE

def run (line : String) : Option String := do
  let args := line.splitOn "\t"
  let encoded ← args[1]?
  let bytes ← unhexList encoded.toList
  let b := ByteArray.mk bytes.toArray
  match args with
  | ["pair", _] => do
      if b.size == 0 || b.size % 384 != 0 then none else do
        let pairs ← (List.range (b.size / 384)).mapM fun i => do
          let p ← readG1 b (i*384)
          let q ← readG2 b (i*384 + 128)
          return (p,q)
        return s!"pair\t{pairingCheck pairs.toArray}"
  | ["mul", _] => do
      if b.size != 160 then none else do
        let p ← readG1 b 0
        let k := Fp.bytesBEToNat (b.extract 128 160)
        return s!"mul\t{pointHex (G1.mulNat p k)}"
  | _ => none

def examples : Array (String × Array (G1 × G2)) :=
  let p := G1.generator
  let q := G2.generator
  let p2 := G1.mulNat p 2
  let q3 := G2.mulNat q 3
  let p6 := G1.mulNat p 6
  let p5 := G1.mulNat p 5
  #[("cancellation", #[(p,q), (G1.neg p,q)]),
    ("non_degeneracy", #[(p,q)]),
    ("bilinearity", #[(p2,q3), (G1.neg p6,q)]),
    ("wrong_scalar", #[(p2,q3), (G1.neg p5,q)]),
    ("identity", #[(G1.zero,q), (p,G2.zero)])]

end PairingExample

def main (args : List String) : IO Unit := do
  let stdout ← IO.getStdout
  if args.contains "--demo" then
    for (name,pairs) in PairingExample.examples do
      stdout.putStrLn s!"{name}\t{pairingCheck pairs}"
  else
    let stdin ← IO.getStdin
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      stdout.putStrLn ((PairingExample.run line.trimAscii.toString).getD "invalid")

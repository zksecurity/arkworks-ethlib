import ArkEth
import ArkEth.CodecUtil

open EthLib.Cryptography.Bls ArkEth.CodecUtil

/-- Match the test runner's affine input boundary before comparing raw Jacobian outputs. -/
def curveInput (n : Nat) : G1 :=
  let p := G1.mulNat G1.generator n
  if p.isInfinity then G1.zero
  else let (x, y) := p.toAffine; ⟨x, y, Fp.one⟩

def runCurveCommand (args : List String) : Option String := do
  let ns ← args[1]?
  let n ← ns.toNat?
  if n ≥ 2^64 then none else do
    let p := curveInput n
    let out ← match args with
      | ["neg", _] => some (G1.neg p)
      | ["double", _] => some (G1.double p)
      | ["add", _, ms] => do
          let m ← ms.toNat?
          if m ≥ 2^64 then none else some (G1.add p (curveInput m))
      | ["mul", _, ks] => do
          let k ← ks.toNat?
          if k ≥ 2^64 then none else some (G1.mulNat p k)
      | ["mul256", _, ks] => do
          let bytes ← unhexList ks.toList
          if bytes.length ≠ 32 then none
          else some (G1.mulNat p (Fp.bytesBEToNat ⟨bytes.toArray⟩))
      | _ => none
    return s!"ok\t{hex (G1.compress out)}\t{hex out.x.toBytesBE}\t{hex out.y.toBytesBE}\t{hex out.z.toBytesBE}"

def runCommand (line : String) : String := Id.run do
  match line.splitOn "\t" with
  | "curve" :: args => return (runCurveCommand args).getD "invalid"
  | ["encode", s] =>
      match s.toNat? with
      | none => return "invalid"
      | some n =>
          if n ≥ 2^64 then return "invalid"
          let p := G1.mulNat G1.generator n
          let (x, y) := p.toAffine
          return s!"ok\t{hex x.toBytesBE}\t{hex y.toBytesBE}\t{hex (G1.compress p)}"
  | ["decode", s] =>
      match unhexList s.toList with
      | none => return "invalid"
      | some bytes =>
          match ArkEth.decodeObservation (ByteArray.mk bytes.toArray) with
          | none => return "invalid"
          | some canonical => return s!"ok\t{hex canonical}"
  | _ => return "invalid"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (runCommand line.trimAscii.toString)

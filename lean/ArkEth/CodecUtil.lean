namespace ArkEth.CodecUtil

def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 97 + n - 10)

def hex (bytes : ByteArray) : String := String.ofList <|
  bytes.data.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def unhexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def unhexList : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
      let x ← unhexDigit a
      let y ← unhexDigit b
      let tail ← unhexList rest
      return UInt8.ofNat (16 * x + y) :: tail
  | _ => none

end ArkEth.CodecUtil

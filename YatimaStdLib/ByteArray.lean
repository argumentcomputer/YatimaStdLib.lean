import YatimaStdLib.List
import YatimaStdLib.Nat

namespace ByteArray

/-- Read Nat from Little-Endian ByteArray -/
def asLEtoNat (b : ByteArray) : Nat :=
  b.data.data.enum.foldl (init := 0)
    fun acc (i, bᵢ) => acc + bᵢ.toNat.shiftLeft (i * 8)

/-- Read Nat from Big-Endian ByteArray -/
def asBEtoNat (b : ByteArray) : Nat :=
  b.data.data.foldl (init := 0)
    fun acc bᵢ => acc.shiftLeft 8 + bᵢ.toNat

def leadingZeroBits (bytes : ByteArray) : Nat := Id.run do
  let mut c := 0
  for byte in bytes do
    let zs := 8 - byte.toNat.sigBits
    if byte != 0
    then return c + zs
    else c := c + zs
  return c

def pushZeros (bytes : ByteArray): Nat → ByteArray
  | 0     => bytes
  | n + 1 => pushZeros (bytes.push 0) n

instance {α : Type u} [Ord α] : Ord (Array α) where
  compare x y := compare x.data y.data

instance : Ord ByteArray where
  compare x y := compare x.data y.data

def Subarray.asBA (s : Subarray UInt8) : ByteArray :=
  s.as.data.toByteArray

def UInt8.showBits (u : UInt8) : String :=
  let numStr := u.toNat |> Nat.toDigits 2
  "".pushn '0' (8 - numStr.length) ++ ⟨numStr⟩

def ByteArray.toString (bs : ByteArray) : String := Id.run do
  if bs.isEmpty then "b[]" else
  let mut ans := "b["
  for u in bs do
    ans := ans ++ UInt8.showBits u ++ ","
  return ans.dropRight 1 ++ "]"

instance : Repr ByteArray where
  reprPrec bs _ := toString bs

def ByteArray.padLeft (bs : ByteArray) (u : UInt8) : Nat → ByteArray
  | 0 => bs
  | n + 1 => ByteArray.mk #[u] ++ padLeft bs u n

partial def UInt64.toByteArray (u : UInt64) : ByteArray :=
  let rec loop (u : UInt64) (acc : Array UInt8) :=
    if u == 0 then acc else loop (u >>> 8) <| acc.push (u &&& (0xff : UInt64)).toUInt8
  loop u #[] |>.reverse
             |> ByteArray.mk
             |> (fun bs => ByteArray.padLeft bs 0 (8 - bs.size))
inductive Bit where
  | one
  | zero
deriving BEq

instance : ToString Bit where
  toString
    | .one  => "1"
    | .zero => "0"
open Bit

def Bit.xOr : Bit → Bit → Bit
  | one, zero
  | zero, one => one
  | _, _      => zero

def Bit.toNat : Bit → Nat
  | zero => 0
  | one  => 1

def Bit.toUInt8 : Bit → UInt8 := Nat.toUInt8 ∘ Bit.toNat
def bArXOr (bs : Array Bit) : Bit := bs.foldl (fun b b' => b.xOr b') zero

def bArToNat (bs : Array Bit) : Nat := bs.foldl (fun b b' => b*2 + b'.toNat) 0

def ByteArray.getD (bs : ByteArray) (idx : Int) : UInt8 :=
  if idx < 0 || bs.size ≤ idx then 0 else bs[idx.toNat]!

def UInt8.getBit (u : UInt8) (n : Nat) : Bit :=
  if u &&& (1 <<< (7 - n)).toUInt8 == 0 then zero else one

def ByteArray.getBit (bs : ByteArray) (n : Nat) : Bit :=
  let (idx, rem) := (n / 8, n%8)
  UInt8.getBit bs[idx]! rem
-- Shifts the byte array left by 1, preserves length (so in particular kills the first coefficient
def ByteArray.shiftLeft (bs : ByteArray) : ByteArray := Id.run do
  let mut answer : ByteArray := .mkEmpty bs.size
  for idx in [:bs.size] do
    answer := answer.push <| (bs[idx]! <<< 1 : UInt8) + (getD bs (idx + 1) >>> 7 : UInt8)
  answer

def ByteArray.shiftAdd (bs : ByteArray) (b : Bit) : ByteArray :=
  let ans := shiftLeft bs
  ans.set! (ans.size - 1) (ans[(ans.size - 1)]! + b.toUInt8)

end ByteArray

import YatimaStdLib.List
import YatimaStdLib.Nat
import YatimaStdLib.UInt
import YatimaStdLib.FFI.UIntByteArray

namespace ByteArray

/-- Read Nat from Little-Endian ByteArray -/
def asLEtoNat (b : ByteArray) : Nat :=
  b.data.data.enum.foldl (init := 0)
    fun acc (i, bᵢ) => acc + bᵢ.toNat.shiftLeft (i * 8)

/-- Read Nat from Big-Endian ByteArray -/
def asBEtoNat (b : ByteArray) : Nat :=
  b.data.data.foldl (init := 0) fun acc bᵢ => acc.shiftLeft 8 + bᵢ.toNat

def leadingZeroBits (bytes : ByteArray) : Nat := Id.run do
  let mut c := 0
  for byte in bytes do
    let zs := 8 - byte.toNat.sigBits
    if byte != 0
    then return c + zs
    else c := c + zs
  return c

def pushZeros (bytes : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut bytes := bytes
  for _ in [0 : n] do
    bytes := bytes.push 0
  return bytes

instance : Ord ByteArray := ⟨ByteArray.ordC⟩

instance : BEq ByteArray where
  beq x y := match compare x y with
    | .eq => true | _ => false

def Subarray.asBA (s : Subarray UInt8) : ByteArray :=
  s.as.data.toByteArray

def toString (bs : ByteArray) : String := Id.run do
  if bs.isEmpty then "b[]" else
  let mut ans := "b["
  for u in bs do
    ans := ans ++ UInt8.showBits u ++ ","
  return ans.dropRight 1 ++ "]"

instance : Repr ByteArray where
  reprPrec bs _ := toString bs

def padLeft (bs : ByteArray) (u : UInt8) : Nat → ByteArray
  | 0 => bs
  | n + 1 => ByteArray.mk #[u] ++ padLeft bs u n

def getD (bs : ByteArray) (idx : Nat) (defaultValue : UInt8) : UInt8 :=
  bs.data.getD idx defaultValue

def getBit (bs : ByteArray) (n : Nat) : Bit :=
  let (idx, rem) := (n / 8, n % 8)
  UInt8.getBit (getD bs idx 0) rem

/--
Shifts the byte array left by 1, preserves length (so in particular kills the
first coefficient
-/
def shiftLeft (bs : ByteArray) : ByteArray := Id.run do
  let mut answer : ByteArray := .mkEmpty bs.size
  for idx in [:bs.size] do
    answer := answer.push <|
      (getD bs idx 0 <<< 1 : UInt8) + (getD bs (idx + 1) 0 >>> 7 : UInt8)
  answer

def shiftAdd (bs : ByteArray) (b : Bit) : ByteArray :=
  let ans := shiftLeft bs
  ans.set! (ans.size - 1) ((getD ans (ans.size - 1) 0) + b.toUInt8)

end ByteArray

partial def UInt64.toByteArray (u : UInt64) : ByteArray :=
  let rec loop (u : UInt64) (acc : Array UInt8) :=
    if u == 0 then acc else loop (u >>> 8) <| acc.push (u &&& (0xff : UInt64)).toUInt8
  loop u #[] |>.reverse
             |> ByteArray.mk
             |> (fun bs => .padLeft bs 0 (8 - bs.size))

import YatimaPrelude.List
import YatimaPrelude.Nat

namespace ByteArray

/-- Read Nat from Little-Endian ByteArray -/
def asLEtoNat (b: ByteArray) : Nat := Id.run do
  let mut x := 0
  for i in [:b.size] do
    x := x + b.data[i].toNat.shiftLeft (i * 8)
  return x

/-- Read Nat from Big-Endian ByteArray -/
def asBEtoNat (b : ByteArray) : Nat := Id.run do
  let mut x := 0
  for i in [:b.size] do
    x := Nat.shiftLeft x 8 + b.data[i].toNat
  return x

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

instance {α : Type u} [inst: Ord α] : Ord (Array α) where
  compare x y := compare x.data y.data

instance : Ord ByteArray where
  compare x y := compare x.data y.data

def Subarray.asBA (s : Subarray UInt8) : ByteArray :=
  s.as.data.toByteArray

end ByteArray
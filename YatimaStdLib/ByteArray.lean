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

end ByteArray

import YatimaStdLib.ByteArray
import Std.Data.Nat.Lemmas

structure ByteVector (n : Nat) where
  data  : ByteArray
  valid : data.size = n
  deriving Ord

namespace ByteVector

instance : Inhabited (ByteVector n) where
  default := ⟨.mk $ .mkArray n 0, by simp [ByteArray.size]⟩

instance : BEq (ByteVector n) where
  beq x y := x.data == y.data

def toString (vec : ByteVector n) : String :=
  let str := s!"⟨{", ".intercalate (vec.data.data.data.map ToString.toString)}⟩"
  s!"{n.toSubscriptString}{str}"

instance : ToString (ByteVector n) := ⟨toString⟩

def ofByteArray (bytes : ByteArray) : ByteVector bytes.size :=
  ⟨bytes, rfl⟩

def get (vec : ByteVector n) (i : Nat) (h : i < n) : UInt8 :=
  vec.data.get ⟨i, by simp only [vec.valid, h]⟩

def get' (vec : ByteVector n) (i : Fin n) : UInt8 :=
  vec.data.get ⟨i, by simp only [vec.valid, i.isLt]⟩

def get! (vec : ByteVector n) (i : Nat) : UInt8 :=
  vec.data.get! i

def set (vec : ByteVector n) (i : Nat) (h : i < n) (u : UInt8) : ByteVector n :=
  let data := vec.data.set ⟨i, by simp only [vec.valid, h]⟩ u
  ⟨data, by rw [ByteArray.set_size, vec.valid]⟩

def set' (vec : ByteVector n) (i : Fin n) (u : UInt8) : ByteVector n :=
  let data := vec.data.set ⟨i, by simp only [vec.valid, i.isLt]⟩ u
  ⟨data, by rw [ByteArray.set_size, vec.valid]⟩

def set! (vec : ByteVector n) (i : Nat) (u : UInt8) : ByteVector n :=
  let data := vec.data.set! i u
  ⟨data, by rw [ByteArray.set!_size, vec.valid]⟩

def genWith (f : Fin n → UInt8) : ByteVector n := Id.run do
  let mut res := default
  for h : i in [0 : n] do
    have := Membership.mem.upper h
    res := res.set i this (f $ Fin.mk i this)
  return res  

def ofNat (n capacity : Nat) : ByteVector capacity :=
  ⟨n.toByteArrayLE.slice 0 capacity, ByteArray.slice_size⟩

@[extern "lean_byte_vector_to_uint16"]
opaque toUInt16 : @& ByteVector 2 → UInt16

@[extern "lean_byte_vector_to_uint32"]
opaque toUInt32 : @& ByteVector 4 → UInt32

@[extern "lean_byte_vector_to_uint64"]
opaque toUInt64 : @& ByteVector 8 → UInt64

def map (v : ByteVector n) (f : UInt8 → UInt8) : ByteVector n := Id.run do
  let mut res := default
  for h : i in [0 : n] do
    have := Membership.mem.upper h
    res := res.set i this (f $ v.get i this)
  pure res

def zipWith (x y : ByteVector n) (f : UInt8 → UInt8 → UInt8) : ByteVector n := Id.run do
  let mut res := default
  for h : i in [0 : n] do
    have := Membership.mem.upper h
    res := res.set i this (f (x.get i this) (y.get i this))
  pure res

def split (x : ByteVector n) (size₁ size₂ : Nat) : ByteVector size₁ × ByteVector size₂ :=
  let left := x.data.slice 0 size₁
  let right := x.data.slice size₁ size₂
  (⟨left, ByteArray.slice_size⟩, ⟨right, ByteArray.slice_size⟩)

open Array in
def append (x : ByteVector n) (y : ByteVector m) : ByteVector (n + m) := 
  let ⟨xData, xSize⟩ := x
  let ⟨yData, ySize⟩ := y
  ⟨⟨xData.data ++ yData.data⟩, append_size xData.data yData.data xSize ySize⟩

def shiftRight1 (x : ByteVector n) : ByteVector n := 
  ⟨x.data.slice 1 n, ByteArray.slice_size⟩

def shiftRight (x : ByteVector n) : Nat → ByteVector n
  | 0     => x
  | m + 1 => shiftRight (shiftRight1 x) m

-- Boolean and arithmetic operations

def lor (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  x.zipWith y UInt8.lor

def and (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  x.zipWith y UInt8.land

def xor (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  x.zipWith y UInt8.xor

def not (x : ByteVector n) : ByteVector n :=
  x.map (255 - ·)

def add (x y : ByteVector n) : ByteVector n := 
  ⟨x.data + y.data |>.slice 0 n, ByteArray.slice_size⟩

instance : Add (ByteVector n) where
  add := add

-- TODO: is it correct?
instance : Sub (ByteVector n) where
  sub x y := x + ByteVector.not y

instance : HMul (ByteVector n) UInt8 (ByteVector n) where
  hMul b u := ⟨b.data * u |>.slice 0 n, ByteArray.slice_size⟩

private def naiiveMul (x y : ByteVector n) : ByteVector n :=
  ⟨x.data * y.data |>.slice 0 n, ByteArray.slice_size⟩

def karatsubaMul (x y : ByteVector n) : ByteVector n := sorry

instance : Mul (ByteVector n) where
  mul := naiiveMul

end ByteVector

@[extern "lean_byte_array_blake3"]
opaque ByteArray.blake3 : @& ByteArray → ByteVector 32

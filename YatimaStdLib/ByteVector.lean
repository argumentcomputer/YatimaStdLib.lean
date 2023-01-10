import YatimaStdLib.ByteArray

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

def byteMap (f : UInt8 → UInt8) (v : ByteVector n) : ByteVector n :=
  ⟨ByteArray.mk $ Array.map f v.data.data, sorry⟩

@[extern "lean_byte_vector_to_uint16"]
opaque toUInt16 : @& ByteVector 2 → UInt16

@[extern "lean_byte_vector_to_uint32"]
opaque toUInt32 : @& ByteVector 4 → UInt32

@[extern "lean_byte_vector_to_uint64"]
opaque toUInt64 : @& ByteVector 8 → UInt64

def zipWith (f : UInt8 → UInt8 → UInt8) (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  let x' := x.data.data
  let y' := y.data.data
  let res := Array.map (fun (x,y) => f x y) $ Array.zip x' y'
  ⟨ByteArray.mk res, sorry⟩

def byteVecAdd (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Add (ByteVector n) where
  add := sorry

def byteVecSub (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Sub (ByteVector n) where
  sub := sorry

def byteVecMul (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Mul (ByteVector n) where
  mul := sorry

def byteVecInv (x : ByteVector n) : ByteVector n := sorry

instance : Inv (ByteVector n) where
  inv := sorry

def byteVecDiv (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Div (ByteVector n) where
  div := sorry

def ByteVector.lor (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  zipWith UInt8.lor x y

def ByteVector.and (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  zipWith UInt8.land x y

def ByteVector.xor (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  zipWith UInt8.xor x y

def ByteVector.not (x : ByteVector n) : ByteVector n :=
  byteMap (fun a => 255 - a) x

end ByteVector

@[extern "lean_byte_array_blake3"]
opaque ByteArray.blake3 : @& ByteArray → ByteVector 32

import YatimaStdLib.ByteArray

structure ByteVector (n : Nat) where
  data  : ByteArray
  valid : data.size = n

namespace ByteVector

instance : Inhabited (ByteVector n) where
  default := ⟨.mk $ .mkArray n 0, by simp [ByteArray.size]⟩

def ofByteArray (bytes : ByteArray) : ByteVector bytes.size :=
  ⟨bytes, rfl⟩

def get (vec : ByteVector n) (i : Nat) (h : i < n) : UInt8 :=
  vec.data.get ⟨i, by simp [vec.valid, h]⟩

@[extern "lean_byte_vector_to_uint16"]
opaque toUInt16 : @& ByteVector 2 → UInt16

@[extern "lean_byte_vector_to_uint32"]
opaque toUInt32 : @& ByteVector 4 → UInt32

@[extern "lean_byte_vector_to_uint64"]
opaque toUInt64 : @& ByteVector 8 → UInt64

end ByteVector

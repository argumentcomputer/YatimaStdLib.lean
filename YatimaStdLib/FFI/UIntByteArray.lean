@[extern "lean_uint16_to_byte_array"]
opaque UInt16.toByteArrayC : UInt16 → ByteArray

@[extern "lean_uint32_to_byte_array"]
opaque UInt32.toByteArrayC : UInt32 → ByteArray

@[extern "lean_uint64_to_byte_array"]
opaque UInt64.toByteArrayC : UInt64 → ByteArray

@[extern "lean_byte_array_to_uint16"]
opaque UInt16.ofByteArrayC : @& ByteArray → UInt16

@[extern "lean_byte_array_to_uint32"]
opaque UInt32.ofByteArrayC : @& ByteArray → UInt32

@[extern "lean_byte_array_to_uint64"]
opaque UInt64.ofByteArrayC : @& ByteArray → UInt64

@[extern "lean_byte_array_ord"]
opaque ByteArray.ordC : @& ByteArray → @& ByteArray → Ordering

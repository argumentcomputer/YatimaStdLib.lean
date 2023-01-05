import YatimaStdLib.Bit

def UInt8.showBits (u : UInt8) : String :=
  let numStr := u.toNat |> Nat.toDigits 2
  "".pushn '0' (8 - numStr.length) ++ ⟨numStr⟩

def UInt8.getBit (u : UInt8) (n : Nat) : Bit :=
  if u &&& (1 <<< (7 - n)).toUInt8 == 0 then .zero else .one

@[extern "lean_uint16_to_byte_array"]
opaque UInt16.toByteArrayC : UInt16 → ByteArray

@[extern "lean_uint32_to_byte_array"]
opaque UInt32.toByteArrayC : UInt32 → ByteArray

@[extern "lean_uint64_to_byte_array"]
opaque UInt64.toByteArrayC : UInt64 → ByteArray

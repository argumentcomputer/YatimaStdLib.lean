import YatimaStdLib.Bit

def UInt8.showBits (u : UInt8) : String :=
  let numStr := u.toNat |> Nat.toDigits 2
  "".pushn '0' (8 - numStr.length) ++ ⟨numStr⟩

def UInt8.getBit (u : UInt8) (n : Nat) : Bit :=
  if u &&& (1 <<< (7 - n)).toUInt8 == 0 then .zero else .one

def UInt16.toByteArray (n : UInt16) : ByteArray :=
  ⟨#[n.toUInt8, (n / 256) % 65536 |>.toUInt8]⟩

theorem UInt16.toByteArray_size_2 : (UInt16.toByteArray n).size = 2 := by
  simp [ByteArray.size, Array.size, List.length]

@[extern "lean_uint16_to_byte_array"]
opaque UInt16.toByteArrayC : UInt16 → ByteArray

def UInt32.toByteArray (n : UInt32) : ByteArray :=
  let a₀ := n.toUInt8
  let n := n / 256
  let a₁ := n % 65536 |>.toUInt8
  let n := n / 256
  let a₂ := n % 16777216 |>.toUInt8
  let n := n / 256
  let a₃ := n % 4294967296 |>.toUInt8
  ⟨#[a₀, a₁, a₂, a₃]⟩

theorem UInt32.toByteArray_size_4 : (UInt32.toByteArray n).size = 4 := by
  simp [ByteArray.size, Array.size, List.length]

@[extern "lean_uint32_to_byte_array"]
opaque UInt32.toByteArrayC : UInt32 → ByteArray

def UInt64.toByteArray (n : UInt64) : ByteArray :=
  let a₀ := n.toUInt8
  let n := n / 256
  let a₁ := n % 65536 |>.toUInt8
  let n := n / 256
  let a₂ := n % 16777216 |>.toUInt8
  let n := n / 256
  let a₃ := n % 4294967296 |>.toUInt8
  let n := n / 256
  let a₄ := n % 1099511627776 |>.toUInt8
  let n := n / 256
  let a₅ := n % 281474976710656 |>.toUInt8
  let n := n / 256
  let a₆ := n % 72057594037927936 |>.toUInt8
  let n := n / 256
  let a₇ := n % 18446744073709551616 |>.toUInt8
  ⟨#[a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]⟩

theorem UInt64.toByteArray_size_8 : (UInt64.toByteArray n).size = 8 := by
  simp [ByteArray.size, Array.size, List.length]

@[extern "lean_uint64_to_byte_array"]
opaque UInt64.toByteArrayC : UInt64 → ByteArray

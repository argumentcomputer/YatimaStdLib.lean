namespace StringInterner

structure Buffer where
  numStrings : Nat
  data       : ByteArray
  deriving Inhabited

abbrev BufferM := StateM Buffer

namespace BufferM

@[inline] def push (byte : UInt8) : BufferM Unit := do
  modify fun b => { b with data := b.data.push byte }

@[inline] def append (bytes : ByteArray) : BufferM Unit := do
  modify fun b => { b with data := b.data.append bytes }

/-- TODO:
  should check `UInt64` bounds for "correct" implementation
  but extra cmp is slow so we forgo it for now -/
def nextSymbol : BufferM Nat := do
  return (← get).data.size
  -- let n := b.data.size
  -- if n < UInt64.size then
  --   n.toUInt64
  -- else
  --   panic! "Buffer overflow, size greater than UInt64 maximum value"

def encodeVarSize (value : Nat) : BufferM Nat := do
  if value ≤ 0x7F then
    push value.toUInt8
    return 1
  else
    let mut value := value
    let mut lenChunks := 0
    while true do
      let mut chunk := value.toUInt8 &&& 0x7F
      value := value >>> 7
      let flag : UInt8 := if value != 0 then 1 else 0
      chunk :=  chunk ||| flag <<< 7
      push chunk
      lenChunks := lenChunks + 1
      if value == 0 then
        break
    return lenChunks

def pushString (str : String) : BufferM Nat := do
  let symbol ← nextSymbol
  let len := str.length
  let bytes := str.toUTF8
  discard $ encodeVarSize len
  modify fun b => { numStrings := b.numStrings + 1, data := b.data.append bytes }
  return symbol

def decodeVarSize! (index : Nat) : BufferM (Nat × Nat) := do
  let first := (← get).data[index]!
  if first ≤ 0x7F then
    return (first.val, 1)
  else
    let mut result := 0
    let mut i := 0
    while true do
      let byte := (← get).data[index + i]!
      let shifted := (byte &&& 0x7F).toNat <<< (i * 7)
      result := result + shifted
      i := i + 1
      if byte &&& 0x80 == 0 then
        break
    return (result, i)

def resolveIndexToStr (index : Nat) : BufferM String := do
  let (strLen, strLenBytes) ← decodeVarSize! index
  let start := index + strLenBytes
  let strBytes := (← get).data.extract start (start + strLen)
  return .fromUTF8! strBytes

end BufferM

end StringInterner

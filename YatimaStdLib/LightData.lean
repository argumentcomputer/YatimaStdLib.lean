import YatimaStdLib.ByteArray
import YatimaStdLib.ByteVector
import YatimaStdLib.DataClasses
import YatimaStdLib.Either
import YatimaStdLib.Ord
import YatimaStdLib.Array

inductive LightData
  | bol : Bool   → LightData
  | u8  : UInt8  → LightData
  | u16 : UInt16 → LightData
  | u32 : UInt32 → LightData
  | u64 : UInt64 → LightData
  | str : String → LightData
  | byt : ByteArray → LightData
  | lnk : ByteVector 32 → LightData
  | arr : Array LightData → LightData
  | prd : LightData × LightData → LightData
  | opt : Option LightData → LightData
  | eit : Either LightData LightData → LightData
  deriving Inhabited, Ord

namespace LightData

partial def beq : LightData → LightData → Bool
  | bol x, bol y
  | u8  x, u8  y
  | u16 x, u16 y
  | u32 x, u32 y
  | u64 x, u64 y
  | str x, str y
  | byt x, byt y
  | lnk x, lnk y => x == y
  | arr x, arr y =>
    let rec aux : List LightData → List LightData → Bool
      | _ :: _, []
      | [], _ :: _ => false
      | [], [] => true
      | x :: xs, y :: ys => x.beq y && aux xs ys
    aux x.data y.data
  | prd (x₁, x₂), prd (y₁, y₂) => x₁.beq y₁ && x₂.beq y₂
  | opt none, opt none => true
  | opt $ some x, opt $ some y
  | eit $ .left x, eit $ .left y
  | eit $ .right x, eit $ .right y => x.beq y
  | _, _ => false

instance : BEq LightData := ⟨beq⟩

partial def toString : LightData → String
  | bol true  => "tt"
  | bol false => "ff"
  | u8  x => s!"{x}ᵤ₈"
  | u16 x => s!"{x}ᵤ₁₆"
  | u32 x => s!"{x}ᵤ₃₂"
  | u64 x => s!"{x}ᵤ₆₄"
  | str x => s!"\"{x}\""
  | byt x => ToString.toString x
  | lnk x => s!"↑{x}"
  | arr x => s!"⟨{", ".intercalate $ x.data.map toString}⟩"
  | prd (x, y) => s!"({x.toString}, {y.toString})"
  | opt none => "?"
  | opt $  some  x => s!"!{x.toString}"
  | eit $ .left  x => s!"←{x.toString}"
  | eit $ .right x => s!"→{x.toString}"

instance : ToString LightData := ⟨toString⟩

section Encoding

def ofNat (x : Nat) : LightData :=
  if x < UInt8.size then u8 (.ofNat x)
  else if x < UInt16.size then u16 (.ofNat x)
  else if x < UInt32.size then u32 (.ofNat x)
  else u64 (.ofNat x) -- may overflow

instance : Encodable LightData LightData ε := ⟨id, pure⟩

instance : Encodable Bool LightData String where
  encode := bol
  decode | bol x => pure x | x => throw s!"Expected a boolean but got {x}"

instance : Encodable Nat LightData String where
  encode := ofNat
  decode
    | u8 x | u16 x | u32 x | u64 x => pure x.toNat
    | x => throw s!"Expected a numeric value but got {x}"

instance : Encodable String LightData String where
  encode := str
  decode | str x => pure x | x => throw s!"Expected a string but got {x}"

instance : Encodable ByteArray LightData String where
  encode := byt
  decode | byt x => pure x | x => throw s!"Expected a byte array but got {x}"

variable [h : Encodable α LightData String]

instance : Encodable (Array α) LightData String where
  encode x := arr $ x.map Encodable.encode
  decode
    | arr x => x.mapM Encodable.decode
    | x => throw s!"Expected an array but got {x}"

instance : Encodable (List α) LightData String where
  encode x := arr $ .mk $ x.map Encodable.encode
  decode
    | arr x => x.data.mapM Encodable.decode
    | x => throw s!"Expected an array but got {x}"

instance : Encodable (Option α) LightData String where
  encode | none => opt none | some a => opt $ some (Encodable.encode a)
  decode
    | opt none => pure none
    | opt $ some x => return some (← Encodable.decode x)
    | x => throw s!"Expected an option but got {x}"

variable [h' : Encodable β LightData String]

instance : Encodable (α × β) LightData String where
  encode | (a, b) => prd (h.encode a, h'.encode b)
  decode
    | prd (a, b) => return (← h.decode a, ← h'.decode b)
    | x => throw s!"Expected a prod but got {x}"

instance : Encodable (Either α β) LightData String where
  encode
    | .left a => eit $ .left (h.encode a)
    | .right b => eit $ .right (h'.encode b)
  decode
    | eit (.left a) => return .left $ ← h.decode a
    | eit (.right b) => return .right $ ← h'.decode b
    | x => throw s!"Expected an either but got {x}"

instance : OfNat LightData n := ⟨.ofNat n⟩

end Encoding

section SerDe

def tag : LightData → UInt8
  | bol false => 0
  | bol true  => 1
  | u8  _ => 2
  | u16 _ => 3
  | u32 _ => 4
  | u64 _ => 5
  | str _ => 6
  | byt _ => 7
  | lnk _ => 8
  | arr _ => 9
  | prd _ => 10
  | opt    none    => 11
  | opt $  some  _ => 12
  | eit $ .left  _ => 13
  | eit $ .right _ => 14

partial def toByteArray (d : LightData) : ByteArray :=
  match d with
  | bol _ => .mk #[d.tag]
  | u8  x => .mk #[d.tag, x]
  | u16 x | u32 x | u64 x => .mk #[d.tag] ++ x.toByteArray
  | str x => let x := x.toUTF8; .mk #[d.tag] ++ toByteArray x.size ++ x
  | byt x => .mk #[d.tag] ++ toByteArray x.size ++ x
  | lnk x => .mk #[d.tag] ++ x.data
  | arr x => x.foldl (fun acc x => acc.append x.toByteArray)
    (⟨#[d.tag]⟩ ++ toByteArray x.size)
  | prd (x, y) => .mk #[d.tag] ++ x.toByteArray ++ y.toByteArray
  | opt none => .mk #[d.tag]
  | opt $ some x | eit $ .left x | eit $ .right x => ⟨#[d.tag]⟩ ++ x.toByteArray

structure Bytes where
  bytes : ByteArray
  size  : Nat
  valid : bytes.size = size

abbrev OfBytesM := ReaderT Bytes $ ExceptT String $ StateM Nat

def readUInt8 : OfBytesM UInt8 := do
  let idx ← get
  let ctx ← read
  if h : idx < ctx.size then
    set idx.succ
    return ctx.bytes.get ⟨idx, by rw [ctx.valid]; exact h⟩
  else throw "No more bytes to read"

def readByteVector (n : Nat) : OfBytesM $ ByteVector n := do
  let idx ← get
  let ctx ← read
  if idx + n - 1 < ctx.size then
    set $ idx + n
    return ⟨ctx.bytes.slice idx n, ByteArray.slice_size⟩
  else throw s!"Not enough data to read {n} bytes (size {ctx.size}, idx {idx})"

def readUInt16 : OfBytesM UInt16 :=
  return (← readByteVector 2).toUInt16

def readUInt32 : OfBytesM UInt32 :=
  return (← readByteVector 4).toUInt32

def readUInt64 : OfBytesM UInt64 :=
  return (← readByteVector 8).toUInt64

def readNat : OfBytesM Nat := do
  match ← readUInt8 with
  | 2 => return (←  readUInt8).toNat
  | 3 => return (← readUInt16).toNat
  | 4 => return (← readUInt32).toNat
  | 5 => return (← readUInt64).toNat
  | x => throw s!"Invalid tag for a numeric value: {x}"

partial def readLightData : OfBytesM LightData := do
  match ← readUInt8 with
  | 0 => return bol false
  | 1 => return bol true
  | 2 => return u8  $ ← readUInt8
  | 3 => return u16 $ ← readUInt16
  | 4 => return u32 $ ← readUInt32
  | 5 => return u64 $ ← readUInt64
  | 6 => return str $ .fromUTF8Unchecked $ (← readByteVector (← readNat)).1
  | 7 => return byt (← readByteVector (← readNat)).1
  | 8 => return lnk $ ← readByteVector 32
  | 9 =>
    return arr $ ← List.range (← readNat) |>.foldlM (init := #[])
      fun acc _ => do pure $ acc.push (← readLightData)
  | 10 => return prd (← readLightData, ← readLightData)
  | 11 => return opt none
  | 12 => return opt $ some (← readLightData)
  | 13 => return eit $ .left (← readLightData)
  | 14 => return eit $ .right (← readLightData)
  | x => throw s!"Invalid LightData tag: {x}"

def ofByteArray (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run readLightData ⟨bytes, bytes.size, rfl⟩) 0).1

instance : Encodable LightData ByteArray String where
  encode := toByteArray
  decode := ofByteArray

end SerDe

section Hashing

protected partial def hash (d : LightData) : ByteVector 32 :=
  d.toByteArray.blake3

instance : HashRepr LightData (ByteVector 32) where
  hashFunc := LightData.hash
  hashRepr := lnk

end Hashing

end LightData

import YatimaStdLib.ByteArray
import YatimaStdLib.ByteVector
import YatimaStdLib.DataClasses
import YatimaStdLib.Either

inductive LightData
  | bol : Bool   → LightData
  | u8  : UInt8  → LightData
  | u16 : UInt16 → LightData
  | u32 : UInt32 → LightData
  | u64 : UInt64 → LightData
  | lnk : UInt64 → LightData
  | str : String → LightData
  | arr : Array LightData → LightData
  | prd : LightData × LightData → LightData
  | opt : Option LightData → LightData
  | eit : Either LightData LightData → LightData
  | big : (n : UInt8) → Fin (2 ^ (8 * n.toNat)) → LightData
  deriving Inhabited

namespace LightData

partial def beq : LightData → LightData → Bool
  | bol x, bol y
  | u8  x, u8  y
  | u16 x, u16 y
  | u32 x, u32 y
  | u64 x, u64 y
  | lnk x, lnk y
  | str x, str y => x == y
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
  | big n₁ f₁, big n₂ f₂ => if n₁ == n₂ then f₁.val == f₂.val else false
  | _, _ => false

instance : BEq LightData := ⟨beq⟩

partial def toString : LightData → String
  | bol true  => "tt"
  | bol false => "ff"
  | u8  x => s!"{x}ᵤ₈"
  | u16 x => s!"{x}ᵤ₁₆"
  | u32 x => s!"{x}ᵤ₃₂"
  | u64 x => s!"{x}ᵤ₆₄"
  | lnk x => s!"↑{x}"
  | str x => s!"\"{x}\""
  | arr x => s!"⟨{", ".intercalate $ x.data.map toString}⟩"
  | prd (x, y) => s!"({x.toString}, {y.toString})"
  | opt none => "?"
  | opt $  some  x => s!"!{x.toString}"
  | eit $ .left  x => s!"←{x.toString}"
  | eit $ .right x => s!"→{x.toString}"
  | big n f => s!"{n.toNat.toSubscriptString}{f.val}"

instance : ToString LightData := ⟨toString⟩

section DataToOfLightData

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

end DataToOfLightData

section LightDataToOfByteArray

def tag : LightData → UInt8
  | bol false => 0
  | bol true  => 1
  | u8  _ => 2
  | u16 _ => 3
  | u32 _ => 4
  | u64 _ => 5
  | lnk _ => 6
  | str _ => 7
  | arr _ => 8
  | prd _ => 9
  | opt    none    => 10
  | opt $  some  _ => 11
  | eit $ .left  _ => 12
  | eit $ .right _ => 13
  | big .. => 14

partial def toByteArray (d : LightData) : ByteArray :=
  match d with
  | bol _ => .mk #[d.tag]
  | u8  x => .mk #[d.tag, x]
  | u16 x | u32 x | u64 x | lnk x => .mk #[d.tag] ++ x.toByteArrayC
  | str x => let x := x.toUTF8; .mk #[d.tag] ++ toByteArray x.size ++ x
  | arr x => x.foldl (fun acc x => acc.append x.toByteArray)
    (⟨#[d.tag]⟩ ++ toByteArray x.size)
  | prd (x, y) => .mk #[d.tag] ++ x.toByteArray ++ y.toByteArray
  | opt none => .mk #[d.tag]
  | opt $ some x | eit $ .left x | eit $ .right x => ⟨#[d.tag]⟩ ++ x.toByteArray
  | big n f =>
    let bytes := f.val.toByteArrayLE
    .mk #[d.tag, n] ++ (bytes.pushZeros (n.toNat - bytes.size))

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

def readByteArray (n : Nat) : OfBytesM $ ByteVector n := do
  let idx ← get
  let ctx ← read
  if idx + n - 1 < ctx.size then
    set $ idx + n
    return ⟨ctx.bytes.copySlice idx .empty 0 n, sorry⟩
  else throw s!"Not enough data to read {n} bytes (size {ctx.size}, idx {idx})"

def readUInt16 : OfBytesM UInt16 :=
  return (← readByteArray 2).toUInt16

def readUInt32 : OfBytesM UInt32 :=
  return (← readByteArray 4).toUInt32

def readUInt64 : OfBytesM UInt64 :=
  return (← readByteArray 8).toUInt64

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
  | 6 => return lnk $ ← readUInt64
  | 7 => return str $ .fromUTF8Unchecked $ (← readByteArray (← readNat)).1
  | 8 =>
    return arr $ ← List.range (← readNat) |>.foldlM (init := #[])
      fun acc _ => do pure $ acc.push (← readLightData)
  | 9 => return prd (← readLightData, ← readLightData)
  | 10 => return opt none
  | 11 => return opt $ some (← readLightData)
  | 12 => return eit $ .left (← readLightData)
  | 13 => return eit $ .right (← readLightData)
  | 14 =>
    let len ← readUInt8
    let lenNat := len.toNat
    let lenNat8 := 8 * lenNat
    let h : (2 ^ lenNat8).isPowerOfTwo := .intro lenNat8 rfl
    return big len $
      .ofNat' (← readByteArray lenNat).1.asLEtoNat (Nat.pos_of_isPowerOfTwo h)
  | x => throw s!"Invalid LightData tag: {x}"

def ofByteArray (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run readLightData ⟨bytes, bytes.size, rfl⟩) 0).1

instance : Encodable LightData ByteArray String where
  encode := toByteArray
  decode := ofByteArray

end LightDataToOfByteArray

section Hashing

protected partial def hash (d : LightData) : UInt64 :=
  match d with
  | bol x | u8 x | u16 x | u32 x | u64 x | lnk x | str x => hash (d.tag, x)
  | arr x => hash (d.tag, x.map (·.hash))
  | prd (x, y) => hash (d.tag, x.hash, y.hash)
  | opt none => hash (d.tag, 0)
  | opt $  some  x
  | eit $ .left  x
  | eit $ .right x => hash (d.tag, x.hash)
  | big n f => hash (d.tag, n, f.val.toByteArrayLE.data)

instance : HashRepr LightData UInt64 where
  hashFunc := LightData.hash
  hashRepr := lnk

end Hashing

end LightData

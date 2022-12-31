import YatimaStdLib.ByteArray
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
  deriving Inhabited, BEq

namespace LightData

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

instance : ToString LightData := ⟨LightData.toString⟩

section DataToOfLightData

partial def ofNat (x : Nat) : LightData :=
  if x < UInt8.size then u8 (.ofNat x)
  else if x < UInt16.size then u16 (.ofNat x)
  else if x < UInt32.size then u32 (.ofNat x)
  else if x < UInt64.size then u64 (.ofNat x)
  else ofNat $ x % UInt64.size -- overflow

instance : DataMap LightData LightData ε := ⟨id, pure⟩

instance : DataMap Bool LightData String where
  ser := bol
  de | bol x => pure x | x => throw s!"Expected a boolean but got {x}"

instance : DataMap Nat LightData String where
  ser := ofNat
  de
    | u8 x | u16 x | u32 x | u64 x => pure x.toNat
    | x => throw s!"Expected a numeric value but got {x}"

instance : DataMap String LightData String where
  ser := str
  de | str x => pure x | x => throw s!"Expected a string but got {x}"

variable [h : DataMap α LightData String]

instance : DataMap (Array α) LightData String where
  ser x := arr $ x.map DataMap.ser
  de | arr x => x.mapM DataMap.de | x => throw s!"Expected an array but got {x}"

instance : DataMap (List α) LightData String where
  ser x := arr $ .mk $ x.map DataMap.ser
  de | arr x => x.data.mapM DataMap.de | x => throw s!"Expected an array but got {x}"

instance : DataMap (Option α) LightData String where
  ser | none => opt none | some a => opt $ some (DataMap.ser a)
  de
    | opt none => pure none
    | opt $ some x => return some (← DataMap.de x)
    | x => throw s!"Expected an option but got {x}"

variable [h' : DataMap β LightData String]

instance : DataMap (α × β) LightData String where
  ser | (a, b) => prd (h.ser a, h'.ser b)
  de
    | prd (a, b) => return (← h.de a, ← h'.de b)
    | x => throw s!"Expected a prod but got {x}"

instance : DataMap (Either α β) LightData String where
  ser | .left a => eit $ .left (h.ser a) | .right b => eit $ .right (h'.ser b)
  de
    | eit (.left a) => return .left $ ← h.de a
    | eit (.right b) => return .right $ ← h'.de b
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

partial def toByteArray (d : LightData) : ByteArray :=
  match d with
  | bol false => .mk #[d.tag]
  | bol true  => .mk #[d.tag]
  | u8  x     => .mk #[d.tag, x]
  | u16 x
  | u32 x
  | u64 x
  | lnk x => .mk #[d.tag] ++ x.toByteArrayC
  | str x => let x := x.toUTF8; .mk #[d.tag] ++ toByteArray x.size ++ x
  | arr x =>
    let init := ⟨#[d.tag]⟩ ++ toByteArray x.size
    x.foldl (fun acc x => acc.append x.toByteArray) init
  | prd (x, y) => .mk #[d.tag] ++ x.toByteArray ++ y.toByteArray
  | opt none => .mk #[d.tag]
  | opt $  some  x
  | eit $ .left  x
  | eit $ .right x => .mk #[d.tag] ++ x.toByteArray

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

def readBool : OfBytesM Bool := do
  match ← readUInt8 with
  | 0 => return false
  | 1 => return true
  | x => throw s!"Invalid data for bool: {x}"

def readByteArray (n : Nat) : OfBytesM ByteArray := do
  let idx ← get
  let ctx ← read
  if idx + n - 1 < ctx.size then
    set $ idx + n
    return ctx.bytes.copySlice idx .empty 0 n
  else throw s!"Not enough data to read {n} bytes (size {ctx.size}, idx {idx})"

def readUInt16 : OfBytesM UInt16 :=
  return .ofByteArrayC $ ← readByteArray 2

def readUInt32 : OfBytesM UInt32 :=
  return .ofByteArrayC $ ← readByteArray 4

def readUInt64 : OfBytesM UInt64 :=
  return .ofByteArrayC $ ← readByteArray 8

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
  | 7 => return str $ .fromUTF8Unchecked $ ← readByteArray (← readNat)
  | 8 =>
    return arr $ ← List.range (← readNat) |>.foldlM (init := #[]) fun acc _ => do
      pure $ acc.push (← readLightData)
  | 9 => return prd (← readLightData, ← readLightData)
  | 10 => return opt none
  | 11 => return opt $ some (← readLightData)
  | 12 => return eit $ .left (← readLightData)
  | 13 => return eit $ .right (← readLightData)
  | x => throw s!"Invalid LightData tag: {x}"

def ofByteArray (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run readLightData ⟨bytes, bytes.size, by eq_refl⟩) 0).1

instance : DataMap LightData ByteArray String where
  ser := toByteArray
  de  := ofByteArray

end LightDataToOfByteArray

section Hashing

protected partial def hash (d : LightData) : UInt64 :=
  match d with
  | bol x
  | u8  x
  | u16 x
  | u32 x
  | u64 x
  | lnk x
  | str x => hash (d.tag, x)
  | arr x => hash (d.tag, x.map (·.hash))
  | prd (x, y) => hash (d.tag, x.hash, y.hash)
  | opt none => hash (d.tag, 0)
  | opt $  some  x
  | eit $ .left  x
  | eit $ .right x => hash (d.tag, x.hash)

instance : HashRepr LightData UInt64 where
  hashFunc := LightData.hash
  hashRepr := lnk

end Hashing

end LightData

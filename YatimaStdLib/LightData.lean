import YatimaStdLib.ByteArray
import YatimaStdLib.DataClasses

inductive LightData
  | nil : LightData
  | bol : Bool   → LightData
  | u8  : UInt8  → LightData
  | u16 : UInt16 → LightData
  | u32 : UInt32 → LightData
  | u64 : UInt64 → LightData
  | lnk : UInt64 → LightData
  | str : String → LightData
  | arr : Array LightData → LightData
  deriving Inhabited, BEq

namespace LightData

partial def toString : LightData → String
  | .nil       => "nil"
  | .bol true  => "tt"
  | .bol false => "ff"
  | .u8  x => s!"{x}ᵤ₈"
  | .u16 x => s!"{x}ᵤ₁₆"
  | .u32 x => s!"{x}ᵤ₃₂"
  | .u64 x => s!"{x}ᵤ₆₄"
  | .lnk x => s!"{x}↑"
  | .str x => s!"\"{x}\""
  | .arr x => s!"⟨{", ".intercalate $ x.data.map toString}⟩"

instance : ToString LightData := ⟨LightData.toString⟩

section DataToOfLightData

partial def ofNat (x : Nat) : LightData :=
  if x < UInt8.size then u8 (.ofNat x)
  else if x < UInt16.size then u16 (.ofNat x)
  else if x < UInt32.size then u32 (.ofNat x)
  else if x < UInt64.size then u64 (.ofNat x)
  else ofNat $ x % UInt64.size -- overflow

instance : SerDe LightData LightData ε where
  ser := id
  de  := pure

instance : SerDe Bool LightData String where
  ser := bol
  de | bol x => pure x | x => throw s!"Expected a boolean but got {x}"

instance : SerDe Nat LightData String where
  ser := ofNat
  de
    | u8 x | u16 x | u32 x | u64 x => pure x.toNat
    | x => throw s!"Expected a numeric value but got {x}"

instance : SerDe String LightData String where
  ser := str
  de | str x => pure x | x => throw s!"Expected a string but got {x}"

instance [SerDe α LightData String] : SerDe (Array α) LightData String where
  ser x := arr $ x.map SerDe.ser
  de | arr x => x.mapM SerDe.de | x => throw s!"Expected an array but got {x}"

instance [SerDe α LightData String] : SerDe (List α) LightData String where
  ser x := arr $ .mk $ x.map SerDe.ser
  de | arr x => x.data.mapM SerDe.de | x => throw s!"Expected an array but got {x}"

instance [h : SerDe α LightData String] : SerDe (Option α) LightData String where
  ser | none => nil | some a => arr #[SerDe.ser a]
  de
    | nil => return none
    | arr #[x] => h.de x
    | x => throw s!"Expected an array but got {x}"

instance : OfNat LightData n := ⟨.ofNat n⟩

end DataToOfLightData

section LightDataToOfByteArray

def tag : LightData → UInt8
  | nil   => 0
  | bol _ => 1
  | u8  _ => 2
  | u16 _ => 3
  | u32 _ => 4
  | u64 _ => 5
  | lnk _ => 6
  | str _ => 7
  | arr _ => 8

partial def toByteArray : LightData → ByteArray
  | nil => .mk #[0]
  | d@(bol false) => .mk #[d.tag, 0]
  | d@(bol true) => .mk #[d.tag, 1]
  | d@(u8  x) => .mk #[d.tag, x]
  | d@(u16 x)
  | d@(u32 x)
  | d@(u64 x)
  | d@(lnk x) => .mk #[d.tag] ++ x.toByteArrayC
  | d@(str x) => let x := x.toUTF8; .mk #[d.tag] ++ toByteArray x.size ++ x
  | d@(arr x) =>
    let init := ⟨#[d.tag]⟩ ++ toByteArray x.size
    x.foldl (fun acc x => acc.append x.toByteArray) init

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
  | 0 => return nil
  | 1 => return bol $ ← readBool
  | 2 => return u8  $ ← readUInt8
  | 3 => return u16 $ ← readUInt16
  | 4 => return u32 $ ← readUInt32
  | 5 => return u64 $ ← readUInt64
  | 6 => return lnk $ ← readUInt64
  | 7 => return str $ .fromUTF8Unchecked $ ← readByteArray (← readNat)
  | 8 =>
    return arr $ ← List.range (← readNat) |>.foldlM (init := #[]) fun acc _ => do
      pure $ acc.push (← readLightData)
  | x => throw s!"Invalid LightData tag: {x}"

def ofByteArray (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run readLightData ⟨bytes, bytes.size, by eq_refl⟩) 0).1

instance : SerDe LightData ByteArray String where
  ser := toByteArray
  de  := ofByteArray

end LightDataToOfByteArray

section Hashing

protected partial def hash : LightData → UInt64
  | nil => 0
  | d@(bol x)
  | d@(u8  x)
  | d@(u16 x)
  | d@(u32 x)
  | d@(u64 x)
  | d@(lnk x)
  | d@(str x) => hash (d.tag, x)
  | d@(arr x) => hash (d.tag, x.map (·.hash))

instance : HashRepr LightData UInt64 where
  hashFunc := LightData.hash
  hashRepr := lnk

end Hashing

end LightData

import YatimaStdLib.ByteArray

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

/- TODO : use faster implementations -/

def UInt16.toByteArray' : UInt16 → ByteArray
  | x => let bytes := x.toNat.toByteArrayLE; bytes.pushZeros $ 2 - bytes.size

def UInt32.toByteArray' : UInt32 → ByteArray
  | x => let bytes := x.toNat.toByteArrayLE; bytes.pushZeros $ 4 - bytes.size

def UInt64.toByteArray' : UInt64 → ByteArray
  | x => let bytes := x.toNat.toByteArrayLE; bytes.pushZeros $ 8 - bytes.size

def UInt16.ofByteArray' : ByteArray → UInt16
  | bytes => .ofNat bytes.asLEtoNat

def UInt32.ofByteArray' : ByteArray → UInt32
  | bytes => .ofNat bytes.asLEtoNat

def UInt64.ofByteArray' : ByteArray → UInt64
  | bytes => .ofNat bytes.asLEtoNat
#eval (400).toByteArrayLE

namespace LightData

partial def toString : LightData → String
  | .nil => "nil"
  | .bol true => "tt"
  | .bol false => "ff"
  | .u8  x => s!"{x}u8"
  | .u16 x => s!"{x}u16"
  | .u32 x => s!"{x}u32"
  | .u64 x => s!"{x}u64"
  | .lnk x => s!"{x}↑"
  | .str x => s!"\"{x}\""
  | .arr x => s!"⟪{", ".intercalate $ x.data.map toString}⟫"

instance : ToString LightData := ⟨LightData.toString⟩

partial def ofNat (x : Nat) : LightData :=
  if x < UInt8.size then .u8 (.ofNat x)
  else if x < UInt16.size then .u16 (.ofNat x)
  else if x < UInt32.size then .u32 (.ofNat x)
  else if x < UInt64.size then .u64 (.ofNat x)
  else ofNat $ x % UInt64.size -- overflow

instance : Coe Bool   LightData := ⟨.bol⟩
instance : Coe UInt8  LightData := ⟨.u8⟩
instance : Coe UInt16 LightData := ⟨.u16⟩
instance : Coe UInt32 LightData := ⟨.u32⟩
instance : Coe UInt64 LightData := ⟨.u64⟩
instance : Coe Nat    LightData := ⟨.ofNat⟩
instance : Coe String LightData := ⟨.str⟩

instance : OfNat LightData n := ⟨.ofNat n⟩

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

partial def serialize : LightData → ByteArray
  | nil => .mk #[0]
  | d@(bol false) => .mk #[d.tag, 0]
  | d@(bol true) => .mk #[d.tag, 1]
  | d@(u8  x) => .mk #[d.tag, x]
  | d@(u16 x)
  | d@(u32 x)
  | d@(u64 x)
  | d@(lnk x) => .mk #[d.tag] ++ x.toByteArray'
  | d@(str x) => let x := x.toUTF8; .mk #[d.tag] ++ serialize x.size ++ x
  | d@(arr x) =>
    let init := ⟨#[d.tag]⟩ ++ serialize x.size
    x.foldl (fun acc x => acc.append x.serialize) init

structure DeContext where
  bytes : ByteArray
  size  : Nat
  valid : bytes.size = size

abbrev DeM := ReaderT DeContext $ ExceptT String $ StateM Nat

def deUInt8 : DeM UInt8 := do
  let idx ← get
  let ctx ← read
  if h : idx < ctx.size then
    set idx.succ
    return ctx.bytes.get ⟨idx, by rw [ctx.valid]; exact h⟩
  else throw "No more bytes to read"

def deBool : DeM Bool := do
  match ← deUInt8 with
  | 0 => return false
  | 1 => return true
  | x => throw s!"Invalid data for bool: {x}"

def deByteArray (n : Nat) : DeM ByteArray := do
  let idx ← get
  let ctx ← read
  if ctx.size - idx - 1 < n then
    set $ idx + n
    return ctx.bytes.copySlice idx .empty 0 n
  else throw s!"Not enough data to read {n} bytes (size {ctx.size}, idx {idx})"

def deUInt16 : DeM UInt16 :=
  return .ofByteArray' $ ← deByteArray 2

def deUInt32 : DeM UInt32 :=
  return .ofByteArray' $ ← deByteArray 4

def deUInt64 : DeM UInt64 :=
  return .ofByteArray' $ ← deByteArray 8

def deNat : DeM Nat := do
  match ← deUInt8 with
  | 2 => return (←  deUInt8).toNat
  | 3 => return (← deUInt16).toNat
  | 4 => return (← deUInt32).toNat
  | 5 => return (← deUInt64).toNat
  | x => throw s!"Invalid tag for a numeric value: {x}"

def deString : DeM String :=
  return .fromUTF8Unchecked $ ← deByteArray (← deNat)

partial def deLightData : DeM LightData := do
  match ← deUInt8 with
  | 0 => return .nil
  | 1 => return .bol $ ← deBool
  | 2 => return .u8  $ ← deUInt8
  | 3 => return .u16 $ ← deUInt16
  | 4 => return .u32 $ ← deUInt32
  | 5 => return .u64 $ ← deUInt64
  | 6 => return .lnk $ ← deUInt64
  | 7 => return .str $ ← deString
  | 8 =>
    return .arr $ ← List.range (← deNat) |>.foldlM (init := #[]) fun acc _ => do
      pure $ acc.push (← deLightData)
  | x => throw s!"Invalid LightData tag: {x}"

def deserialize (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run deLightData ⟨bytes, bytes.size, by eq_refl⟩) 0).1

def qq : LightData := .arr #[300, 300]
#eval (qq, deserialize qq.serialize)

end LightData

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

def UInt16.toByteArray : UInt16 → ByteArray
  | _ => sorry

def UInt32.toByteArray : UInt32 → ByteArray
  | _ => sorry

def UInt64.toByteArray : UInt64 → ByteArray
  | _ => sorry

namespace LightData

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
  | d@(bol true)  => .mk #[d.tag, 1]
  | d@(u8  x) => .mk #[d.tag, x]
  | d@(u16 x)
  | d@(u32 x)
  | d@(u64 x)
  | d@(lnk x) => .mk #[d.tag] ++ x.toByteArray
  | d@(str x) => let x := x.toUTF8; .mk #[d.tag] ++ serialize x.size ++ x
  | d@(arr x) =>
    let init := ⟨#[d.tag]⟩ ++ serialize x.size
    x.foldl (fun acc x => acc.append x.serialize) init

def deserialize (bs : ByteArray) : Except String LightData :=
  sorry

end LightData

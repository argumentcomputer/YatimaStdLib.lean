import YatimaStdLib.Bit

def UInt8.showBits (u : UInt8) : String :=
  let numStr := u.toNat |> Nat.toDigits 2
  "".pushn '0' (8 - numStr.length) ++ ⟨numStr⟩

def UInt8.getBit (u : UInt8) (n : Nat) : Bit :=
  if u &&& (1 <<< (7 - n)).toUInt8 == 0 then .zero else .one

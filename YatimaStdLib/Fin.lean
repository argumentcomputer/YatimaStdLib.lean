import YatimaStdLib.Algebra
import YatimaStdLib.Nat
import YatimaStdLib.Int

namespace Fin 

def ofInt {n : Nat} (a : Int) : Fin n.succ := 
  ⟨a.modToNat n.succ, Int.modToNat_le⟩

/- This is copied from core since it is private -/
theorem mlt {b : Nat} : {a : Nat} → a < n → b % n < n
  | 0  , h => Nat.mod_lt _ h
  | _+1, h => Nat.mod_lt _ (Nat.lt_trans (Nat.zero_lt_succ _) h)

def inv : Fin n → Fin n
  | ⟨a, h⟩ => ⟨(Int.modToNat (Nat.gcdA a n) n) % n, mlt h⟩

instance : YatimaStdLib.Inv (Fin n) where
  inv a := Fin.inv a

end Fin

import YatimaStdLib.Int

structure Zmod (_ : Nat) where
  rep : Int

namespace Zmod

instance : Coe Int (Zmod n) where
  coe i := .mk (i % n)

instance : Coe Nat (Zmod n) where
  coe i := .mk (i % n)

open Int

instance : Add (Zmod n) where
  add (a b : Zmod n) := (rep a + rep b) % (n : Int)

instance : Mul (Zmod n) where
  mul (a b : Zmod n) := (rep a * rep b) % (n : Int)

instance : Inhabited (Zmod n) where
  default := .mk 0

instance {n m : Nat} : OfNat (Zmod n) m where
  ofNat := m

def pow' (a : Zmod n) (l : Nat) : Zmod n:=
  match l with
    | 0 => 1
    | k + 1 => a * pow' a k

instance : Pow (Zmod n) Nat where
  pow := pow'

instance : Sub (Zmod n) where
  sub (a b : Zmod n) := (rep a - rep b) % (n : Int)

def modInv (a : Zmod n) : Zmod n := Int.modInv a.rep n

instance : Div (Zmod n) where
  div a b := a * modInv b

instance : HShiftRight (Zmod n) Nat (Zmod n) where
  hShiftRight x k := (x.rep.toNat.shiftRight k) % n

def norm (x : Zmod n) : Nat :=
  let rep := x.rep
  if rep < 0 then (rep - (rep / n - 1) * n).toNat else rep.toNat % n

instance : BEq (Zmod n) where
  beq x y := x.norm == y.norm

instance : Repr (Zmod n) where
  reprPrec n _ := s!"0x{Nat.toDigits 16 (Zmod.norm n) |>.asString}"

end Zmod

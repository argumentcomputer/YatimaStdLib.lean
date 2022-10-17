import YatimaStdLib.Int

abbrev Zmod (_ : Nat) : Type := Int

open Int

namespace Zmod

def ofInt (a : Int) : Zmod n := a

def rep (a : Zmod n) : Int := a

instance : Add (Zmod n) where
  add (a b : Zmod n) := (rep a + rep b) % (n : Int)

notation:50 a "  + " b " mod " n => Add.add (a : Zmod n) (b : Zmod n)

instance : Mul (Zmod n) where
  mul (a b : Zmod n) := (rep a * rep b) % (n : Int)

notation:51 a " * " b " mod " n => Mul.mul (a : Zmod n) (b : Zmod n)

instance : Inhabited (Zmod n) where
  default := 0

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

notation:50 a " - " b " mod " n => Sub.sub (a : Zmod n) (b : Zmod n)

def modInv (a : Zmod n) : Zmod n := Int.modInv a n

instance : Div (Zmod n) where
  div a b := a * modInv b

def Zmod.norm (x : Zmod n) : Nat :=
  if x < 0 then (x.rep - (x.rep / n - 1) * n).toNat else x.toNat

instance : Repr (Zmod n) where
  reprPrec n _ := s!"0x{Nat.toDigits 16 (Zmod.norm n) |>.asString}"

end Zmod
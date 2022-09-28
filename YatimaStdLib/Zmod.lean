import YatimaStdLib.Int

set_option quotPrecheck false

abbrev Zmod (_ : Nat) : Type := Int

open Int

namespace Zmod

def ofInt (a : Int) : Zmod n := a

def rep (a : Zmod n) : Int := a

instance : Add (Zmod n) where
  add (a b : Zmod n) := (rep a + rep b) % (n : Int)

notation a " + " b " mod " n => (a : Zmod n) + (b : Zmod n)

instance : Mul (Zmod n) where
  mul (a b : Zmod n) := (rep a * rep b) % (n : Int)

notation a " * " b " mod " n => (a : Zmod n) * (b : Zmod n)

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

notation a " - " b " mod " n => (a : Zmod n) - (b : Zmod n)

def modInv (a : Zmod n) : Zmod n := Int.modInv a n
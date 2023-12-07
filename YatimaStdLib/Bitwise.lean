import YatimaStdLib.Nat

namespace Bitwise

/-! Some bitwise arithmetics for `Int`s, assuming twos complement. -/

def bdiff a b := a && not b

def bitwise (f : Bool → Bool → Bool) (m' n' : Int) : Int :=
  let go f' m n :=
    if f' false false
      then .negSucc $ Nat.bitwise (fun x y => not $ f' x y) m n
      else .ofNat   $ Nat.bitwise f' m n
  match m', n' with
  | .ofNat m, .ofNat n     => go f m n
  | .ofNat m, .negSucc n   => go (fun x y => f x (not y)) m n
  | .negSucc m, .ofNat n   => go (fun x y => f (not x) y) m n
  | .negSucc m, .negSucc n => go (fun x y => f (not x) (not y)) m n

def lnot : Int → Int
  | .ofNat m   => .negSucc m
  | .negSucc m => .ofNat m

def land : Int → Int → Int
  | .ofNat m,   .ofNat n   => m &&& n
  | .ofNat m,   .negSucc n => .ofNat $ Nat.bitwise bdiff m n
  | .negSucc m, .ofNat n   => .ofNat $ Nat.bitwise bdiff n m
  | .negSucc m, .negSucc n => .negSucc $ m ||| n

def lor : Int → Int → Int
  | .ofNat m,   .ofNat n   => m ||| n
  | .ofNat m,   .negSucc n => .negSucc $ Nat.bitwise bdiff n m
  | .negSucc m, .ofNat n   => .negSucc $ Nat.bitwise bdiff m n
  | .negSucc m, .negSucc n => .negSucc $ m &&& n

def lxor : Int → Int → Int
  | .ofNat m,   .ofNat n   => m ^^^ n
  | .ofNat m,   .negSucc n => .negSucc $ m ^^^ n
  | .negSucc m, .ofNat n   => .negSucc $ m ^^^ n
  | .negSucc m, .negSucc n => m ^^^ n

def shiftLeft : Int → Int → Int
  | .ofNat m,   .ofNat n   => m <<< n
  | .ofNat m,   .negSucc n => m >>> (n+1)
  | .negSucc m, .ofNat n   => .negSucc $ Nat.shiftLeft1 m n
  | .negSucc m, .negSucc n => .negSucc $ m >>> (n+1)

def shiftRight m n := shiftLeft m (-n)

instance : AndOp Int := ⟨land⟩
instance : OrOp Int := ⟨lor⟩
instance : Xor Int := ⟨lxor⟩
instance : ShiftLeft  Int := ⟨shiftLeft⟩
instance : ShiftRight Int := ⟨shiftRight⟩

/-- Turn a negative integer into a positive by taking its bit representation
and interpreting it as unsigned. `size` is the number of bits to assume. -/
def unsign (i : Int) (size : Nat := 64) : Int :=
  match i with
  | .ofNat m => m
  | .negSucc _ => i + ((2 : Int) ^ size)


end Bitwise

class Ring (R : Type) extends Add R, Mul R, Sub R, OfNat R (nat_lit 0), OfNat R (nat_lit 1), HPow R Nat R, BEq R

def natToRing [Ring R] (n : Nat) : R :=
  match n with
    | 0 => 0
    | k + 1 => natToRing k + 1

instance [Ring R] : Coe Nat R where
  coe := natToRing

instance [Ring R] : OfNat R n where
  ofNat := Coe.coe n

instance [Ring R] : Inhabited R where
  default := 0

class Field (K : Type) extends Ring K where
  inv : K → K
  sqrtRatio : K → K → Bool × K

/-- Doubles this element -/
def double [Field K] (k : K) : K := 2 * k

/-- Returns the square root of the field element, if it is a quadratic residue -/
def sqrt [Field K] (k : K) : Option K :=
  let (isSquare, res) := Field.sqrtRatio k 1
  match isSquare with
  | false => none
  | true => some res

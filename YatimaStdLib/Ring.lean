class Ring (R : Type) extends Add R, Mul R, Sub R, OfNat R (nat_lit 0), OfNat R (nat_lit 1), HPow R Nat R

instance [Add R] [Mul R] [Sub R] [OfNat R 0] [OfNat R 1] [HPow R Nat R] : Ring R := {}

def natToRing [Ring R] (n : Nat) : R :=
  match n with
    | 0 => 0
    | k+1 => natToRing k + 1

instance [Ring R] : Coe Nat R where
  coe := natToRing

instance [Ring R] : Inhabited R where
  default := 0
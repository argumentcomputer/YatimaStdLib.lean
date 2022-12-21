class Ring (R : Type) extends Add R, Mul R, Sub R, OfNat R (nat_lit 0), OfNat R (nat_lit 1), HPow R Nat R

instance [Add R] [Mul R] [Sub R] [OfNat R 0] [OfNat R 1] [HPow R Nat R] : Ring R := {}

instance [Ring R] : Inhabited R where
  default := 0
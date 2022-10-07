class Ring (R : Type) extends Add R, Mul R, OfNat R (0 : Nat), HPow R Nat R

instance [Add R] [Mul R] [OfNat R 0] [HPow R Nat R] : Ring R := {}

instance [Ring R] [OfNat R 0] : Inhabited R where
  default := 0
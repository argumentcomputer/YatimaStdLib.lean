class Ring (R : Type) extends Add R, Mul R, Sub R, OfNat R (nat_lit 0), OfNat R (nat_lit 1), 
  HPow R Nat R, BEq R

namespace Ring

instance {R : Type _} [Add R] [Mul R] [Sub R] [OfNat R (nat_lit 0)] [OfNat R (nat_lit 1)] 
  [HPow R Nat R] [BEq R] : Ring R where

instance [Ring R] : Inhabited R where
  default := 0

end Ring

class Field (K : Type) extends Ring K where
  inv : K → K
  sqrt : K → Option K

namespace Field

instance [Field K] : Div K where
  div a b := a * Field.inv b

end Field

namespace Instances

instance ord2beq [Ord T] : BEq T where
  -- beq x y := compare x y == Ordering.eq
  beq x := BEq.beq Ordering.eq ∘ compare x

def ord2compare [Ord T] (x y : T) : Bool :=
  compare x y == Ordering.eq

end Instances
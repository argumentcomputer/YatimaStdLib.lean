/-- Generates the array of nats from 0,...,n by a given n -/
def Array.iota (n : Nat) : Array Nat :=
  Array.mk (List.range n) |>.push n

def Array.join (l : Array (Array A)) : Array A :=
  Array.foldr (. ++ .) #[] l

instance : Monad Array where
  map := Array.map
  pure x := #[x]
  bind l f := Array.join $ Array.map f l

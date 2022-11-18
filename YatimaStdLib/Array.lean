-- generates the array of nats from 0,...,n by a given n
def Array.iota (n : Nat) : Array Nat :=
  match n with
    | 0 => #[0]
    | k+1 => Array.push (iota k) (k + 1)
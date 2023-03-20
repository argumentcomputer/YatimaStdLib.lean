namespace Random

class Random (K : Type _) where
  random {gen : Type u} [RandomGen gen] [Inhabited gen] (g : gen) : K × gen 

namespace Random

instance : Random Bool where
  random := randBool

instance [Random α] [Random β] : Random (α × β) where
  random g :=
    let (a, g) := random g
    let (b, g) := random g
    ((a, b), g)

def list (K : Type _) [Random K] {gen : Type _} [RandomGen gen] [Inhabited gen] (g : gen) (len : Nat) : List K :=
  match len with
  | 0 => []
  | n + 1 => 
    let (k, g) := random g
    k :: list K g n

def array (K : Type _) [Random K] {gen : Type _} [RandomGen gen] [Inhabited gen] (g : gen) (len : Nat) : Array K :=
  Id.run do
    let mut answer := #[]
    let mut (k, g') := random g
    for _ in [:len] do
      (k, g') := random g'
      answer := answer.push k

    return answer

end Random
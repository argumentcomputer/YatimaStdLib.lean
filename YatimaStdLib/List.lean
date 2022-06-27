import YatimaStdLib.Foldable

namespace List

def compareAux [Ord α] : List α → List α → Ordering
  | [], [] => Ordering.eq
  | [], _ => Ordering.lt
  | _, [] => Ordering.gt
  | x::xs, y::ys => match compare x y with
    | Ordering.eq => compareAux xs ys
    | other => other

instance listOrd [Ord α] : Ord (List α) where
  compare := compareAux

def mapOption {α β: Type u} : (α → Option β) → List α → List β
  | _, []      => []
  | f, x :: xs =>
    match f x with
    | none   => mapOption f xs
    | some r => r :: (mapOption f xs)

def catOptions {α : Type u} : List (Option α) → List α := mapOption id

-- mathlib already has this
-- def indexOf' [BEq α] (as : List α) (a : α) : Option Nat :=
--   let rec aux (a : α) (i : Nat) : List α → Option Nat
--     | a' :: as' => if a == a' then some i else aux a (i + 1) as'
--     | []        => none
--   aux a 0 as

protected def fold [HMul M M M] [One M] (l : List M) : M :=
  match l with
    | [] => One.one
    | (x :: xs) => x * List.fold xs

instance : Foldable List where
  fold := List.fold
  foldr := List.foldr
  foldl := List.foldl

end List
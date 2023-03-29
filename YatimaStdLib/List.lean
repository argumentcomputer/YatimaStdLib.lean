import YatimaStdLib.Applicative
import YatimaStdLib.Foldable
import YatimaStdLib.Traversable
import Std.Data.List.Basic

namespace List

def _root_.YatimaStdLib.List.sum [HAdd α α α] [YatimaStdLib.Zero α] (xs : List α) : α :=
  xs.foldl (· + ·) 0

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

open YatimaStdLib (One)

protected def fold [HMul M M M] [One M] : List M → M
  | [] => One.one
  | (x :: xs) => x * List.fold xs

instance : Foldable List where
  fold := List.fold
  foldr := List.foldr
  foldl := List.foldl

def _root_.YatimaStdLib.List.traverse [Applicative F] (f : A → F B) : List A → F (List B) :=
  let cons_f x ys := Applicative.liftA₂ (fun x xs => x :: xs) (f x) ys
  List.foldr cons_f (pure [])

instance : YatimaStdLib.Traversable List where
  traverse := YatimaStdLib.List.traverse

-- the `B` suffix avoids name conflicts with mathlib
def eraseDupB [BEq α] : List α → List α
  | [] => []
  | x::xs =>
    let exs := eraseDupB xs
    if exs.contains x then exs else x::exs

/--
`splitAt`, but it includes the first element at which `p` fails in the first list
e.g. `splitAtP (fun x => x == 3) [3, 1, 2, 3]` will output `[[3, 1], [2, 3]]`
-/
def splitAtP [BEq α] (p : α → Bool) (l : List α) : List α × List α :=
  match l.dropWhile p with
  | [] => (l, [])
  | a::as => ⟨l.takeWhile p ++ [a], as⟩

def extract (l : List α) (b : Nat) (e : Nat) : List α :=
  if b > e then l else
    let lₐ := l.drop b
    lₐ.take $ e - b

partial def mergeM [Monad μ] (cmp : α → α → μ Ordering) : List α → List α → μ (List α)
  | as@(a::as'), bs@(b::bs') => do
    if (← cmp a b) == Ordering.gt
    then List.cons b <$> mergeM cmp as bs'
    else List.cons a <$> mergeM cmp as' bs
  | [], bs => return bs
  | as, [] => return as

def mergePairsM [Monad μ] (cmp: α → α → μ Ordering) : List (List α) → μ (List (List α))
  | a::b::xs => List.cons <$> (mergeM cmp a b) <*> mergePairsM cmp xs
  | xs => return xs

partial def mergeAllM [Monad μ] (cmp: α → α → μ Ordering) : List (List α) → μ (List α)
  | [x] => return x
  | xs => mergePairsM cmp xs >>= mergeAllM cmp

mutual
  partial def sequencesM [Monad μ] (cmp : α → α → μ Ordering) : List α → μ (List (List α))
    | a::b::xs => do
      if (← cmp a b) == .gt
      then descendingM cmp b [a] xs
      else ascendingM cmp b (fun ys => a :: ys) xs
    | xs => return [xs]

  partial def descendingM [Monad μ] (cmp : α → α → μ Ordering) (a : α) (as : List α) : List α → μ (List (List α))
    | b::bs => do
      if (← cmp a b) == .gt
      then descendingM cmp b (a::as) bs
      else List.cons (a::as) <$> sequencesM cmp (b::bs)
    | [] => List.cons (a::as) <$> sequencesM cmp []

  partial def ascendingM [Monad μ] (cmp : α → α → μ Ordering) (a : α) (as : List α → List α) : List α → μ (List (List α))
    | b::bs => do
      if (← cmp a b) != .gt
      then ascendingM cmp b (fun ys => as (a :: ys)) bs
      else List.cons (as [a]) <$> sequencesM cmp (b::bs)
    | [] => List.cons (as [a]) <$> sequencesM cmp []

end

/--
Monadic mergesort, based on the Haskell version:
https://hackage.haskell.org/package/base-4.16.1.0/docs/src/Data-OldList.html#sort
By default we sort from least to greatest; set `rev := true` for greatest to least
-/
def sortByM [Monad μ] (xs: List α) (cmp: α -> α -> μ Ordering) (rev := false) :
    μ (List α) := do
  if rev then
    let revCmp : _ → _ → μ Ordering := fun x y => do
      match (← cmp x y) with
      | .gt => return Ordering.lt
      | .eq => return Ordering.eq
      | .lt => return Ordering.gt
    sequencesM revCmp xs >>= mergeAllM revCmp
  else
    sequencesM cmp xs >>= mergeAllM cmp

/--
Mergesort from least to greatest. To sort from greatest to
-/
def sortBy (cmp : α -> α -> Ordering) (xs: List α) (rev := false) : List α :=
  Id.run do xs.sortByM (cmp <$> · <*> ·) rev

def sort [Ord α] (xs: List α) (rev := false) : List α :=
  sortBy compare xs rev

def groupByMAux [Monad μ] (eq : α → α → μ Bool) : List α → List (List α) → μ (List (List α))
  | a::as, (ag::g)::gs => do match (← eq a ag) with
    | true  => groupByMAux eq as ((a::ag::g)::gs)
    | false => groupByMAux eq as ([a]::(ag::g).reverse::gs)
  | _, gs => return gs.reverse

def groupByM [Monad μ] (p : α → α → μ Bool) : List α → μ (List (List α))
  | []    => return []
  | a::as => groupByMAux p as [[a]]

def joinM [Monad μ] : List (List α) → μ (List α)
  | []      => return []
  | a :: as => do return a ++ (← joinM as)

def pairwise : List α → List (α × α)
  | [ ]
  | [_] => []
  | x :: y :: zs => ((y :: zs).map fun k => (x, k)) ++ (y :: zs).pairwise

def cartesian (as : List α) (bs : List β) : List (α × β) :=
  as.foldl (init := []) fun acc a => acc ++ bs.map fun b => (a, b)

def List.minWith (f : α → β) [LE β] [DecidableRel (@LE.le β _)] : List α → Option α
  | [] => .none
  | a :: as => match (minWith f as) with
    | .some a' => if f a ≤ f a' then .some a else .some a'
    | .none => .some a

end List

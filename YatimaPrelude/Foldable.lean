import Mathlib.Algebra.Group.Defs
import YatimaPrelude.NonEmpty

namespace Foldable

class Foldable (T : Type → Type) where
   fold : [HMul M M M] → [One M] → T M → M
   foldr : (A → B → B) → B → T A → B
   foldl : (A → B → A) → A → T B → A

def foldList [HMul M M M] [One M]
             (l : List M) : M :=
  match l with
    | [] => One.one
    | (x :: xs) => x * foldList xs

instance foldableList : Foldable List where
  fold := foldList
  foldr := List.foldr
  foldl := List.foldl

def foldNE [HMul M M M] (l : NonEmpty.NEList M) : M :=
  match l with
    | .uno x => x
    | .cons x xs => x * foldNE xs

instance foldableNEList : Foldable NonEmpty.NEList where
  fold := foldNE
  foldr := NonEmpty.foldrNE
  foldl := NonEmpty.foldlNE

end Foldable
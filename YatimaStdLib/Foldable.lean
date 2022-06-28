import Mathlib.Algebra.Group.Defs

/-
The Foldable class represents data structures that can be reduced to a summary value one element at a time. 

Inspired by:
https://hackage.haskell.org/package/base-4.16.1.0/docs/Data-Foldable.html#t:Foldable
-/
class Foldable (T : Type → Type) where
  fold : [HMul M M M] → [One M] → T M → M
  foldr : (A → B → B) → B → T A → B
  foldl : (A → B → A) → A → T B → A
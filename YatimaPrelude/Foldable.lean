import Mathlib.Algebra.Group.Defs

class Foldable (T : Type → Type) where
  fold : [HMul M M M] → [One M] → T M → M
  foldr : (A → B → B) → B → T A → B
  foldl : (A → B → A) → A → T B → A
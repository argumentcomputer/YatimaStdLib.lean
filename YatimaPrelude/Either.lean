import Mathlib.Algebra.Group.Defs

namespace Either

inductive Either (L: Type u) (R: Type v) where
| left (l : L)
| right (r : R)

def fixs {A B C : Type} (c : C) : Either A (B × C) → (Either A B) × C
  | .left a => ⟨ .left a, c ⟩
  | .right ⟨ a, b ⟩ => ⟨ .right a, c ⟩

def fixs' {A B C W : Type} [m : Monoid W] (c : C) : Either A (B × C × W) → (Either A B) × C × W
  | .left a => ⟨ .left a, c, m.one ⟩
  | .right ⟨ a, b, w ⟩ => ⟨ .right a, c, w ⟩

end Either
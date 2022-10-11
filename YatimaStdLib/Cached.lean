namespace Cached

structure Cached {α : Type u} {β : Type v} (f : α → β) (x : α) :=
  val : β
  isFX : f x = val
  deriving Repr

instance : EmptyCollection (Cached f x) where emptyCollection := ⟨f x, rfl⟩
instance : Inhabited (Cached f x) where default := {}
instance : Subsingleton (Cached f x) where
  allEq := fun ⟨b, hb⟩ ⟨c, hc⟩ => by subst hb; subst hc; rfl
instance : DecidableEq (Cached f x) := fun _ _ => isTrue (Subsingleton.allEq ..)
instance [ToString β] : ToString (@Cached α β f x) where
  toString c := toString c.val

abbrev Cached' (a : α) := Cached id a

end Cached

import Batteries.Data.RBMap

namespace Batteries.RBMap

open Std

variable {cmp : α → α → Ordering}

def enumList (xs : List α) : RBMap α Nat cmp :=
  RBMap.ofList (xs.enum.map (fun (x, y) => (y, x))) cmp

def unitMap (xs : List α) : RBMap α Unit cmp :=
  RBMap.ofList (xs.map (fun x => (x, ()))) cmp

def filterOut [BEq α] [Ord α] (map : RBMap α β cmp) (t : RBSet α cmp) :
    RBMap α β cmp :=
  RBMap.foldl (fun acc a b => if t.contains a then acc else acc.insert a b) map (init := default)

def fromArray (x : Array (α × β)) : RBMap α β cmp :=
  x.foldl (fun r p => r.insert p.1 p.2) (mkRBMap α β cmp)

/-
Merge two RBMaps, always taking the first value in case of a key being present
in both maps. Intended for set simulation.
-/
def mergeKeySets (m1 : RBMap α β cmp) m2 :=
  RBMap.mergeWith (fun _ v _ => v) m1 m2

instance : Append (RBMap α Unit cmp) := ⟨RBMap.mergeKeySets⟩

def mapValues (m : RBMap α β cmp) (f : β → χ) : RBMap α χ cmp :=
  m.foldl (init := default) fun acc a b => acc.insert a (f b)

def mapKeys [Ord χ] (m : RBMap α β cmp) (f : α → χ) : RBMap χ β compare :=
  m.foldl (init := default) fun acc a b => acc.insert (f a) b

def zipD (m₁ : RBMap α β₁ cmp) (m₂ : RBMap α β₂ cmp) (b₂ : β₂) : RBMap α (β₁ × β₂) cmp :=
  m₁.foldl (init := default) fun acc a b₁ => acc.insert a (b₁, m₂.findD a b₂)


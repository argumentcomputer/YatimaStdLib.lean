import Lean

namespace Std.RBMap

variable {cmp : α → α → Ordering}

def single (a : α) (b : β) : RBMap α β cmp :=
  RBMap.empty.insert a b

def enumList (xs : List α) : RBMap α Nat cmp :=
  RBMap.ofList $ xs.enum.map (fun (x, y) => (y, x))

def unitMap (xs : List α) : RBMap α Unit cmp :=
  RBMap.ofList $ xs.map (fun x => (x, ()))

def filterOut [BEq α] [Ord α] (map : RBMap α β cmp) (t : RBTree α cmp) :
    RBMap α β cmp :=
  map.fold (init := default) fun acc a b =>
    if t.contains a then acc else acc.insert a b

def toKeyList : RBMap α β cmp → List α
  | ⟨t, _⟩ => t.revFold (fun ks k _ => k::ks) []

def toValueList : RBMap α β cmp → List β
  | ⟨t, _⟩ => t.revFold (fun vs _ v => v::vs) []

/-
  Merge two RBMaps, always taking the first value in case of a key
  being present in both maps. Intended for set simulation.
-/
def mergeKeySets (m1 : RBMap α β cmp) m2 :=
  RBMap.mergeBy (fun _ v _ => v) m1 m2

instance : Append (RBMap α Unit cmp) := ⟨RBMap.mergeKeySets⟩

end Std.RBMap

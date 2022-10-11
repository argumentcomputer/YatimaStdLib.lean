import Lean

namespace Std.RBMap

variable {cmp : α → α → Ordering} 

instance : Inhabited (RBMap α β cmp) where
  default := .empty

def single (a : α) (b : β) : RBMap α β cmp := 
  RBMap.empty.insert a b

def enumList (xs : List α) : RBMap α Nat cmp := 
  RBMap.ofList $ xs.enum.map (fun (x, y) => (y, x))

def filterOut [BEq α] [Ord α] (map : RBMap α β cmp) (t : RBTree α cmp) :
    RBMap α β cmp :=
  map.fold (init := default) fun acc a b =>
    if t.contains a then acc else acc.insert a b

end Std.RBMap

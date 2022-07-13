import Std

namespace Std.RBMap 

instance {cmp : α → α → Ordering} : Inhabited (RBMap α β cmp) where
  default := .empty

def single {cmp : α → α → Ordering} (a : α) (b : β) : RBMap α β cmp := 
  RBMap.empty.insert a b

def enumList {cmp : α → α → Ordering} (xs : List α) : RBMap α Nat cmp := 
  RBMap.ofList $ xs.enum.map (fun (x, y) => (y, x))

end Std.RBMap

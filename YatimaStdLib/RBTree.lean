import Std

namespace Std.RBTree

def union [Ord α] (rbₗ rbᵣ : RBTree α compare) : RBTree α compare :=
  if rbₗ.size < rbᵣ.size then
    rbₗ.fold (init := rbᵣ) fun acc a => acc.insert a
  else
    rbᵣ.fold (init := rbₗ) fun acc a => acc.insert a

end Std.RBTree
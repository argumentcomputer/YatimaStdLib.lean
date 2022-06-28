import Std.Data.RBTree
open Std RBNode

namespace Std.RBNode

@[specialize] def toList (map : RBNode α (fun _ => β)) : List (α × β) :=
  map.revFold (fun as a b => (a, b) :: as) []

instance [BEq α] [BEq β] : BEq (RBNode α fun _ => β) where
  beq a b := RBNode.toList a == RBNode.toList b

namespace Std.RBNode

namespace Std.RBMap 

def findM {ordering : α → α → Ordering} [Monad m] [MonadExcept ε m] 
  (rbmap : RBMap α β ordering) (a : α) (e : ε) : m β :=
  match rbmap.find? a with 
  | some b => pure b
  | none => throw e

instance [ToString α] [ToString β] {ordering : α → α → Ordering} : 
  ToString (RBMap α β ordering) :=
  { toString := fun rbmap => s!"{rbmap.toList}" }

end Std.RBMap 
import Std.Data.RBTree
open Std RBNode

namespace Std.RBNode

@[specialize] def toList (map : RBNode α (fun _ => β)) : List (α × β) :=
  map.revFold (fun as a b => (a, b) :: as) []

instance [BEq α] [BEq β] : BEq (RBNode α fun _ => β) where
  beq a b := RBNode.toList a == RBNode.toList b

namespace Std.RBNode
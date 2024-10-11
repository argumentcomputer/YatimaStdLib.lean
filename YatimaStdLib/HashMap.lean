import Std.Data.HashMap
import YatimaStdLib.HashSet

namespace Std

def HashMap.unionWith {α β : Type _} [BEq α] [Hashable α] [Inhabited β] (combine : β → β → β)
    (s₁ s₂ : HashMap α β) : HashMap α β :=
  s₁.fold
    (fun map key value =>
      map.insert key (combine value <| map.getD key default)) s₂

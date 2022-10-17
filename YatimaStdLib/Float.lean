namespace Float

open Float (log)

def Float.toNat : Float → Nat := USize.toNat ∘ Float.toUSize

def logBase (base arg : Float) : Float := log arg / log base

end Float
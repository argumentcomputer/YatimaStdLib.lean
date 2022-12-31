/--
If any `a : α` can be mapped to `d : δ` for a data format `δ` and if there's a
function that maps `d` back to `a`, being allowed to throw errors (of any type
`ε`), then we say that we have a data mapping from `α` to `δ`
-/
class DataMap (α δ : Type _) (ε : outParam $ Type _) where
  ser : α → δ
  de : δ → Except ε α

/-- Any `DataMap α δ _` instance gives us a trivial `Coe α δ` instance -/
instance [DataMap α δ ε] : Coe α δ := ⟨DataMap.ser⟩

/--
If a data format `δ` can be hashed to a type `τ` and if there is a way to
represent terms of `τ` as terms of `δ`, then we say that `δ` has a hash
representation of `τ`
-/
class HashRepr (δ τ : Type _) where
  hashFunc : δ → τ
  hashRepr : τ → δ

/-- A `HashRepr δ UInt64` instance gives us a trivial `Hashable δ` instance -/
instance [HashRepr δ UInt64] : Hashable δ := ⟨HashRepr.hashFunc⟩

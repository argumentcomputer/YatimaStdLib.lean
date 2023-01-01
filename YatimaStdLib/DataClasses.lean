/--
`Encodable α δ ε` means that `α` is encodable into a data format `δ` with some 
injection `encode : α → δ`. It also provides a partial function `decode : δ → α`
that may throws errors `ε` for elements with no preimage
-/
class Encodable (α δ : Type _) (ε : outParam $ Type _) where
  encode : α → δ
  decode : δ → Except ε α

/-- Any `DataMap α δ _` instance gives us a trivial `Coe α δ` instance -/
instance [Encodable α δ ε] : Coe α δ := ⟨Encodable.encode⟩

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

/--
`Encodable α δ` means that `α` is encodable into a data format `δ` with some 
injection `encode : α → δ`. It also provides a partial function
`decode : δ → Except String α` that may throw errors for terms of `δ` without
preimage.

TODO: add deriving macros
-/
class Encodable (α δ : Type _) where
  encode : α → δ
  decode : δ → Except String α

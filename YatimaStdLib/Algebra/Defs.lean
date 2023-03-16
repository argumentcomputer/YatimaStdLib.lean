class Zero.{u} (α : Type u) where
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

class One.{u} (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

class Inv (α : Type u) where
  inv : α → α

class Semigroup (G : Type u) extends Mul G where
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)

class MulOneClass (M : Type u) extends One M, Mul M where
  mul_one : ∀ (a : M), a * 1 = a
  one_mul : ∀ (a : M), 1 * a = a

class Monoid (M : Type u) extends Semigroup M, MulOneClass M 

/-! 
This file is largely a port of `Mathlib`'s `Algebra.Group.Defs`
-/

class Zero.{u} (α : Type u) where
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

class One.{u} (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

class AddSemigroup (A : Type u) extends Add A where
  add_assoc (a b c : A) : (a + b) + c = a + (b + c)

theorem add_assoc {G : Type u} [AddSemigroup G] :
  ∀ a b c : G, (a + b) + c = a + (b + c) :=
  AddSemigroup.add_assoc

class AddCommSemigroup (A : Type u) extends AddSemigroup A where
  add_comm (a b : A) : a + b = b + a

theorem add_comm {A : Type u} [AddCommSemigroup A] (a b : A) : a + b = b + a :=
AddCommSemigroup.add_comm a b
/-
### Cancellative semigroups
-/

class IsAddLeftCancel (A : Type u) [Add A] where
  add_left_cancel (a b c : A) : a + b = a + c → b = c

class IsAddRightCancel (A : Type u) [Add A] where
  add_right_cancel (a b c : A) : b + a = c + a → b = c

section AddLeftCancel_lemmas

variable {A : Type u} [AddSemigroup A] [IsAddLeftCancel A] {a b c : A}

theorem add_left_cancel : a + b = a + c → b = c :=
IsAddLeftCancel.add_left_cancel a b c

theorem add_left_cancel_iff : a + b = a + c ↔ b = c :=
⟨add_left_cancel, congrArg _⟩

-- no `function.injective`?
--theorem add_right_injective (a : G) : function.injective (c * .) :=
--λ a b => add_left_cancel

@[simp] theorem add_right_inj (a : A) {b c : A} : a + b = a + c ↔ b = c :=
⟨add_left_cancel, congrArg _⟩

--theorem add_ne_add_right (a : A) {b c : A} : a + b ≠ a + c ↔ b ≠ c :=
--(add_right_injective a).ne_iff

end AddLeftCancel_lemmas

section AddRightCancel_lemmas

variable {A : Type u} [AddSemigroup A] [IsAddRightCancel A] {a b c : A}

theorem add_right_cancel : b + a = c + a → b = c :=
IsAddRightCancel.add_right_cancel a b c

theorem add_right_cancel_iff : b + a = c + a ↔ b = c :=
⟨add_right_cancel, λ h => h ▸ rfl⟩

@[simp] theorem add_left_inj (a : A) {b c : A} : b + a = c + a ↔ b = c :=
⟨add_right_cancel, λ h => h ▸ rfl⟩

end AddRightCancel_lemmas

/-
### Additive monoids
-/

/-- Typeclass for expressing that a type `M` with + and 0 satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (A : Type u) extends Zero A, Add A where
  add_zero (a : A) : a + 0 = a
  zero_add (a : A) : 0 + a = a

class AddMonoid (A : Type u) extends AddSemigroup A, AddZeroClass A

section AddMonoid_lemmas

variable  {A : Type u} [AddMonoid A] {a b c : A}

@[simp] theorem add_zero (a : A) : a + 0 = a :=
AddMonoid.add_zero a

@[simp] theorem zero_add (a : A) : 0 + a = a :=
AddMonoid.zero_add a

theorem left_neg_eq_right_neg (hba : b + a = 0) (hac : a + c = 0) : b = c :=
by rw [←zero_add c, ←hba, add_assoc, hac, add_zero b]

end AddMonoid_lemmas

/-! ### Additive monoids with one -/

class AddMonoidWithOne (R : Type u) extends AddMonoid R, One R where
  natCast : Nat → R
  natCast_zero : natCast 0 = 0
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1

def Nat.cast [AddMonoidWithOne R] : Nat → R := AddMonoidWithOne.natCast

instance [AddMonoidWithOne R] : CoeTail Nat R where coe := Nat.cast
instance [AddMonoidWithOne R] : CoeHTCT Nat R where coe := Nat.cast

@[simp] theorem Nat.cast_zero [AddMonoidWithOne R] : ((0 : Nat) : R) = 0 := AddMonoidWithOne.natCast_zero
@[simp 500]
theorem Nat.cast_succ [AddMonoidWithOne R] : ((Nat.succ n : Nat) : R) = (n : R) + 1 := AddMonoidWithOne.natCast_succ _
@[simp]
theorem Nat.cast_one [AddMonoidWithOne R] : ((1 : Nat) : R) = 1 := by simp

@[simp] theorem Nat.cast_add [AddMonoidWithOne R] : ((m + n : Nat) : R) = (m : R) + n := by
  induction n <;> simp_all [add_succ, add_assoc]

class Nat.AtLeastTwo (n : Nat) : Prop where
  prop : n ≥ 2
instance : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ $ Nat.succ_le_succ $ Nat.zero_le _

instance [AddMonoidWithOne R] [Nat.AtLeastTwo n] : OfNat R n where
  ofNat := n.cast

@[simp] theorem Nat.cast_ofNat [AddMonoidWithOne R] [Nat.AtLeastTwo n] :
  (Nat.cast (OfNat.ofNat n) : R) = OfNat.ofNat n := rfl

/-
### Commutative additive monoids
-/

class AddCommMonoid (A : Type u) extends AddMonoid A, AddCommSemigroup A where
  -- TODO: doesn't work
  zero_add a := (by rw [add_comm, add_zero])
  add_zero a := (by rw [add_comm, zero_add])

/-
### sub_neg_monoids
Additive groups can "pick up" several equal but not defeq actions of ℤ.
This trick isolates one such action, `gsmul`, and decrees it to
be "the canonical one".
-/

class SubNegMonoid (A : Type u) extends AddMonoid A, Neg A, Sub A where
  sub := λ a b => a + -b
  sub_eq_add_neg : ∀ a b : A, a - b = a + -b

export SubNegMonoid (sub_eq_add_neg)

/-
### Additive groups
-/

class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg (a : A) : -a + a = 0

section AddGroup_lemmas

variable {A : Type u} [AddGroup A] {a b c : A}

@[simp] theorem add_left_neg : ∀ a : A, -a + a = 0 :=
AddGroup.add_left_neg

theorem neg_add_self (a : A) : -a + a = 0 := add_left_neg a

@[simp] theorem neg_add_cancel_left (a b : A) : -a + (a + b) = b :=
by rw [← add_assoc, add_left_neg, zero_add]

theorem neg_eq_of_add_eq_zero (h : a + b = 0) : -a = b :=
left_neg_eq_right_neg (neg_add_self a) h

@[simp] theorem neg_neg (a : A) : -(-a) = a :=
neg_eq_of_add_eq_zero (add_left_neg a)

@[simp] theorem add_right_neg (a : A) : a + -a = 0 := by
  rw [←add_left_neg (-a), neg_neg]

-- synonym
theorem add_neg_self (a : A) : a + -a = 0 := add_right_neg a

@[simp] theorem add_neg_cancel_right (a b : A) : a + b + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

instance (A : Type u) [AddGroup A] : IsAddRightCancel A where
  add_right_cancel a b c h := by
  rw [← add_neg_cancel_right b a, h, add_neg_cancel_right]

instance (A : Type u) [AddGroup A] : IsAddLeftCancel A where
  add_left_cancel a b c h := by
    rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

-- lemma eq_of_sub_eq_zero' (h : a - b = 0) : a = b :=
--   add_right_cancel <| show a + (-b) = b + (-b) by rw [← sub_eq_add_neg, h, add_neg_self]

end AddGroup_lemmas

class AddCommGroup (A : Type u) extends AddGroup A, AddCommMonoid A


/-! ### Additive groups with one -/

class AddGroupWithOne (R : Type u) extends AddMonoidWithOne R, AddGroup R where
  intCast : ℤ → R
  intCast_ofNat : ∀ n : Nat, intCast n = natCast n
  intCast_negSucc : ∀ n : Nat, intCast (Int.negSucc n) = - natCast (n + 1)

def Int.cast [AddGroupWithOne R] : ℤ → R := AddGroupWithOne.intCast

instance [AddGroupWithOne R] : CoeTail ℤ R where coe := Int.cast

-- theorem Int.cast_ofNat [AddGroupWithOne R] : (Int.cast (Int.ofNat n) : R) = Nat.cast n :=
--   AddGroupWithOne.intCast_ofNat _
-- @[simp]
-- theorem Int.cast_negSucc [AddGroupWithOne R] : (Int.cast (Int.negSucc n) : R) = (-(Nat.cast (n + 1)) : R) :=
--   AddGroupWithOne.intCast_negSucc _

-- @[simp] theorem Int.cast_zero [AddGroupWithOne R] : ((0 : ℤ) : R) = 0 := by
--   erw [Int.cast_ofNat, Nat.cast_zero]
-- @[simp] theorem Int.cast_one [AddGroupWithOne R] : ((1 : ℤ) : R) = 1 := by
--   erw [Int.cast_ofNat, Nat.cast_one]

/-
## Multiplicative semigroups, monoids and groups
-/

/-
## Semigroups
-/

class Semigroup (G : Type u) extends Mul G where
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)

export Semigroup (mul_assoc)

class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm (a b : G) : a * b = b * a

export CommSemigroup (mul_comm)

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  mul_one : ∀ (a : M), a * 1 = a
  one_mul : ∀ (a : M), 1 * a = a

/-
### Cancellative semigroups
-/

class IsMulLeftCancel (G : Type u) [Mul G] where
  mul_left_cancel (a b c : G) : a * b = a * c → b = c

class IsMulRightCancel (G : Type u) [Mul G] where
  mul_right_cancel (a b c : G) : b * a = c * a → b = c
section MulLeftCancel

variable {G : Type u} [Semigroup G] [IsMulLeftCancel G] {a b c : G}

theorem mul_left_cancel : a * b = a * c → b = c :=
  IsMulLeftCancel.mul_left_cancel a b c

theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congrArg _⟩

-- no `function.injective`?
--theorem mul_right_injective (a : G) : function.injective (c * .) :=
--λ a b => mul_left_cancel

@[simp] theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congrArg _⟩

--theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
--(mul_right_injective a).ne_iff

end MulLeftCancel

section MulRightCancel

variable {G : Type u} [Semigroup G] [IsMulRightCancel G] {a b c : G}


theorem mul_right_cancel : b * a = c * a → b = c :=
IsMulRightCancel.mul_right_cancel a b c


theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, λ h => h ▸ rfl⟩

@[simp] theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, λ h => h ▸ rfl⟩

end MulRightCancel

/-
### Monoids
-/

class Monoid (M : Type u) extends Semigroup M, MulOneClass M 

/-
### Commutative monoids
-/

class CommMonoid (M : Type u) extends Monoid M where
  mul_comm (a b : M) : a * b = b * a

section CommMonoid
variable {M} [CommMonoid M]

instance : CommSemigroup M where
  mul_comm := CommMonoid.mul_comm

end CommMonoid

/-
### Div inv monoids
-/

class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G :=
(div := λ a b => a * b⁻¹)
(div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹)

/-
### Groups
-/

class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv (a : G) : a⁻¹ * a = 1

class CommGroup (G : Type u) extends Group G where
  mul_comm (a b : G) : a * b = b * a

instance (G : Type u) [CommGroup G] : CommMonoid G where
  mul_comm := CommGroup.mul_comm
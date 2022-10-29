/-!
The `Either` type represents values with two possibilities: a value of type
`Either α β` is either `left α` or `right β`.

The data type is inspired by:
https://hackage.haskell.org/package/base-4.16.1.0/docs/Data-Either.html#t:Either
-/

inductive Either (α : Type u) (β : Type v) where
  | left  : α → Either α β
  | right : β → Either α β

namespace Either

instance [Inhabited α] : Inhabited (Either α β) :=
  ⟨left default⟩

instance [Inhabited β] : Inhabited (Either α β) :=
  ⟨right default⟩

instance [BEq α] [BEq β] : BEq (Either α β) where beq
  | left a₁, left a₂ => a₁ == a₂
  | right b₁, right b₂ => b₁ == b₂
  | _, _ => false

instance [Ord α] [Ord β] : Ord (Either α β) where compare
  | left _, right _ => .lt
  | right _, left _ => .gt
  | left a₁, left a₂ => compare a₁ a₂
  | right b₁, right b₂ => compare b₁ b₂

def isLeft : Either α β → Bool
  | left _ => true
  | _      => false

def isRight : Either α β → Bool
  | right _ => true
  | _       => false

def left? : Either α β → Option α
  | left a => some a
  | right _ => none

def right? : Either α β → Option β
  | left _ => none
  | right b => some b

def leftsArray (l : List $ Either α β) : Array α :=
  l.foldl (init := #[]) fun acc e => match e with
    | left a => acc.push a
    | _ => acc

def lefts (l : List $ Either α β) : List α :=
  leftsArray l |>.data

/-- Faster version of `lefts`, but the resulting order is reversed. -/
def leftsReverse (l : List $ Either α β) : List α :=
  l.foldl (init := []) fun acc e => match e with
    | left a => a :: acc
    | _ => acc

def rightsArray (l : List $ Either α β) : Array β :=
  l.foldl (init := #[]) fun acc e => match e with
    | right b => acc.push b
    | _ => acc

/-- Faster version of `rights`, but the resulting order is reversed. -/
def rightsReverse (l : List $ Either α β) : List β :=
  l.foldl (init := []) fun acc e => match e with
    | right b => b :: acc
    | _ => acc

def rights (l : List $ Either α β) : List β :=
  rightsArray l |>.data

@[specialize] def either (f : α → χ) (g : β → χ) : Either α β → χ
  | .left  a => f a
  | .right b => g b

@[specialize] def map (f : α → χ) (g : β → δ) : Either α β → Either χ δ
  | .left  a => left  $ f a
  | .right b => right $ g b

@[specialize] def mapM [Monad m] (f : α → m χ) (g : β → m δ) :
    Either α β → m (Either χ δ)
  | .left  a => return left  $ ← f a
  | .right b => return right $ ← g b

@[specialize] def mapLeft (f : α → χ) : Either α β → Either χ β
  | left  a => left (f a)
  | right b => right b

@[specialize] def mapLeftM [Monad m] (f : α → m χ) : Either α β → m (Either χ β)
  | left  a => return left (← f a)
  | right b => return right b

@[specialize] def mapRight (f : β → χ) : Either α β → Either α χ
  | left  a => left a
  | right b => right (f b)

@[specialize] def mapRightM [Monad m] (f : β → m χ) : Either α β → m (Either α χ)
  | left  a => return left a
  | right b => return right (← f b)

def fixLeft (a : α) : Either α β → Either α β
  | left _ => left a
  | right b => right b

def fixRight (b : β) : Either α β → Either α β
  | left a => left a
  | right _ => right b

namespace Correctness

/-!
The Either type is sometimes used to represent a value which is either correct
or an error; by convention, the `left` constructor is used to hold an error
value and the `right` constructor is used to hold a correct value
(mnemonic: "right" also means "correct").
-/

scoped instance : Monad (Either ε) where
  map := mapRight
  seq fs xs :=
    match fs with
      | .left l => .left l
      | .right f => mapRight f (xs ())
  pure x := .right x
  bind x f :=
    match x with
      | .left l => .left l
      | .right r => f r

def fixs (c : χ) : Either ε (α × τ) → (Either ε α) × χ
  | .left  e      => (.left  e, c)
  | .right (a, _) => (.right a, c)

def fixs' [OfNat M 1] (c : χ) : Either ε (α × τ × M) → (Either ε α) × χ × M
  | .left  e         => (.left  e, c, 1)
  | .right (a, _, m) => (.right a, c, m)

end Correctness

end Either

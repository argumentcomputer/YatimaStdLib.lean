import YatimaStdLib.Algebra.Defs

/- 
The Either type represents values with two possibilities: a value of type Either a b is either Left a or Right b.

The Either type is sometimes used to represent a value which is either correct or an error; 
by convention, the Left constructor is used to hold an error value and the Right constructor 
is used to hold a correct value (mnemonic: "right" also means "correct").

The data type is inspired by:
https://hackage.haskell.org/package/base-4.16.1.0/docs/Data-Either.html#t:Either
-/
inductive Either (L : Type u) (R : Type v) where
| left (l : L)
| right (r : R)

namespace Either

def either (f : A → C) (g : B → C) (x : Either A B) : C :=
  match x with
    | .left x => f x
    | .right x => g x

def isLeft (x : Either A B) : Bool :=
  match x with
    | .left _ => true
    | _       => false 

def isRight (x : Either A B) : Bool :=
  match x with
    | .right _ => true
    | _        => false 

def lefts (l : List (Either A B)) : List A :=
  match l with
    | [] => []
    | (x::xs) => 
         match x with
           | .left x => x :: lefts xs
           | .right _ => lefts xs

def rights (l : List (Either A B)) : List B :=
  match l with
    | [] => []
    | (x::xs) => 
         match x with
           | .left _ => rights xs
           | .right x => x :: rights xs

def fixs (c : C) : Either A (B × C) → (Either A B) × C
  | .left a => ⟨ .left a, c ⟩
  | .right ⟨ a, b ⟩ => ⟨ .right a, c ⟩

def fixs' [Monoid W] (c : C) : Either A (B × C × W) → (Either A B) × C × W
  | .left a => ⟨ .left a, c, 1 ⟩
  | .right ⟨ a, b, w ⟩ => ⟨ .right a, c, w ⟩

end Either
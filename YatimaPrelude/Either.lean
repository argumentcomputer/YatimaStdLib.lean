import Mathlib.Algebra.Group.Defs


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

def fixs' [Inhabited W] (c : C) : Either A (B × C × W) → (Either A B) × C × W
  | .left a => ⟨ .left a, c, default ⟩
  | .right ⟨ a, b, w ⟩ => ⟨ .right a, c, w ⟩

end Either
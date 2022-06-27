/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-
This file contains definitions for `NEList`, an inductive type meant to
represent non-empty lists.
-/

namespace NonEmpty

inductive NEList (A : Type)
  | uno  : A → NEList A
  | cons : A → NEList A → NEList A

/-- Builds an `NEList A` from a term of `A` and a term of `List A` -/
def toNEList (a : A) : List A → NEList A
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

/-- Creates a term of `List A` from the elements of a term of `NEList A` -/
def toList : NEList A → List A
  | .uno  a   => [a]
  | .cons a b => a :: toList b

/-- Performs a fold-left on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldlNE (f : B → A → B) (init : B) (l : NEList A) : B :=
  match l with
    | .uno x => f init x
    | .cons x xs => foldlNE f (f init x) xs 

/-- Performs a fold-right on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldrNE (f : A → B → B) (init : B) (l : NEList A) : B :=
  match l with
    | .uno x => f x init
    | .cons x xs => foldrNE f (f x init) xs

/-- Performs a map on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def NEList.map (f : α → β) : NEList α → NEList β
  | uno  a    => uno  (f a)
  | cons a as => cons (f a) (map f as)

instance neFun : Functor NEList where
  map := NEList.map

instance ord2beq [Ord T] : BEq T where
  -- beq x y := compare x y == Ordering.eq
  beq x := BEq.beq Ordering.eq ∘ compare x

def ord2compare [Ord T] (x y : T) : Bool :=
  compare x y == Ordering.eq

def ord2beq_nel [Ord T] [BEq T] (x y : NEList T) : Bool :=
  match x, y with
  | .cons u x₁, .cons v y₁ => ord2compare u v && ord2beq_nel x₁ y₁
  | .uno u, .uno v => ord2compare u v
  | _, _ => false

def nonEmpty (l : List A) : Option (NEList A) :=
  match l with
  | [] => Option.none
  | (x :: xs) => NEList.cons x <$> nonEmpty xs

def nonEmptyString (s : String) : Option (NEList Char) :=
  match s with
    | { data := str } => nonEmpty str

end NonEmpty
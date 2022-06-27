/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-
This file contains definitions for `NEList`, an inductive type meant to
represent non-empty lists.
-/
import YatimaStdLib.Foldable

inductive NEList (A : Type)
  | uno  : A → NEList A
  | cons : A → NEList A → NEList A
-- TODO: introduce notation

namespace NEList

/-- Creates a term of `List A` from the elements of a term of `NEList A` -/
def toList : NEList A → List A
  | .uno  a   => [a]
  | .cons a b => a :: toList b

/-- Performs a fold-left on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldl (f : B → A → B) (init : B) (l : NEList A) : B :=
  match l with
    | .uno x => f init x
    | .cons x xs => foldl f (f init x) xs 

/-- Performs a fold-right on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldr (f : A → B → B) (init : B) (l : NEList A) : B :=
  match l with
    | .uno x => f x init
    | .cons x xs => foldr f (f x init) xs

/-- Performs a map on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def map (f : α → β) : NEList α → NEList β
  | uno  a    => uno  (f a)
  | cons a as => cons (f a) (map f as)

instance : Functor NEList where
  map := NEList.map

instance BEqOfOrd [Ord T] : BEq T where
  beq x y := compare x y == Ordering.eq

protected def beq [BEq α] : NEList α → NEList α → Bool
  | .uno a,     .uno b     => a == b
  | .cons a as, .cons b bs => a == b && NEList.beq as bs
  | _,          _          => false

instance [BEq T] : BEq $ NEList T := ⟨NEList.beq⟩
  
def nonEmpty (l : List A) : Option (NEList A) :=
  match l with
  | [] => Option.none
  | (x :: xs) => NEList.cons x <$> nonEmpty xs

def nonEmptyString (s : String) : Option (NEList Char) :=
  match s with
    | { data := str } => nonEmpty str

protected def fold [HMul M M M] (l : NEList M) : M :=
  match l with
    | .uno x => x
    | .cons x xs => x * NEList.fold xs

instance : Foldable NEList where
  fold := NEList.fold
  foldr := NEList.foldr
  foldl := NEList.foldl

end NEList

namespace List 

/-- Builds an `NEList A` from a term of `A` and a term of `List A` -/
def toNEList (a : A) : List A → NEList A
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

end List
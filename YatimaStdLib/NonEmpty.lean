/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-
This file contains definitions for `NEList`, an inductive type meant to
represent non-empty lists.
-/
import YatimaStdLib.Applicative
import YatimaStdLib.Foldable
import YatimaStdLib.Traversable

inductive NEList (α : Type _)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α

-- TODO: add macros for full NEList shortcut syntax, similar to `[a, b, c]`
infixr:67 " :| " => NEList.cons
notation:max "⟦" x "⟧" => NEList.uno x
syntax "⟦"term ", " term,* "⟧" : term

open Lean in
macro_rules
  | `(⟦$x:term, $[$xs:term],*⟧) => do
    let xs := [x] ++ xs.toList |>.reverse
    let mut exprs : TSyntax `term := ← `(⟦$(xs[0]!)⟧)
    for z in xs.tail! do
      exprs := ← `(NEList.cons $z $exprs)
    return exprs

instance [ToString α] : ToString (NEList α) where
  toString
    | ⟦x⟧ => s!"⟦{x}⟧"
    | xs => let rec go | ⟦e⟧ => s!"{e}" | e :| es => s!"{e}, {go es}"
      s!"⟦{go xs}⟧"

namespace NEList

/-- Creates a term of `List α` from the elements of a term of `NEList α` -/
def toList : NEList α → List α
  | .uno  a   => [a]
  | .cons a b => a :: toList b

/-- Performs a fold-left on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldl (f : β → α → β) (init : β) (l : NEList α) : β :=
  match l with
    | .uno x => f init x
    | .cons x xs => foldl f (f init x) xs

/-- Performs a fold-right on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldr (f : α → β → β) (init : β) (l : NEList α) : β :=
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

instance BEqOfOrd [Ord τ] : BEq τ where
  beq x y := compare x y == Ordering.eq

protected def beq [BEq α] : NEList α → NEList α → Bool
  | .uno a,     .uno b     => a == b
  | .cons a as, .cons b bs => a == b && NEList.beq as bs
  | _,          _          => false

instance [BEq τ] : BEq $ NEList τ := ⟨NEList.beq⟩

def nonEmpty (l : List α) : Option (NEList α) :=
  match l with
  | [] => Option.none
  | [x] => Option.some $ NEList.uno x
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

def traverse [Applicative φ] (f : α → φ β) : NEList α → φ (NEList β)
  | ⟦x⟧ => .uno <$> f x
  | x :| xs => Applicative.liftA₂ (.cons) (f x) $ traverse f xs

open Traversable in
instance : Traversable NEList where
  traverse := NEList.traverse

instance : Pure NEList where
  pure x := ⟦x⟧

end NEList

namespace List

/-- Builds an `NEList α` from a term of `α` and a term of `List α` -/
def toNEList (a : α) : List α → NEList α
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

end List

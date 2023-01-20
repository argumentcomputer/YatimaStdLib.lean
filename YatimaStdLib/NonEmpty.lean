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

structure NEList (α : Type u) where
  head : α
  tail : List α

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
    | xs => s!"{xs.head :: xs.tail}"

namespace NEList

/-- Creates a term of `List α` from the elements of a term of `NEList α` -/
def singleton (x : α) : NEList α := ⟨ x , [] ⟩

/-- Creates a term of `List α` from the elements of a term of `NEList α` -/
def toList (xs : NEList α) : List α := xs.head :: xs.tail

/-- Performs a fold-left on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldl (f : β → α → β) (init : β) (l : NEList α) : β :=
  l.toList.foldl f init

/-- Performs a fold-right on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def foldr (f : α → β → β) (init : β) (l : NEList α) : β :=
  l.toList.foldr f init

/-- Performs a map on a `NEList`
The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def map (f : α → β) : NEList α → NEList β
  | .mk head tail => ⟨f head, tail.map f⟩

instance : Functor NEList where
  map := NEList.map

instance BEqOfOrd [Ord τ] : BEq τ where
  beq x y := compare x y == Ordering.eq

protected def beq [BEq α] (xs ys : NEList α) : Bool :=
  xs.toList == ys.toList

instance [BEq τ] : BEq $ NEList τ := ⟨NEList.beq⟩

def nonEmpty (l : List α) : Option (NEList α) :=
  match l with
  | [] => .none
  | (x :: xs) => .some ⟨x, xs⟩

def nonEmptyString (s : String) : Option (NEList Char) :=
  match s with
    | { data := str } => nonEmpty str

protected def fold [HMul M M M] (l : NEList M) : M :=
  let rec go (x : M) : List M → M
    | [] => x
    | y :: ys => x * go y ys
  go l.head l.tail

instance : Foldable NEList where
  fold := NEList.fold
  foldr := NEList.foldr
  foldl := NEList.foldl

def traverse [Applicative φ] (f : α → φ β) (l : NEList α) : φ (NEList β) :=
  let rec go : List α → φ (List β)
    | [] => pure []
    | y :: ys => Applicative.liftA₂ (.cons) (f y) (go ys)
  Applicative.liftA₂ .mk (f l.head) (go l.tail)
  -- | ⟦x⟧ => .uno <$> f x
  -- | x :| xs => Applicative.liftA₂ (.cons) (f x) $ traverse f xs

open Traversable in
instance : Traversable NEList where
  traverse := NEList.traverse

instance : Pure NEList where
  pure x := ⟦x⟧

def compareWith [Ord α] : NEList α → NEList α → Ordering
  | uno a, uno b => compare a b
  | uno a, cons b _ =>
    let cmp := compare a b
    if cmp == .eq then .lt else cmp
  | cons a _, uno b =>
    let cmp := compare a b
    if cmp == .eq then .gt else cmp
  | cons a as, cons b bs =>
    let cmp := compare a b
    if cmp == .eq then compareWith as bs else cmp

instance [Ord α] : Ord $ NEList α := ⟨compareWith⟩

end NEList

namespace List

/-- Builds an `NEList α` from a term of `α` and a term of `List α` -/
def toNEList (a : α) : List α → NEList α
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

end List

def NEList.min {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] : NEList α → α
  | .uno a     => a
  | .cons a as => if a ≤ (min as) then a else (min as)

def NEList.max {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] : NEList α → α
  | .uno a     => a
  | .cons a as => if a ≤ (max as) then (max as) else a
  
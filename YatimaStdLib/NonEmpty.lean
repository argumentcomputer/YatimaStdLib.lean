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
import YatimaStdLib.List

structure NEList (α : Type u) where
  head : α
  tail : List α

instance [ToString α] : ToString (NEList α) where
  toString xs := toString (xs.head :: xs.tail)

namespace NEList

instance : CoeDep (List α) (x :: xs) (NEList α) where
  coe := { head := x, tail := xs }

/-- Creates a term of `List α` from the elements of a term of `NEList α` -/
@[inline]
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
def map (f : α → β) (xs : NEList α) : NEList β :=
  f xs.head :: xs.tail.map f

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
  | (x :: xs) => .some $ x :: xs

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
  Applicative.liftA₂ (· :: ·) (f l.head) (l.tail.traverse f)

open Traversable in
instance : Traversable NEList where
  traverse := NEList.traverse

instance : Pure NEList where
  pure x := [x]

instance [Ord α] : Ord $ NEList α where
  compare xs ys := compare xs.toList ys.toList

def min {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] (as : NEList α) : α :=
  as.tail.foldl (fun a acc => if a ≤ acc then a else acc) as.head

def max {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] (as : NEList α) : α :=
  as.tail.foldl (fun a acc => if a ≤ acc then acc else a) as.head

end NEList

namespace List

/-- Builds an `NEList α` from a term of `α` and a term of `List α` -/
def toNEList (a : α) (as : List α) : NEList α :=
  a :: as

end List

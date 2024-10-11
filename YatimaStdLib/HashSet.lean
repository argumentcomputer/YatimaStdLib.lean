import Std.Data.HashSet

syntax "⦃" term,* "⦄" : term

open Std

open Lean in
macro_rules
  | `(⦃$xs,*⦄) => do
    let mut acc : TSyntax `term ← `(HashSet.empty)
    for x in xs.getElems do
      acc ← `(HashSet.insert $acc $x)
    return ← `($acc)

instance [ToString α] [BEq α] [Hashable α] : ToString (HashSet α) where
  toString set :=
    let content := ", ".intercalate (set |>.toList |>.reverse |>.map fun k => s!"{k}")
    s!"⦃{content}⦄"

namespace Std.HashSet


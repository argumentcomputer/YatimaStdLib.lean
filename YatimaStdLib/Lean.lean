import Lean

namespace Lean.Name

def compareNames : Name → Name → Ordering
  | .anonymous, .anonymous => .eq
  | .num namₗ nₗ, .num namᵣ nᵣ =>
    if nₗ < nᵣ then .lt
    else
      if nₗ > nᵣ then .gt
      else compareNames namₗ namᵣ
  | .str namₗ sₗ, .str namᵣ sᵣ =>
    if sₗ < sᵣ then .lt
    else
      if sₗ > sᵣ then .gt
      else compareNames namₗ namᵣ
  | .anonymous, .num .. => .lt
  | .anonymous, .str .. => .lt
  | .num .., .str .. => .lt
  | .num .., .anonymous => .gt
  | .str .., .anonymous => .gt
  | .str .., .num .. => .gt

instance : Ord Name where
  compare := compareNames

end Lean.Name

namespace Lean.Expr

def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous

def getAppFnArgs (e : Expr) : Name × Array Expr :=
  withApp e fun e a => (e.constName, a)

/-- Converts a `Expr` of a list to a list of `Expr`s -/
partial def toListExpr (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``List.nil, #[_]) => []
  | (``List.cons, #[_, x, xs]) => x :: toListExpr xs
  | _ => []

end Lean.Expr

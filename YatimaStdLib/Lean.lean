import Lean

namespace Lean.Expr

/-- Converts a `Expr` of a list to a list of `Expr`s -/
partial def toListExpr (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``List.nil, #[_]) => []
  | (``List.cons, #[_, x, xs]) => x :: toListExpr xs
  | _ => []

end Lean.Expr

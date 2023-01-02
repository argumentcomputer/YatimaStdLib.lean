import Lean

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

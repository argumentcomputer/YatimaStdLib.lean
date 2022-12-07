import Lean

namespace MLE.DSL

open Lean Elab Meta Term

declare_syntax_cat summand
scoped syntax "(" num num ")" : summand
scoped syntax "(" num "-" noWs num ")" : summand

declare_syntax_cat polynomial
scoped syntax num num "#" summand* : polynomial

def mkNatIntPair (a : Nat) (b : Int) : Nat × Int := (a, b)
def mkNatNatPair (a b : Nat)         : Nat × Nat := (a, b)
def mkKeyValuePair (k : Nat × Nat) (v : List $ Nat × Int) :
    (Nat × Nat) × (List $ Nat × Int) :=
  (k, v)

def elabSummand : TSyntax `summand → TermElabM Expr
  | `(summand | ($b:num $c:num)) =>
    return mkAppN (.const ``mkNatIntPair [])
      #[mkNatLit b.getNat, mkAppN (.const ``Int.ofNat []) #[mkNatLit c.getNat]]
  | `(summand | ($b:num -$c:num)) => do
    let c := match c.getNat with
      | 0 => mkAppN (.const ``Int.ofNat []) #[.const ``Nat.zero []]
      | n + 1 => mkAppN (.const ``Int.negSucc []) #[mkNatLit n]
    return mkAppN (.const ``mkNatIntPair []) #[mkNatLit b.getNat, c]
  | _ => throwUnsupportedSyntax

def elabProdType (n₁ n₂ : Name) : TermElabM Expr :=
  mkAppM ``Prod #[.const n₁ [], .const n₂ []]

def elabPolynomial : TSyntax `polynomial → TermElabM Expr
  | `(polynomial | $w:num $ν:num # $ar:summand*) => do
    let k := mkAppN (.const ``mkNatNatPair []) #[mkNatLit w.getNat, mkNatLit ν.getNat]
    let ar ← ar.data.mapM elabSummand
    let natInt ← elabProdType ``Nat ``Int
    return mkAppN (.const ``mkKeyValuePair []) #[k, ← mkListLit natInt ar]
  | _ => throwUnsupportedSyntax

scoped elab "⟪" ps:polynomial,* "⟫" : term => do
  let natNat ← elabProdType ``Nat ``Nat
  let natInt ← elabProdType ``Nat ``Int
  let listNatInt ← mkAppM ``List #[natInt]
  let polyType ← mkAppM ``Prod #[natNat, listNatInt]
  let ps ← ps.getElems.data.mapM elabPolynomial
  mkListLit polyType ps

#eval ⟪1 2 # (2 4) (5 3), 1 2 # (2 4) (5 0)⟫

end MLE.DSL

import Std.Data.RBMap
import LSpec

/--
A `MultiVarLinPolynomial` represents a multivariate linear polynomial. Each
`(b, c)` pair in the `RBMap` represents a non-zero coefficient.

The coefficient itself is `c + 1`. Note that wee add `1` for the sake of
canonicity, such that a zero coefficient cannot be represented in two different
ways: not being in the `RBMap` or being present with value `0`.

The variables relative to the coefficient are encoded in the base `b`, which, if
understood in binary form, tells whether a variable multiplies the coefficient
or not.

For example, `9·x1·x2` is represented by the pair `(6, 8)` because
* `8 + 1 = 9` (the coefficient)
* `6₁₀ = 110₂` (variables on indexes `1` and `2` are present)
-/
abbrev MultiVarLinPolynomial := Std.RBMap Nat Nat compare

namespace MultiVarLinPolynomial

abbrev Indices := Std.RBSet Nat compare

def Indices.ofBase (b: Nat) : Indices :=
  List.range (b.log2 + 1) |>.foldl (init := default) fun acc idx =>
    if b >>> idx % 2 == 0 then acc else acc.insert idx

def Indices.toBase (is : Indices) : Nat :=
  is.foldl (init := 0) fun acc i => acc + 1 <<< i

open LSpec in -- TODO : prove this as a theorem
#lspec check "roundtripping" $ ∀ n, (Indices.ofBase n).toBase = n

variable (mvlp : MultiVarLinPolynomial)

def toSummands : List $ Nat × Indices :=
  mvlp.foldl (init := []) fun acc b c => (c + 1, Indices.ofBase b) :: acc

def ofSummands (summands : List $ Nat × Indices) : MultiVarLinPolynomial :=
  summands.foldl (init := default) fun acc (c, is) =>
    if c == 0 then acc else acc.insert is.toBase (c - 1)

def toSummandsL : List $ Nat × List Nat :=
  mvlp.foldl (init := []) fun acc b c => (c + 1, Indices.ofBase b |>.toList) :: acc

def ofSummandsL (summands : List $ Nat × List Nat) : MultiVarLinPolynomial :=
  summands.foldl (init := default) fun acc (c, is) =>
    if c == 0 then acc else acc.insert (Indices.toBase (.ofList is _)) (c - 1)

def toString : String :=
  let summandsString := mvlp.toSummands.map fun (coef, indices) =>
    if indices.isEmpty then ToString.toString coef
    else
      let varsProdString := "·".intercalate $ indices.toList.map fun i => s!"x{i}"
      s!"{coef}·{varsProdString}"
  " + ".intercalate summandsString

#eval (ofSummandsL [(2, [1]), (3, [4, 0]), (4, [])]).toString
-- "3·x0·x4 + 2·x1 + 4"

def coef (is : Indices) : Nat :=
  match mvlp.find? is.toBase with
  | some c => c + 1
  | none   => 0

end MultiVarLinPolynomial

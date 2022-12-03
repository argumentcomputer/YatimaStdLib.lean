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

def baseToVarIndices (b: Nat) : List Nat :=
  List.range (b.log2 + 1) |>.foldr (init := []) fun idx acc =>
    if b >>> idx % 2 == 0 then acc else idx :: acc

def varIndicesToBase (is : List Nat) : Nat :=
  is.foldl (init := 0) fun acc i => acc + 1 <<< i

open LSpec in -- TODO : prove this as a theorem
#lspec check "roundtripping" $ ∀ n, varIndicesToBase (baseToVarIndices n) = n

variable (mvlp : MultiVarLinPolynomial)

def toParts : List (Nat × List Nat) :=
  mvlp.toList.map fun (b, c) => (c + 1, baseToVarIndices b)

def ofParts (parts : List (Nat × List Nat)) : MultiVarLinPolynomial :=
  parts.foldl (init := default) fun acc (c, is) =>
    if c == 0 then acc else acc.insert (varIndicesToBase is) (c - 1)

def toString : String :=
  let partsString := mvlp.toParts.map fun (coef, indices) =>
    if indices.isEmpty then ToString.toString coef
    else
      let varsProdString := "·".intercalate $ indices.map fun i => s!"x{i}"
      s!"{coef}·{varsProdString}"
  " + ".intercalate partsString

#eval (ofParts [(2, [1]), (3, [4, 0]), (4, [])]).toString
-- "4 + 2·x1 + 3·x0·x4"

end MultiVarLinPolynomial

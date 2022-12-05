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

def scale (n : Nat) : MultiVarLinPolynomial :=
  if n == 0 then default
  else mvlp.foldl (init := default) fun acc b c => acc.insert b $ n * c.succ - 1

def add (mvlp' : MultiVarLinPolynomial) : MultiVarLinPolynomial :=
  mvlp'.foldl (init := mvlp) fun acc b' c' => match mvlp.find? b' with
    | some c => acc.insert b' $ c + c' + 1
    | none => acc.insert b' c'

def disjointMul (mvlp' : MultiVarLinPolynomial) : MultiVarLinPolynomial :=
  mvlp.foldl (init := default) fun pol b c =>
    mvlp'.foldl (init := pol) fun pol b' c' =>
      pol.insert (b ||| b') (c.succ * c'.succ - 1)

def eval (input : Std.RBMap Nat Nat compare) : Nat :=
  mvlp.foldl (init := 0) fun acc b c =>
    let prod := Indices.ofBase b |>.foldl (init := 1) fun acc i =>
      match input.find? i with
      | none
      | some 0 => 0
      | some v => acc * v
    acc + c.succ * prod

@[inline] def evalL (input : List $ Nat × Nat) : Nat :=
  mvlp.eval $ .ofList input _

namespace Tests

open LSpec

-- TODO : prove this as a theorem
#lspec check "roundtripping" $ ∀ n, (Indices.ofBase n).toBase = n

/-- 3·x0·x4 + 2·x1 + 4 -/
def pol1 := ofSummandsL [(2, [1]), (3, [4, 0]), (4, [])]

/-- 2·x1·x4 + 4·x0·x4 + 1·x1·x3 + 3 -/
def pol2 := ofSummandsL [(1, [1, 3]), (4, [4, 0]), (2, [4, 1]), (3, [])]

/-- 9·x0·x4 + 6·x1 + 12 -/
def pol1Scaled3 := ofSummandsL [(6, [1]), (9, [4, 0]), (12, [])]

/-- 2·x1·x4 + 7·x0·x4 + 1·x1·x3 + 2·x1 + 7 -/
def pol1AddPol2 :=
  ofSummandsL [(1, [1, 3]), (2, [1]), (7, [4, 0]), (2, [4, 1]), (7, [])]

/-- 4·x2·x3 + 12·x2 + 5 -/
def pol3 := ofSummandsL [(12, [2]), (4, [2, 3]), (5, [])]

/--
12·x0·x2·x3·x4 + 36·x0·x2·x4 + 15·x0·x4 + 8·x1·x2·x3 + 16·x2·x3 +
  24·x1·x2 + 48·x2 + 10·x1 + 20
-/
def pol1MulPol3 := ofSummandsL [
  (12, [0, 2, 3, 4]), (36, [0, 2, 4]), (15, [0, 4]),
  (8, [1, 2, 3]), (24, [1, 2]), (10, [1]),
  (16, [2, 3]), (48, [2]), (20, [])]

#lspec
  test "scaling works" (pol1.scale 3 == pol1Scaled3) $
  test "addition is correct" (pol1.add pol2 == pol1AddPol2) $
  test "disjoint multiplication is correct"
    (pol1.disjointMul pol3 == pol1MulPol3) $
  test "evaluation is correct"
    (pol1MulPol3.evalL [(0, 0), (1, 1), (2, 2), (4, 4)] == 174)

end Tests

end MultiVarLinPolynomial

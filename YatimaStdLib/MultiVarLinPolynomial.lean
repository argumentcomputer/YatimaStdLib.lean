import Std.Data.RBMap
import YatimaStdLib.Nat
import LSpec

/--
A `MultiVarLinPolynomial α` represents a multivariate linear polynomial on `α`. Each
`(b, c)` pair in the `RBMap` represents a non-zero coefficient.

The coefficient itself is `c + 1`. Note that wee add `1` for the sake of
canonicity, such that a zero coefficient cannot be represented in two different
ways: not being in the `RBMap` or being present with value `0`.

The variables relative to the coefficient are encoded in the base `b`, which, if
understood in binary form, tells whether a variable multiplies the coefficient
or not.

For example, `9x₁x₂` is represented by the pair `(6, 8)` because
* `8 + 1 = 9` (the coefficient)
* `6₁₀ = 110₂` (variables on indexes `1` and `2` are present)
-/
abbrev MultiVarLinPolynomial α := Std.RBMap Nat α compare

namespace MultiVarLinPolynomial

abbrev Indices := Std.RBSet Nat compare

def Indices.ofBase (b: Nat) : Indices :=
  List.range (b.log2 + 1) |>.foldl (init := default) fun acc idx =>
    if b >>> idx % 2 == 0 then acc else acc.insert idx

def Indices.toBase (is : Indices) : Nat :=
  is.foldl (init := 0) fun acc i => acc + 1 <<< i

variable (mvlp : MultiVarLinPolynomial α) [HMul α α α] [HAdd α α α] [OfNat α 0]

def toSummands : List $ α × Indices :=
  mvlp.foldl (init := []) fun acc b c => (c, Indices.ofBase b) :: acc

def ofSummands (summands : List $ α × Indices) : MultiVarLinPolynomial α :=
  summands.foldl (init := default) fun acc (c, is) =>
    acc.insert is.toBase c

def toSummandsL : List $ α × List Nat :=
  mvlp.foldl (init := []) fun acc b c => (c, Indices.ofBase b |>.toList) :: acc

def ofSummandsL (summands : List $ α × List Nat) : MultiVarLinPolynomial α :=
  summands.foldl (init := default) fun acc (c, is) =>
    acc.insert (Indices.toBase (.ofList is _)) c

def toString [ToString α] : String :=
  let summandsString := mvlp.toSummands.map fun (coef, indices) =>
    indices.foldl (init := ToString.toString coef) fun acc i =>
      s!"{acc}x{i.toSubscriptString}"
  " + ".intercalate summandsString

def scale (a : α) : MultiVarLinPolynomial α :=
  mvlp.foldl (init := default) fun acc b c => acc.insert b $ a * c

def add (mvlp' : MultiVarLinPolynomial α) : MultiVarLinPolynomial α :=
  mvlp'.foldl (init := mvlp) fun acc b' c' => match mvlp.find? b' with
    | some c => acc.insert b' (c + c')
    | none => acc.insert b' c'

def disjointMul (mvlp' : MultiVarLinPolynomial α) : MultiVarLinPolynomial α :=
  mvlp.foldl (init := default) fun pol b c =>
    mvlp'.foldl (init := pol) fun pol b' c' =>
      pol.insert (b ||| b') (c * c')

def eval (input : Array α) : α :=
  let inputSize := input.size
  mvlp.foldl (init := 0) fun acc b c => acc + (
    Indices.ofBase b |>.foldl (init := c) fun acc i =>
      acc * (if h : i < inputSize then input[i]'h else 0))

def eval' (input : Std.RBMap Nat α compare) : α :=
  mvlp.foldl (init := 0) fun acc b c => acc + (
    Indices.ofBase b |>.foldl (init := c) fun acc i =>
      acc * (input.find? i |>.getD 0))

@[inline] def eval'L (input : List $ Nat × α) : α :=
  mvlp.eval' $ .ofList input _

namespace Tests

open LSpec

-- TODO : prove this as a theorem
#lspec check "roundtripping" $ ∀ n, (Indices.ofBase n).toBase = n

/-- 3x₀x₄ + 2x₁ + 4 -/
def pol1 := ofSummandsL [(2, [1]), (3, [4, 0]), (4, [])]

/-- 2x₁x₄ + 4x₀x₄ + 1x₁x₃ + 3 -/
def pol2 := ofSummandsL [(1, [1, 3]), (4, [4, 0]), (2, [4, 1]), (3, [])]

/-- 9x₀x₄ + 6x₁ + 12 -/
def pol1Scaled3 := ofSummandsL [(6, [1]), (9, [4, 0]), (12, [])]

/-- 2x₁x₄ + 7x₀x₄ + 1x₁x₃ + 2x₁ + 7 -/
def pol1AddPol2 :=
  ofSummandsL [(1, [1, 3]), (2, [1]), (7, [4, 0]), (2, [4, 1]), (7, [])]

/-- 4x₂x₃ + 12x₂ + 5 -/
def pol3 := ofSummandsL [(12, [2]), (4, [2, 3]), (5, [])]

/-- 12x₀x₂x₃x₄ + 36x₀x₂x₄ + 15x₀x₄ + 8x₁x₂x₃ + 16x₂x₃ + 24x₁x₂ + 48x₂ + 10x₁ + 20 -/
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
    (pol1MulPol3.eval #[0, 1, 2, 0, 4] == 174)

end Tests

end MultiVarLinPolynomial

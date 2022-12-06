import Std.Data.RBMap
import YatimaStdLib.Nat
import LSpec

/--
A `MultiVarLinPolynomial α` ("MVLP" for short) represents a multivariate linear
polynomial on `α`. Each `(b, c)` pair in the `RBMap` represents a summand with
coefficient `c : α` and variables encoded in `b : Nat`.

The encoding in `b` assumes that the variables are indexed from 0 and their
presence (or absence) on the respective summand are indicated by `1` or `0`, in
binary form, from right to left.

For example, `(6, 9)` encodes `9x₁x₂` because
* `9` is the coefficient
* `6₁₀ = 110₂`, so the variables on indexes `1` and `2` are present
-/
abbrev MultiVarLinPolynomial α := Std.RBMap Nat α compare

namespace MultiVarLinPolynomial

/-- The indices of variables in a summand -/
abbrev Indices := Std.RBSet Nat compare

/-- Extracts the variable indices encoded on a base -/
def Indices.ofBase (b : Nat) : Indices :=
  List.range (b.log2 + 1) |>.foldl (init := default) fun acc idx =>
    if b >>> idx % 2 == 0 then acc else acc.insert idx

/-- Encodes variable indices into a base -/
def Indices.toBase (is : Indices) : Nat :=
  is.foldl (init := 0) fun acc i => acc + 1 <<< i

variable (mvlp : MultiVarLinPolynomial α)

/-- Turns a MVLP into a list of its summands -/
def toSummands : List $ α × Indices :=
  mvlp.foldl (init := []) fun acc b c => (c, Indices.ofBase b) :: acc

/-- Instantiates a MVLP from a list of summands -/
def ofSummands (summands : List $ α × Indices) : MultiVarLinPolynomial α :=
  summands.foldl (init := default) fun acc (c, is) =>
    acc.insert is.toBase c

/-- Similar to `toSummands`, but the resulting indices are lists of `Nat` -/
def toSummandsL : List $ α × List Nat :=
  mvlp.foldl (init := []) fun acc b c => (c, Indices.ofBase b |>.toList) :: acc

/-- Similar to `ofSummands`, but the consumed indices are lists of `Nat` -/
def ofSummandsL (summands : List $ α × List Nat) : MultiVarLinPolynomial α :=
  summands.foldl (init := default) fun acc (c, is) =>
    acc.insert (Indices.toBase (.ofList is _)) c

protected def toString [ToString α] : String :=
  let summandsString := mvlp.toSummands.map fun (c, is) =>
    is.foldl (init := toString c) fun acc i => s!"{acc}x{i.toSubscriptString}"
  " + ".intercalate summandsString

instance [ToString α] : ToString $ MultiVarLinPolynomial α where
  toString x := x.toString

variable [HMul α α α] [HAdd α α α] [OfNat α 0]

/-- Scales the coefficients of a MVLP by a factor `a : α` -/
def scale (a : α) : MultiVarLinPolynomial α :=
  mvlp.foldl (init := default) fun acc b c => acc.insert b $ a * c

/-- The sum of two MVLP defined on the same domain `a` -/
def add (mvlp' : MultiVarLinPolynomial α) : MultiVarLinPolynomial α :=
  mvlp'.foldl (init := mvlp) fun acc b' c' => match mvlp.find? b' with
    | some c => acc.insert b' (c + c')
    | none => acc.insert b' c'

instance : HAdd (MultiVarLinPolynomial α) (MultiVarLinPolynomial α)
  (MultiVarLinPolynomial α) where hAdd x y := x.add y

/--
Multiplying two MVLPs is not as straightforward because multiplication may
increase the power of some variable if it's present on summands of the two
initial MVLPs, resulting on a polynomial that would no longer be linear.

Thus we implement a "disjoint" multiplication, which considers that no variable
is present on summands of the input MVLPs.

For example, `(x + 1) * (y + x + 2)` wouldn't be a disjoint multiplication, but
`(x + 1) * (y + 2)` would.
-/
def disjointMul (mvlp' : MultiVarLinPolynomial α) : MultiVarLinPolynomial α :=
  mvlp.foldl (init := default) fun pol b c =>
    mvlp'.foldl (init := pol) fun pol b' c' =>
      pol.insert (b ||| b') (c * c')

instance : HMul (MultiVarLinPolynomial α) (MultiVarLinPolynomial α)
  (MultiVarLinPolynomial α) where hMul x y := x.disjointMul y

/--
Evaluates a MVLP on an array whose values represent the values of the variables
indexed from 0, matching the indexes of the array. Variables on indexes beyond
the range of the array are considered to have value 0.
-/
def eval (input : Array α) : α :=
  let inputSize := input.size
  mvlp.foldl (init := 0) fun acc b c => acc + (
    Indices.ofBase b |>.foldl (init := c) fun acc i =>
      acc * (if h : i < inputSize then input[i]'h else 0))

/--
Evaluates a MVLP on a map that indicates the value of the variables indexed from
0. Variables whose indexes aren't in the map are considered to have value 0.
-/
def eval' (input : Std.RBMap Nat α compare) : α :=
  mvlp.foldl (init := 0) fun acc b c => acc + (
    Indices.ofBase b |>.foldl (init := c) fun acc i =>
      acc * (input.find? i |>.getD 0))

/-- Similar to `eval'`, but takes a list of `(index, value)` instead -/
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

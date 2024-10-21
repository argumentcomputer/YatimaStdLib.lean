import YatimaStdLib.Bit
import YatimaStdLib.MultilinearPolynomial
import YatimaStdLib.MLE.MultilinearExtension
import YatimaStdLib.MLE.MultilinearLagrangeData

open LSpec
open MLE MultilinearPolynomial

section MLPTests


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

-- TODO : prove this as a theorem
def roundTripTest := check "roundtripping" $ ∀ n, (Indices.ofBase n).toBase = n

def mlpTests :=
  test "scaling works" (pol1.scale 3 == pol1Scaled3) $
  test "addition is correct" (pol1.add pol2 == pol1AddPol2) $
  test "disjoint multiplication is correct" (pol1.disjointMul pol3 == pol1MulPol3) $
  test "evaluation is correct" (pol1MulPol3.eval #[0, 1, 2, 0, 4] == 174) $
  test "scaling with zero results on zero" (pol1.scale 0 == default) $
  test "zero is right-neutral on addition" (pol1 + default == pol1) $
  test "zero is left-neutral on addition" (default + pol1 == pol1) $
  test "multiplying by zero takes to zero" (pol1 * default == default) $
  test "zero multiplied by anything goes to zero" (default * pol1 == default)

end MLPTests

section LagrangeTests

/--
Tests whether the multilinear Lagrange polynomials satisfy their defining property:
`L_i(i) = 1` and `L_i(j) = 0` when `i ≠ j`.
-/
def buildLagrangeTests (size : Nat) : Bool := Id.run do
  let mut results := #[]
  let cases := getBits size
  for t in [:2^size] do
    for t' in [:2^size] do
      let res := if t == t' then 1 else 0
      let b := eval (@multilinearLagrangePolynomial 13 size t) cases[t']! == res
      results := results.push b
  results.all (· == true)

open LSpec

def lagrangeTests := test "Lagrange polys are correct 1" (buildLagrangeTests 1) $
       test "Lagrange polys are correct 2" (buildLagrangeTests 2) $
       test "Lagrange polys are correct 3" (buildLagrangeTests 3) $
       test "Lagrange polys are correct 4" (buildLagrangeTests 4)

end LagrangeTests

section MLETests

/- A couple random functions for testing (Random number generator: My brain)-/
private def f₁ : Nat → Zmod pallasFSize
  | 0 => 7
  | 1 => 11
  | 2 => 3
  | 3 => 5
  | 4 => 12
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | _ => 0

private def f₂ : Nat → Zmod pallasFSize
  | 0 | 5 | 13 => 19
  | 1 | 12 => 7
  | 2 | 7 => 1
  | 3 => 0
  | 4 | 10 | 14 => 9
  | 6 => 28
  | 8 => 3
  | 9 | 11 => 11
  | 15 => 3
  | _ => 0

def buildCases (f : Nat → Zmod pallasFSize) (ν : Nat) : Array (Zmod pallasFSize) := Id.run do
  let mut answer := #[]
  for i in [:2^ν] do
    answer := answer.push (f i)
  return answer

open MultilinearPolynomial in
def buildMLETests (f : Nat → Zmod pallasFSize) (ν : Nat) : Bool := Id.run do
  let mut comps := #[]
  let bins := getBits ν
  let results := buildCases f ν
  let mle := multilinearExtension .pallas f ν
  for t in [:2^ν] do
    let b := eval mle bins[t]! == results[t]!
    comps := comps.push b
  dbg_trace comps
  comps.all (· == true)

def mleTests :=
  test "Multilinear extension works 1" (buildMLETests f₁ 3) $
  test "Multilinear extension works 2" (buildMLETests f₂ 4)

end MLETests

open LSpec

def main := lspecIO $
  roundTripTest ++ mlpTests ++ lagrangeTests ++ mleTests


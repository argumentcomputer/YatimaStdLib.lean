import LSpec
import YatimaStdLib.MLE.MultilinearLagrangeData
import YatimaStdLib.Bit

open MLE MultilinearPolynomial

/-- 
Tests whether the multilinear Lagrange polynomials satisfy their defining property: 
`L_i(i) = 1` and `L_i(j) = 0` when `i ≠ j`. 
-/
def buildTests (size : Nat) : Bool := Id.run do
  let mut results := #[]
  let cases := getBits size
  for t in [:2^size] do
    for t' in [:2^size] do
      let res := if t == t' then 1 else 0
      let b := eval (@multilinearLagrangePolynomial 13 size t) cases[t']! == res
      results := results.push b
  results.all (· == true)

open LSpec

#lspec test "Lagrange polys are correct 1" (buildTests 1) $
       test "Lagrange polys are correct 2" (buildTests 2) $
       test "Lagrange polys are correct 3" (buildTests 3) $
       test "Lagrange polys are correct 4" (buildTests 4) 
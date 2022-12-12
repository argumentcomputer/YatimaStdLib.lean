import LSpec
import YatimaStdLib.MLE.MultilinearLagrangeData

open MLE MultilinearPolynomial

private def Array.padZero [OfNat α (nat_lit 0)] (ar : Array α) (n : Nat) : Array α :=
  let diff := n - ar.size
  ar ++ (.mkArray diff 0)

/-- Generates the array of binary expansions between `0` and `2^n` -/
private def getBins (n : Nat) : Array (Array Nat) := Id.run do
  let mut answer := #[(.mkArray n 0)]
  for x in [1:2^n] do
    let xBits := x |> (Nat.toDigits 2 ·) 
                   |>.map (fun c => c.toNat - 48)
                   |>.reverse
                   |>.toArray
                   |>.padZero n
    answer := answer.push xBits
  return answer

/-- 
Tests whether the multilinear Lagrange polynomials satisfy their defining property: 
`L_i(i) = 1` and `L_i(j) = 0` when `i ≠ j`. 
-/
def buildTests (size : Nat) : Bool := Id.run do
  let mut results := #[]
  let cases := getBins size
  for t in [:2^size] do
    for t' in [:2^size] do
      let res := if t == t' then 1 else 0
      let b := eval (@multilinearLagrangePolynomial 13 size t) cases[t']! == res
      results := results.push b
  dbg_trace results
  results.all (· == true)

open LSpec

#lspec test "Lagrange polys are correct 1" (buildTests 1) $
       test "Lagrange polys are correct 2" (buildTests 2) $
       test "Lagrange polys are correct 3" (buildTests 3) $
       test "Lagrange polys are correct 4" (buildTests 4) 
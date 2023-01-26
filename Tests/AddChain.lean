import LSpec
import YatimaStdLib.AddChain

open Lean LSpec Exp

/- 
NOTE: Writing this test by hand is a work-around for `LSpec` running into a stack overflow.
-/
def main : IO UInt32 := do
  let bytes ← IO.getRandomBytes 8
  IO.setRandSeed bytes.toUInt64BE!.toNat

  IO.println "Starting test"

  for _ in [:1000] do
    let n ← IO.rand 0 1000000
    let m ← IO.rand 0 1000000
    unless fastExp n m == n ^ m do
      IO.println s!"Found an error: fastExp {n} {m} != {n} ^ {m}"
      return 1

  IO.println "Tests passed!"
  return 0
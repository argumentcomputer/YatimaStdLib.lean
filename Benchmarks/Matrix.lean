import YatimaStdLib.Benchmark
import YatimaStdLib.Functions
import YatimaStdLib.Matrix

open Benchmark

instance : FixedSize (Vector Nat) where
  random size := do
    let mut answer := #[]
    let g := (← get).down
    let mut (n, g') := randNat g 0 1000000
    for _ in [:size] do
      (n, g') := RandomGen.next g'
      answer := answer.push n
    return answer
  size vec := vec.size

open FixedSize in
instance : FixedSize (Matrix Nat) where
  random size := do
    let mut answer : Matrix Nat := #[]
    for _ in [:size] do
      answer := answer.push (← random size)
    return answer
  size vec := vec.size

def matrixAction := @Matrix.action Nat

def matrixBench : FunctionAsymptotics $ unCurry matrixAction where
  inputSizes := Array.stdSizes 12

def main (args : List String) : IO UInt32 := benchMain args matrixBench.benchmark 

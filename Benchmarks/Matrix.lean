import YatimaStdLib.Benchmark
import YatimaStdLib.Matrix

open Benchmark

instance : FixedSize (Vector Nat) where
  random size g := do
    let mut answer := #[]
    let mut (n, g') := RandomGen.next g.down
    for _ in [:size] do
      (n, g') := RandomGen.next g'
      answer := answer.push n
    return (answer, .up g')

open FixedSize in
instance : FixedSize (Matrix Nat) where
  random size := do
    let mut answer : Matrix Nat := #[]
    for _ in [:size] do
      answer := answer.push (← random size)
    return answer

def main (args : List String) : IO Unit := benchmarks args (stdSizes 12) 
  (fun ((v : Vector Nat), (m : Matrix Nat)) => m.action v)

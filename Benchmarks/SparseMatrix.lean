import YatimaStdLib.Benchmark
import YatimaStdLib.SparseMatrix

open Benchmark

open RandomGen in
instance : FixedSize (SparseMatrix Nat) where
  random size g := do
    let mut answer : SparseMatrix Nat := .empty 20000 20000
    let mut (n₁, n₂, n₃) := (0,0,0)
    let mut (_, g') := next g.down
    for _ in [:size] do
      (n₁, g') := next g'
      (n₂, g') := next g'
      (n₃, g') := next g'
      answer := answer.insert (n₁ % 20000) (n₂ % 20000) n₃
    return (answer, .up g')

def main (args : List String) : IO Unit := benchmarks args (stdSizes 12) 
  (fun ((m₁ : SparseMatrix Nat), (m₂ : SparseMatrix Nat)) => m₁ * m₂)
  

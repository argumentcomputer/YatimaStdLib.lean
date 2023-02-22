import YatimaStdLib.Benchmark
import YatimaStdLib.Functions
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
  size mat := mat.entries.keys.size

def sparseMatrixMul := @SparseMatrix.multiplication Nat

def sparseMatrixMulBench : FunctionAsymptotics $ unCurry sparseMatrixMul where
  inputSizes := Array.stdSizes 12

def main (args : List String) : IO UInt32 := benchMain args sparseMatrixMulBench.benchmark
  

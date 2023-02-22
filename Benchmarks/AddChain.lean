import YatimaStdLib.Benchmark
import YatimaStdLib.AddChain

open Benchmark Exp

def f₁ : Nat → Nat := (37 ^ ·)

def f₂ : Nat → Nat := fastExp 37

def addChainBench : Comparison f₁ f₂ where
  inputs := #[10000000, 15000000, 20000000, 25000000, 30000000, 35000000, 40000000, 45000000, 50000000]

-- Performance characteristics are just as good, if not slightly better, than Lean's built-in exponentiation
def main (args : List String) : IO UInt32 := benchMain args addChainBench.benchmark

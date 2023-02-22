import YatimaStdLib.Benchmark
import YatimaStdLib.AddChain

open Benchmark Exp

instance : FixedSize Nat where
  random size := return size
  size num := num

def addChainBench : FunctionAsymptotics (fun (n : Nat) => fastExp 37 n) where
  inputSizes := #[10000000, 15000000, 20000000, 25000000, 30000000, 35000000, 40000000, 45000000, 50000000]

-- Performance characteristics are just as good, if not slightly better, than Lean's built-in exponentiation
def main (args : List String) : IO UInt32 := benchMain args addChainBench.benchmark

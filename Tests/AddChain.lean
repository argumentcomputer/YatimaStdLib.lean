import LSpec
import YatimaStdLib.AddChain

open Lean LSpec

/- 
TODO: Getting a stack overflow when running this.
(also getting a stack overflow without the `fastExp` side of the equation)
-/
def main := lspecIO $ 
  check "fastExp works" $ (∀ n m : Nat, fastExp n m = n ^ m)

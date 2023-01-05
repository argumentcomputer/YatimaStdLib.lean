import LSpec.SlimCheck.Control.Random
import YatimaStdLib.Cronos
import YatimaStdLib.Array

section cronos_utils

/--
We include this additional method to output the summary of a `Cronos` type, but assume the keys are
string representations of natural numbers
Note: The output times in are nanoseconds.
-/
def Cronos.orderedSummary (c : Cronos) : String := 
  let orderedKeys := c.data.keysArray.qsort (fun s₁ s₂ => 
    let n₁ := s₁.toNat!
    let n₂ := s₂.toNat!
    n₁ ≤ n₂)
  orderedKeys.foldl (init := "") fun acc key => acc ++ s!"\n{key}:{c.data.find! key}"

end cronos_utils
namespace Benchmark

section fixed_size

open SlimCheck

/--
The class that represents a type `α` that has a measurable size, represented in terms of the 
generator that creates instances of type `α` of given size.
-/
class FixedSize (α : Type u) where
  random (size : Nat) : RandT StdGen α

open FixedSize

instance [FixedSize α] [FixedSize β] : FixedSize (α × β) where
  random (size : Nat) := return (← random size, ← random size)

end fixed_size

section benchmarks

open SlimCheck
open Benchmark

/--
Standard sizes to use as an input to the benchmarking program. The sizes vary over the powers of 
two up to `2^maxSize`
-/
def stdSizes (maxSize : Nat) := Array.iota maxSize |>.map (2 ^ ·)

/--
Auxiliary function that runs the benchmarks, tracks the outputs, and either prints the benchmark 
results or logs them to a file. Contains the main logic used by `Bench.benchmarks`.
-/
def benchmarksAux (sizes : Array Nat) [cmd : FixedSize α] (f : α → β) 
    (logging : Option (Option String) := .none) : IO Unit := do
  let mut cron := Cronos.new
  let mut answers := #[]
  for size in sizes do
    let blah ← IO.runRand $ cmd.random size
    cron ← cron.clock s!"{size}"
    answers := answers.push $ f blah
    cron ← cron.clock s!"{size}"
  match logging with
  | .none => IO.println cron.orderedSummary
  | .some name? => 
    let filename := match name? with | .some name => name | .none => "benchmark"
    IO.FS.writeFile filename (cron.orderedSummary)
/--
Run the benchmarks for the function `f` with input of type `α` whose size varies over the array of
input sizes `sizes`
Allows for logging to a file with the `logging` flag `-l` or `--log` with an optional name 
-/
def benchmarks (args : List String) (sizes : Array Nat) [cmd : FixedSize α] (f : α → β) 
    : IO Unit := do
  if args.isEmpty then
    benchmarksAux sizes f else
    match args with
    | ["-l"] | ["--log"] => benchmarksAux sizes f (.some .none)
    | ["-l", name] | ["--log", name] => benchmarksAux sizes f (.some name)
    | _ => IO.println "Please call with either -l, --log, -l <name>, or --log <name"

end benchmarks

end Benchmark

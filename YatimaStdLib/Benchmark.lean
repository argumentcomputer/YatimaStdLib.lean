import LSpec.SlimCheck.Control.Random
import YatimaStdLib.Array
import YatimaStdLib.RBMap

/-!
# Benchmarking

Some basic utilities for benchmarking. See the `Benchmarks` folder for examples of use.
-/

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

private def _root_.Std.RBMap.orderedSummary [ToString β] [Inhabited β]
    (benchs : Std.RBMap Nat β compare) : String := 
  let orderedKeys := benchs.keysArray.qsort (fun n₁ n₂ => n₁ ≤ n₂)
  orderedKeys.foldl (init := "") fun acc key => acc ++ s!"\n{key}:{benchs.find! key}"

private def _root_.Array.average (arr : Array Nat) : Nat := 
  let sum := arr.foldl (init := 0) fun acc a => acc + a
  sum / arr.size

open Std in
/--
Auxiliary function that runs the benchmarks and tracks the outputs. Contains the main logic used by 
`Bench.benchmarks`.
-/
def benchmarksAux (sizes : Array Nat) [cmd : FixedSize α] (f : α → β) (numIter : Nat := 1) : 
    IO $ RBMap Nat Nat compare := do
  let mut cron : Std.RBMap Nat Nat compare := .empty
  let mut answers := #[]
  for size in sizes do
    let mut times : Array Nat := #[]
    for _ in [:numIter] do
      let blah ← IO.runRand $ cmd.random size
      let before ← IO.monoNanosNow
      answers := answers.push $ f blah
      let after ← IO.monoNanosNow
      let diff := after - before
      times := times.push diff
    cron := cron.insert size times.average

  return cron

open Std in
/--
The benchmarking logger used when benchmarking a single function
-/
def benchmarksLogger [ToString β] [Inhabited β] (cron : RBMap Nat β compare) 
    (logging : Option (Option String) := none) : IO Unit :=
  match logging with
  | .none => IO.println cron.orderedSummary
  | .some name? => 
    let filename := match name? with | .some name => name | .none => "benchmark"
    IO.FS.writeFile filename (cron.orderedSummary)

/--
Run the benchmarks for the function `f` with input of type `α` whose size varies over the array of
input sizes `sizes`
Allows for logging to a file with the `logging` flag `-l` or `--log` with an optional name
Allows for repeated trials to get an average with the `-n <iterations>` or `--num <iterations>` flags
-/
def benchmarksMain (args : List String) (sizes : Array Nat) [cmd : FixedSize α] (f : α → β)
    : IO Unit := do -- FIXME: This is an awful hack because we aren't importing CLI in YSL :(
  let numIdx? := args.findIdx? (fun str => str == "-n" || str == "--num")
  let logIdx? := args.findIdx? (fun str => str == "-l" || str == "--log")
  match numIdx?, logIdx? with 
  | none, none => benchmarksLogger (← benchmarksAux sizes f)
  | some numIdx, none => 
    if let some numIterStr := args.get? (numIdx + 1) then
      if let some numIter := numIterStr.toNat? then
        benchmarksLogger (← benchmarksAux sizes f numIter) 
      else
        IO.println "-n or --num must be followed by a number of iterations"
    else
      IO.println "-n or --num must be followed by a number of iterations"
  | none, some logIdx =>
    if let some logName := args.get? (logIdx + 1) then
      if logName != "-n" || logName != "--num" then
        benchmarksLogger (← benchmarksAux sizes f) (some logName) 
      else
        benchmarksLogger (← benchmarksAux sizes f)
    else
      benchmarksLogger (←benchmarksAux sizes f)
  | some numIdx, some logIdx =>
    if let some numIterStr := args.get? (numIdx + 1) then
      if let some numIter := numIterStr.toNat? then
        if let some logName := args.get? (logIdx + 1) then
          if logName != "-n" || logName != "--num" then
            benchmarksLogger (← benchmarksAux sizes f numIter) (some logName) 
          else
            benchmarksLogger (← benchmarksAux sizes f numIter)
        else
          benchmarksLogger (←benchmarksAux sizes f numIter)
      else
        IO.println "-n or --num must be followed by a number of iterations"
    else
      IO.println "-n or --num must be followed by a number of iterations"

/--
Run the benchmarks for the functions `f` and `g` with input of type `α` whose size varies over the 
array of input sizes `sizes` and display the time comparison
Allows for logging to a file with the `logging` flag `-l` or `--log` with an optional name
Allows for repeated trials to get an average with the `-n <iterations>` or `--num <iterations>` flags

TODO: Refactor this so there isn't as much copy and pasting when I'm less tired
-/
def benchmarksCompare (args : List String) (sizes : Array Nat) [cmd : FixedSize α] (f g : α → β)
    : IO Unit := do
  let numIdx? := args.findIdx? (fun str => str == "-n" || str == "--num")
  let logIdx? := args.findIdx? (fun str => str == "-l" || str == "--log")
  match numIdx?, logIdx? with 
  | none, none => benchmarksLogger $ (← benchmarksAux sizes f).zipD (← benchmarksAux sizes g) 0
  | some numIdx, none => 
    if let some numIterStr := args.get? (numIdx + 1) then
      if let some numIter := numIterStr.toNat? then
        benchmarksLogger $ (← benchmarksAux sizes f numIter).zipD (← benchmarksAux sizes g numIter) 0
      else
        IO.println "-n or --num must be followed by a number of iterations"
    else
      IO.println "-n or --num must be followed by a number of iterations"
  | none, some logIdx =>
    if let some logName := args.get? (logIdx + 1) then
      if logName != "-n" || logName != "--num" then
        benchmarksLogger ((← benchmarksAux sizes f).zipD (← benchmarksAux sizes g) 0) (some logName) 
      else
        benchmarksLogger $ (← benchmarksAux sizes f).zipD (← benchmarksAux sizes g) 0
    else
      benchmarksLogger $ (← benchmarksAux sizes f).zipD (← benchmarksAux sizes g) 0
  | some numIdx, some logIdx =>
    if let some numIterStr := args.get? (numIdx + 1) then
      if let some numIter := numIterStr.toNat? then
        if let some logName := args.get? (logIdx + 1) then
          if logName != "-n" || logName != "--num" then
            benchmarksLogger 
              ((← benchmarksAux sizes f numIter).zipD (← benchmarksAux sizes g numIter) 0) 
              (some logName) 
          else
            benchmarksLogger $ (← benchmarksAux sizes f numIter).zipD (← benchmarksAux sizes g numIter) 0
        else
          benchmarksLogger $ (← benchmarksAux sizes f numIter).zipD (← benchmarksAux sizes g numIter) 0
      else
        IO.println "-n or --num must be followed by a number of iterations"
    else
      IO.println "-n or --num must be followed by a number of iterations"


end benchmarks

end Benchmark

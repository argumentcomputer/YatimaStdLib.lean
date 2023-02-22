import LSpec.SlimCheck.Control.Random
import YatimaStdLib.Array
import YatimaStdLib.RBMap

/-!
# Benchmarking

Some basic utilities for benchmarking. See the `Benchmarks` folder for examples of use.

There are current 4 benchmarking modes implemented:
- `FunctionAsymptotics`: Takes in a single function `f : α → β` where `α` implemented `FixedSize`  
  and a list of input sizes, and runs a benchmark on an array of randomly generated inputs.
- `FixedInput`: Takes in a function `f : α → β` and a array of inputs `inputs : Array α`, and
  benchmarks the time to run `f` on the list of inputs 
- `Comparison`: Takes in two functions `f g : α → β` and an array of inputs `inputs : Array α` and
  benchmarks the relative times for `f` and `g` on the fixed array of inputs
- `RandomComparison`: Similar to the above, but works on a type `a` which implements `FixedSize` and
  runs the benchmark on randomly generated inputs

More modes can be easily implemented using the `unorderedRunnerAux` and `orderedRunnerAux` utilities
by following the guide set out in the above examples

**NOTE**: Functions that are fed into the benchmarking infrastructure must be **uncurried**
          (it is on the TODO to eliminate this restriction)
-/

section fixed_size

open SlimCheck

/--
The class that represents a type `α` that has a measurable size, represented in terms of the 
generator that creates instances of type `α` of given size, and its measure.
-/
class FixedSize (α : Type u) where
  random (size : Nat) : RandT StdGen α
  size (a : α) : Nat

open FixedSize

instance [FixedSize α] [FixedSize β] : FixedSize (α × β) where
  random (size : Nat) := return (← random size, ← random size)
  size p := FixedSize.size p.fst

end fixed_size

namespace Benchmark

/-- 
Logging mode for the benchmark logger. `stdOut` prints to `stdOut` and `fsOut` prints to the
filesystem to a file named `name?` (or `benchmark` if no name is provided) 
-/
inductive LoggingMode
  | stdOut
  | fsOut (name? : Option String)

/-- 
The mode in which the benchmark is being run based off the arguments given to the binary 
`loggingMode` is as aboe and `rounds` determines the number of repetitions are averaged to generate
the timing results
-/
structure TestMode where
  rounds : Nat
  loggingMode : LoggingMode

open Std in
/--
The type that contains all the resulting data from a benchmark run. 

Note: `keys`, `values`, and `keyOrd` can in many cases be left out when defining an instance of
`Result` by having Lean solve them via unification from information coming from `data`.
-/
class Result where
  keys : Type _
  values : Type _
  keyOrd : Ord keys
  data : IO $ RBMap keys values compare
  printKeys : keys → String 
  printVal : values → String 

open Result in
def Result.print (result : Result) : IO $ Array String := 
  return (← result.data).foldl (init := #[]) 
                               (fun acc key res => acc.push s!"{printKeys key}: {printVal res}")

open Std in
/--
The actual Benchmark runner
-/
structure Runner where
  run (rounds : Nat) : Result

open Std in
def unorderedRunnerAux {χ : Type _} [Ord χ] (inputs : Array α) (f : α → β) (numIter : Nat) 
  (order : α → χ) : IO $ RBMap χ Nat compare := do
    let mut cron : Std.RBMap χ Nat compare := .empty
    let mut answers := Array.mkEmpty inputs.size
    for input in inputs do
      let mut times : Array Nat := .mkEmpty numIter
      for _ in [:numIter] do
        let before ← IO.monoNanosNow
        answers := answers.push $ f input 
        let after ← IO.monoNanosNow
        let diff := after - before
        times := times.push diff
      cron := cron.insert (order input) times.average 
    return cron

open Std in
def orderedRunnerAux [Ord α] (inputs : Array α) (f : α → β) (numIter : Nat) : IO $ RBMap α Nat
  compare := unorderedRunnerAux inputs f numIter id

structure FunctionAsymptotics {α : Type _} (f : α → β) where
  inputSizes : Array Nat 

open SlimCheck in
def FunctionAsymptotics.generateInputs [cmd : FixedSize α] {f : α → β} 
  (K : FunctionAsymptotics f) : IO $ Array α := do
    let mut answer : Array α := #[]
    for size in K.inputSizes do
      answer := answer.push (← IO.runRand $ cmd.random size)
    return answer 

def FunctionAsymptotics.benchmark {f : α → β} [FixedSize α] (K : FunctionAsymptotics f) : Runner where
  run rounds := {
    data := do
      let inputs ← FunctionAsymptotics.generateInputs K
      return ← unorderedRunnerAux inputs f rounds FixedSize.size
    printKeys := ToString.toString
    printVal := ToString.toString
  }

structure FixedInput {α : Type _} (f : α → β) where
  inputs : Array α

def FixedInput.benchmark {f : α → β} [Ord α] [ToString α] (K : FixedInput f) 
    : Runner where
  run rounds := {
    data := return ← orderedRunnerAux K.inputs f rounds 
    printKeys := ToString.toString
    printVal := ToString.toString
  }

structure Comparison {α : Type _} (f g : α → β) where
  inputs : Array α  

def Comparison.benchmark {f g : α → β} [Ord α] [ToString α] (K : Comparison f g) 
    : Runner where
  run rounds := {
    data := do
      let fData ← orderedRunnerAux K.inputs f rounds
      let gData ← orderedRunnerAux K.inputs g rounds
      let answer := fData.zipD gData 0
      return answer 
    printKeys := ToString.toString
    printVal := fun (n₁, n₂) => s!"f:{n₁} vs g:{n₂}"
  }

structure RandomComparison {α : Type _} (f g : α → β) where
  inputSizes : Array Nat

open SlimCheck in
def RandomComparison.generateInputs [cmd : FixedSize α] {f g : α → β} 
  (K : RandomComparison f g) : IO $ Array α := do
    let mut answer : Array α := #[]
    for size in K.inputSizes do
      answer := answer.push (← IO.runRand $ cmd.random size)
    return answer 

def RandomComparison.benchmark {f g : α → β} [Ord α] [FixedSize α] (K : RandomComparison f g) 
    : Runner where
  run rounds := {
    data := do
      let inputs ← K.generateInputs 
      let fData ← orderedRunnerAux inputs f rounds
      let gData ← orderedRunnerAux inputs g rounds
      let answer := fData.zipD gData 0
      return answer 
    printKeys := fun key => s!"{FixedSize.size key}"
    printVal := fun (n₁, n₂) => s!"f:{n₁} vs g:{n₂}"
  }

/-- Parse arguments coming from `main` -/
private def parseArgs (args : List String) : Except String TestMode := 
  let numIdx? := args.findIdx? (fun str => str == "-n" || str == "--num")
  let logIdx? := args.findIdx? (fun str => str == "-l" || str == "--log")
  match numIdx?, logIdx? with 
  | none, none => .ok {rounds := 1, loggingMode := .stdOut}
  | some numIdx, none => 
    if let some numIterStr := args.get? (numIdx + 1) then
      if let some numIter := numIterStr.toNat? then
        .ok {rounds := numIter, loggingMode := .stdOut}
      else
        .error "-n or --num must be followed by a number of iterations"
    else
      .error "-n or --num must be followed by a number of iterations"
  | none, some logIdx =>
    if let some logName := args.get? (logIdx + 1) then
      if logName != "-n" && logName != "--num" then
        .ok {rounds := 1, loggingMode := .fsOut logName}
      else
        .ok {rounds := 1, loggingMode := .fsOut none}
    else
      .ok {rounds := 1, loggingMode := .fsOut none}
  | some numIdx, some logIdx =>
    if let some numIterStr := args.get? (numIdx + 1) then
      if let some numIter := numIterStr.toNat? then
        if let some logName := args.get? (logIdx + 1) then
          if logName != "-n" && logName != "--num" then
            .ok {rounds := numIter, loggingMode := .fsOut logName}
          else
            .ok {rounds := numIter, loggingMode := .fsOut none}
        else
          .ok {rounds := numIter, loggingMode := .fsOut none}
      else
        .error "-n or --num must be followed by a number of iterations"
    else
      .error "-n or --num must be followed by a number of iterations"

/-- 
This should be the main function used in a benchmark. In general the workflow will be:

* Define the function(s) you wish to benchmark
* If using randomized test inputs, define a `FixedSize` instance for your input types
* Instantiate the benchmark runner you want to use (`FunctionAsymptotics`, `FixedInput`, etc...)
  with the function and inputs
* Call `benchMain` with the runner from stage 3.
-/
def benchMain (args : List String) (bench : Runner) : IO UInt32 := do
  match parseArgs args with
  | .ok mode => 
    let result ← Runner.run bench mode.rounds |>.print
    match mode.loggingMode with
    | .stdOut => 
      for line in result do
        IO.println line
      return 0
    | .fsOut name? => 
      let filename := match name? with | some name => name | none => "benchmark"
      IO.FS.writeFile filename <| result.foldl (init := "") (fun acc line => acc ++ line ++ "\n")
      return 0
  | .error str => 
    IO.eprintln str
    return 1

  
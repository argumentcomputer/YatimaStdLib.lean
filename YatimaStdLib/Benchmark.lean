import LSpec.SlimCheck.Control.Random
import YatimaStdLib.Array
import YatimaStdLib.RBMap

/-!
# Benchmarking

Some basic utilities for benchmarking. See the `Benchmarks` folder for examples of use.
-/
section random_std

/--
Standard sizes to use as an input to the benchmarking program. The sizes vary over the powers of 
two up to `2^maxSize`
-/
def Array.stdSizes (maxSize : Nat) := Array.iota maxSize |>.map (2 ^ ·)

private def Std.RBMap.orderedSummary [ToString α] [ToString β] [Inhabited β] [Ord α]
    (benchs : Std.RBMap α β compare) : String := 
  let orderedKeys := benchs.keysArray.qsort (fun n₁ n₂ => compare n₁ n₂ |>.isLE)
  orderedKeys.foldl (init := "") fun acc key => acc ++ s!"\n{key}:{benchs.find! key}"

private def Array.average (arr : Array Nat) : Nat := 
  let sum := arr.foldl (init := 0) fun acc a => acc + a
  sum / arr.size

end random_std

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

namespace Benchmark

inductive LoggingMode
  | stdOut
  | fsOut (name : Option String)

structure TestMode where
  rounds : Nat
  loggingMode : LoggingMode

-- TODO : This is wrong, think this through
/-
The idea is that there should be a `Benchmark` typeclass and a `BenchResult` typeclass...
-/

open Std in
class BenchResult where
  keys : Type _
  inst : Ord keys
  data : RBMap keys Nat compare
  printKeys : keys → String 

def BenchResult.print (result : BenchResult) : Array String := sorry

open Std in
class Benchmark (K : Type _) where
  run (f : α → β) (n : Nat) : BenchResult

def parseArgs (args : List String) : Except String TestMode := 
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

open Std in
def benchLogger [ToString α] [Ord α] [ToString β] [Inhabited β] (cron : RBMap α β compare) 
    (logging : LoggingMode) : IO Unit :=
  match logging with
  | .stdOut => IO.println cron.orderedSummary
  | .fsOut name? => 
    let filename := match name? with | .some name => name | .none => "benchmark"
    IO.FS.writeFile filename (cron.orderedSummary)

def benchMain (args : List String) (f : α → β) (bench : Type _) [Benchmark bench] : IO UInt32 := do
  match parseArgs args with
  | .ok mode => 
    let result := Benchmark.run bench f mode.rounds |>.print
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
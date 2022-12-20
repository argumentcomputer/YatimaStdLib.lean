import LSpec.SlimCheck.Control.Random
import YatimaStdLib.Cronos
import YatimaStdLib.Array

namespace Benchmark

section fixed_size

open SlimCheck

class FixedSize (α : Type u) where
  random (size : Nat) : RandT StdGen α

open FixedSize

instance [FixedSize α] [FixedSize β] : FixedSize (α × β) where
  random (size : Nat) := return (← random size, ← random size)

end fixed_size

section benchmarks

open SlimCheck
open Benchmark

def stdSizes (maxSize : Nat) := Array.iota maxSize |>.map (2 ^ ·)

def benchmarks (sizes : Array Nat) [cmd : FixedSize α] (f : α → β) : IO Unit := do
  let mut cron := Cronos.new
  let mut answers := #[]
  for size in sizes do
    let blah ← IO.runRand $ cmd.random size
    cron ← cron.clock s!"{size}"
    answers := answers.push $ f blah
    cron ← cron.clock s!"{size}"
  IO.println cron.summary

end benchmarks

end Benchmark

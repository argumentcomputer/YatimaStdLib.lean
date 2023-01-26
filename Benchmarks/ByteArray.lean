import YatimaStdLib.Benchmark
import YatimaStdLib.ByteArray

open Benchmark FixedSize

open RandomGen in
instance : FixedSize Nat where
  random n g := do
    let mut (m, g') := RandomGen.next g.down
    let mut answer := 0
    for _ in [:n] do
      (m, g') := RandomGen.next g'
      answer := answer * 256 + (m % 256)
    return (answer, .up g')

instance : FixedSize UInt8 where
  random _ := do
    let n : Nat := ← random 10
    return n.toUInt8

instance : FixedSize ByteArray where
  random size := do
    let mut answer := default
    for _ in [:size] do
      answer := answer.push (← random 10)
    return answer

def main (args : List String) : IO Unit := benchmarks args (#[1024, 2048, 4096, 8192, 16384, 32768]) 
  (fun ((b₁ : ByteArray), (b₂ : ByteArray)) => b₁ * b₂)

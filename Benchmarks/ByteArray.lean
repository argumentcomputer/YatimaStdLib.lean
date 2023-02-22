import YatimaStdLib.Benchmark
import YatimaStdLib.ByteArray
import YatimaStdLib.Functions

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
  size n := n

instance : FixedSize UInt8 where
  random _ := do
    let n : Nat := ← random 10
    return n.toUInt8
  size u := u.log2 |>.toNat

instance : FixedSize ByteArray where
  random size := do
    let mut answer := default
    for _ in [:size] do
      answer := answer.push (← random 10)
    return answer
  size b := b.size

def byteArrayMul (b₁ b₂ : ByteArray) : ByteArray := b₁ * b₂

def byteArrayMulBench : FunctionAsymptotics $ unCurry byteArrayMul where
  inputSizes := Array.stdSizes 8

def main (args : List String) : IO UInt32 := benchMain args byteArrayMulBench.benchmark

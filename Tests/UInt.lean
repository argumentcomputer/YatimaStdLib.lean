import LSpec
import YatimaStdLib.UInt

open LSpec

def nats : List Nat := [
  0, 1,
  UInt16.size / 2, UInt16.size-2, UInt16.size-1, UInt16.size, UInt16.size+1,
  UInt32.size / 2, UInt32.size-2, UInt32.size-1, UInt32.size, UInt32.size+1,
  UInt64.size / 2, UInt64.size-2, UInt64.size-1, UInt64.size, UInt64.size+1
]

def main := lspecIO $
  nats.foldl (init := .done) fun tSeq n =>
    let u16 : UInt16 := .ofNat n
    let u32 : UInt32 := .ofNat n
    let u64 : UInt64 := .ofNat n
    tSeq ++
      (test s!"C/Lean match for {u16}₁₆" $
        u16.toByteArray.data == u16.toByteArrayL.data) ++
      (test s!"C/Lean match for {u32}₃₂" $
        u32.toByteArray.data == u32.toByteArrayL.data) ++
      (test s!"C/Lean match for {u64}₆₄" $
        u64.toByteArray.data == u64.toByteArrayL.data)

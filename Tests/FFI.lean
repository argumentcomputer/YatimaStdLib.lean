import LSpec
import YatimaStdLib.UInt
import YatimaStdLib.ByteArray
import YatimaStdLib.ByteVector

open LSpec

def nats : List Nat := [
  0, 1,
  UInt16.size / 2, UInt16.size-2, UInt16.size-1, UInt16.size, UInt16.size+1,
  UInt32.size / 2, UInt32.size-2, UInt32.size-1, UInt32.size, UInt32.size+1,
  UInt64.size / 2, UInt64.size-2, UInt64.size-1, UInt64.size, UInt64.size+1
]

#lspec nats.foldl (init := .done) fun tSeq n =>
  let u16 : UInt16 := .ofNat n
  let u32 : UInt32 := .ofNat n
  let u64 : UInt64 := .ofNat n
  let x : ByteVector 2 := ⟨u16.toByteArrayC, sorry⟩
  let y : ByteVector 4 := ⟨u32.toByteArrayC, sorry⟩
  let z : ByteVector 8 := ⟨u64.toByteArrayC, sorry⟩
  tSeq ++
    (test s!"{n}₁₆ roundtrips" $ x.toUInt16 == u16) ++
    (test s!"{n}₃₂ roundtrips" $ y.toUInt32 == u32) ++
    (test s!"{n}₆₄ roundtrips" $ z.toUInt64 == u64)

def arrays : List ByteArray := [
  ⟨#[]⟩, ⟨#[1]⟩, ⟨#[0, 3]⟩, ⟨#[1, 1, 1]⟩, ⟨#[3, 3, 3, 3]⟩, ⟨#[13]⟩
]

#lspec arrays.zip arrays |>.foldl (init := .done) fun tSeq (x, y) =>
  tSeq ++ (test s!"{x} = {y}" $ x.beqC y)

#lspec arrays.zip arrays |>.foldl (init := .done) fun tSeq (x, y) =>
  tSeq ++ (test s!"{x} = {y}" $ x.ordC y == .eq)

#lspec arrays.zip arrays.reverse |>.foldl (init := .done) fun tSeq (x, y) =>
  tSeq ++ (test s!"{x} ≠ {y}" $ !x.beqC y)

def arrays' : List ByteArray := [
  ⟨#[1]⟩, ⟨#[2]⟩, ⟨#[0, 3, 0]⟩, ⟨#[1, 2, 1]⟩, ⟨#[3, 3, 4, 3]⟩, ⟨#[13, 0]⟩
]

#lspec arrays.zip arrays' |>.foldl (init := .done) fun tSeq (x, y) =>
  tSeq ++ (test s!"{x} < {y}" $ x.ordC y == .lt)

#lspec arrays'.zip arrays |>.foldl (init := .done) fun tSeq (x, y) =>
  tSeq ++ (test s!"{x} > {y}" $ x.ordC y == .gt)

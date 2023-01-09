import LSpec
import YatimaStdLib.LightData

def data : List LightData := [
  true, false, 0, 1, 255, 256, 300, 300000, "", "aaa", "\\", "\"",
  (none : Option Nat), some 3, some (some 2), ("ars", 3, some #[3]),
  (.left 1 : Either Nat String), (.right #[3] : Either Nat (Array Nat)),
  .arr #[true, false, 0, 1, 255, 256, 300, 300000, "", "aaa", "\\", "\""],
  .arr #[.arr #[false, .arr #[true, 1, "hello", "world"]]],
  .big 2 (.ofNat 3), .big 2 (.ofNat 10), .big 10 (.ofNat UInt64.size.succ)
]

open LSpec

def serde := data.foldl (init := .done) fun tSeq d =>
  let bytes := d.toByteArray
  tSeq ++ withExceptOk s!"{d} deserializes" (LightData.ofByteArray bytes)
    fun d' => test s!"{d} roundtrips" (d == d')

def hashing := data.foldl (init := .done) fun tSeq d =>
  data.foldl (init := tSeq) fun tSeq d' =>
    if d == d' then
      tSeq ++ test s!"{d} and {d'} have the same hash" (d.hash == d'.hash)
    else tSeq ++ test s!"{d} and {d'} have different hashes" (d.hash != d'.hash)

def main := lspecIO $
  serde ++ hashing

import LSpec
import YatimaStdLib.LightData

def data : List LightData := [
  .nil, true, false, 0, 1, 255, 256, 300, 300000, "", "aaa", "\\", "\"",
  .arr #[.nil, true, false, 0, 1, 255, 256, 300, 300000, "", "aaa", "\\", "\""],
  .arr #[.nil, .arr #[.nil, .arr #[.nil, 1, "hello", "world"]]]
]

open LSpec

#lspec data.foldl (init := .done) fun tSeq d =>
  let bytes := d.toByteArray
  tSeq ++ withExceptOk s!"{d} deserializes" (LightData.ofByteArray bytes)
    fun d' => test s!"{d} roundtrips" (d == d')

#lspec data.foldl (init := .done) fun tSeq d =>
  data.foldl (init := tSeq) fun tSeq d' =>
    if d == d' then
      tSeq ++ test s!"{d} and {d'} have the same hash" (d.hash == d'.hash)
    else tSeq ++ test s!"{d} and {d'} have different hashes" (d.hash != d'.hash)

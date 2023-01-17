import LSpec
import YatimaStdLib.ByteArray

open LSpec

def arrays : List ByteArray := [
  ⟨#[]⟩, ⟨#[1]⟩, ⟨#[0, 3]⟩, ⟨#[1, 1, 1]⟩, ⟨#[3, 3, 3, 3]⟩, ⟨#[13]⟩
]

def sliceInputs : List (Nat × Nat) := [
  (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
  (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
  (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6),
  (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6),
  (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6),
  (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6)
]

def arrays' : List ByteArray := [
  ⟨#[1]⟩, ⟨#[2]⟩, ⟨#[0, 3, 0]⟩, ⟨#[1, 2, 1]⟩, ⟨#[3, 3, 4, 3]⟩, ⟨#[13, 0]⟩
]

def beq : TestSeq :=
  arrays.zip arrays |>.foldl (init := .done) fun tSeq (x, y) =>
    tSeq ++ (test s!"{x} = {y}" $ x.beq y && x.beqL y)

def ord : TestSeq :=
  arrays.zip arrays |>.foldl (init := .done) fun tSeq (x, y) =>
    tSeq ++ (test s!"{x} = {y}" $ x.ord y == .eq && x.ordL y == .eq)

def neq : TestSeq :=
  arrays.zip arrays.reverse |>.foldl (init := .done) fun tSeq (x, y) =>
    tSeq ++ (test s!"{x} ≠ {y}" $ !x.beq y && !x.beqL y)

def lt : TestSeq :=
  arrays.zip arrays' |>.foldl (init := .done) fun tSeq (x, y) =>
    tSeq ++ (test s!"{x} < {y}" $ x.ord y == .lt && x.ordL y == .lt)

def gt : TestSeq :=
  arrays'.zip arrays |>.foldl (init := .done) fun tSeq (x, y) =>
    tSeq ++ (test s!"{x} > {y}" $ x.ord y == .gt && x.ordL y == .gt)

def slice : TestSeq :=
  arrays.foldl (init := .done) fun tSeq arr =>
    sliceInputs.foldl (init := tSeq) fun tSeq (i, n) =>
      tSeq ++ test s!"Lean/C match for {arr} sliced {i} {n}"
        (arr.sliceL i n == arr.slice i n)

def main := lspecIO $
  beq ++ ord ++ neq ++ lt ++ gt ++ slice

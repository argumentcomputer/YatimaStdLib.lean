import LSpec
import YatimaStdLib.Nat

open Lean LSpec Nat

def nextPowerOfTwoInOut : List (Nat × Nat) := [
       (5, 8),
       (100, 128),
       (1000, 1024),
       (0, 1),
       (30000, 32768)
]

def nextPowerOfTwoTests : TestSeq := 
  nextPowerOfTwoInOut.foldl (init := .done) 
  (fun tSeq (inp, out) => tSeq ++ (test "nextPowerOfTwo' is correct" (nextPowerOfTwo' inp == out)))


def powModInOut : List ((Nat × Nat × Nat) × Nat) := [
       ((3, 17, 21), 2),
       ((4, 78, 101), 0),
       ((27, 98, 317), 8),
       ((14, 5, 801), 13),
       ((4, 7, 91), 3)
]

def powModTests : TestSeq := 
  powModInOut.foldl (init := .done) 
  (fun tSeq ((mod, base, exp), out) => 
    tSeq ++ (test "powMod is correct" (powMod mod base exp == out)))

def legendreInOut : List ((Nat × Nat) × Nat) := [
       ((31, 5), 1),
       ((87, 9), 0),
       ((4, 3), 1),
       ((73, 103), 102),
       ((7, 19), 1),
       ((3, 113), 112)
]

def legendreTests : TestSeq := legendreInOut.foldl (init := .done) 
  (fun tSeq ((a, p), out) => tSeq ++ (test "legendre is correct" (legendre a p == out)))

def tonelliInOut : List $ (Nat × Nat) × (Option (Nat × Nat)) := [
       ((10, 13), some (7, 6)), 
       ((56, 101), some (37, 64)),
       ((1030, 10009), some (1632, 8377)), 
       ((1032, 10009), none),
       ((44402, 100049), some (30468, 69581)),
       ((665820697, 1000000009) , some (378633312,621366697))
]

def tonelliTests : TestSeq := tonelliInOut.foldl (init := .done) 
  (fun tSeq ((n, p), out) => tSeq ++ (test "tonelli is correct" (tonelli n p == out)))

def main := lspecIO $
  nextPowerOfTwoTests ++ powModTests ++ legendreTests ++ tonelliTests
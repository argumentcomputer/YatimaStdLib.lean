import Batteries.Data.Array.Basic
import YatimaStdLib.List

namespace Array

/-- Generates the array of nats from 0,...,n by a given n -/
def iota (n : Nat) : Array Nat :=
  Array.mk (List.range n) |>.push n

instance : Monad Array where
  map := Array.map
  pure x := #[x]
  bind l f := Array.join $ Array.map f l

def shuffle (ar : Array α) (seed : Option Nat := none) [Inhabited α] :
    IO $ Array α := do
  IO.setRandSeed $ seed.getD (← IO.monoMsNow)
  let mut ar := ar
  let size := ar.size
  for i in [0 : size - 2] do
    let j ← IO.rand i.succ (size - 1)
    let tmp := ar[j]!
    ar := ar.set! j ar[i]! |>.set! i tmp
  return ar

/-- Pads the array `ar` with `a` until it has length `n`-/
def pad (ar : Array α) (a : α) (n : Nat) : Array α :=
  let diff := n - ar.size
  ar ++ (.mkArray diff a)

instance [Ord α] : Ord (Array α) where
  compare x y := compare x.data y.data

def last (ar : Array α) : Array α := ar.toSubarray.popFront.toArray

theorem append_size (arr₁ arr₂ : Array α) (h1 : arr₁.size = n) (h2 : arr₂.size = m)
    : (arr₁ ++ arr₂).size = n + m := by
  unfold Array.size at *
  simp [h1, h2]

def stdSizes (maxSize : Nat) := Array.iota maxSize |>.map (2 ^ ·)

def average (arr : Array Nat) : Nat :=
  let sum := arr.foldl (init := 0) fun acc a => acc + a
  sum / arr.size

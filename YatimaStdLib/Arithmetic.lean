import YatimaStdLib.HashMap
import YatimaStdLib.Int

/--
An implementation of the probabilistic Miller-Rabin primality test. Returns `false` if it can be
verified that `n` is not prime, and returns `true` if `n` is probably prime after `k` loops, which 
may return a false positive with probability `1 / 4^k` assuming the ψRNG `gen` doesn't conspire
against us in some unexpected way
-/
def millerRabinTest (n k : Nat) : Bool :=
  let (s, d) := (n - 1).get2Adicity
  -- let exp : Nat → Nat := Exp.fastExpFunc d -- TODO: Use AddChains once we have an efficient Zmod
  Id.run do
    let mut a := 0
    let mut gen := mkStdGen (n + k) -- Using Lean's built in ψRNG 
    for _ in [:k] do
      (a, gen) := randNat gen 2 (n - 2)
      let mut x := Nat.powMod n a d
      let mut y := x * x % n
      for _ in [:s] do
        y := x * x % n
        if y == 1 && x != 1 && x != n - 1 then
          return false
        x := y
      if y != 1 then
        return false
    return true

open Std in
/-- 
Calculates the discrete logarithm of using the Babystep-Giantstep algorithm, should have `O(√n)`
runtime 
-/
def dLog (base result mod : Nat) : Option Nat := do
  let mut basePowers : HashMap Nat Nat := .empty

  let lim := mod.sqrt + 1
  let mut temp := 1
  for pow in [:lim] do
    basePowers := basePowers.insert temp pow
    temp := temp * base % mod

  let basePow := Nat.powMod mod base lim
  let basePowInv := Int.modInv basePow mod |>.toNat

  let mut target := result

  for quot in [:lim] do
    match basePowers.find? target with
    | some rem => return quot * lim + rem
    | none => target := target * basePowInv % mod

  none

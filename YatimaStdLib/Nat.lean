import Std.Data.Nat.Basic

namespace Nat

def toByteArrayCore : Nat → Nat → ByteArray → ByteArray
  | 0, _, bytes => bytes
  | fuel + 1, n, bytes =>
    let b: UInt8 := UInt8.ofNat (n % 256)
    let n' := n / 256
    if n' = 0 then (bytes.push b)
    else toByteArrayCore fuel n' (bytes.push b)

/-- Convert Nat to Little-Endian ByteArray -/
def toByteArrayLE (n : Nat) : ByteArray :=
  toByteArrayCore (n + 1) n default

/-- Convert Nat to Big-Endian ByteArray -/
def toByteArrayBE (n : Nat) : ByteArray :=
  ⟨toByteArrayCore (n + 1) n default |>.data.reverse⟩

def toByteListCore : Nat → Nat → List UInt8 → List UInt8
  | 0, _, bytes => bytes
  | fuel + 1, n, bytes =>
    let b: UInt8 := UInt8.ofNat (n % 256)
    let n' := n / 256
    if n' = 0 then (bytes.cons b)
    else toByteListCore fuel n' (bytes.cons b)

/-- Convert Nat to Big-Endian byte list -/
def toByteListBE (n : Nat) : List UInt8 :=
  toByteListCore (n + 1) n []

def byteLength (n : Nat) : Nat :=
  n.toByteArrayLE.size

def fromByteListCore: Nat → List UInt8 → Nat → Nat
  | 0,        _,       n => n
  | _ + 1,    [],      n => n
  | fuel + 1, b :: bs, n =>
    fromByteListCore fuel bs (n.shiftLeft 8 + b.toNat)

/-- Read Nat from Big-Endian byte list -/
def fromByteListBE (b : List UInt8) : Nat :=
  fromByteListCore (b.length + 1) b 0

def sigBitsCore: Nat → Nat → Nat → Nat
  | 0,     acc, _ => acc
  | _ + 1, acc, 0 => acc
  | f + 1, acc, n => sigBitsCore f (acc + 1) (n.shiftRight 1)

/-- Significant Bits in a Nat -/
def sigBits (x : Nat) : Nat :=
  sigBitsCore x 0 x

/-- Faster in-kernel log2 -/
def log2' (x : Nat) : Nat :=
  sigBits x - 1

/--
Given a natural number n, `nextPowerOfTwo'` returns the smallest power of two
which is less than or equal to `2^n`.

This version uses the low-level implementation of `Nat.log2` and is meant to be
faster than the original `Nat.nextPowerOfTwo`
-/
def nextPowerOfTwo' (n : Nat) : Nat :=
  if n == 0 then 1 else
  1 <<< (n.log2 + 1)

section GCD

/-! From mathlib -/

/-- Helper function for the extended GCD algorithm (`nat.xgcd`). -/
partial def xgcdAux : Nat → Int → Int → Nat → Int → Int → Nat × Int × Int
  | 0, _, _, r', s', t' => (r', s', t')
  | r, s, t, r', s', t' =>
    let q := r' / r
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t

/--
Use the extended GCD algorithm to generate the `a` and `b` values
satisfying `gcd x y = x * a + y * b`.
-/
def xgcd (x y : Nat) : Int × Int := (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : Nat) : Int := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : Nat) : Int := (xgcd x y).2

end GCD

theorem div2_lt (h : n ≠ 0) : n / 2 < n := by
  match n with
  | 1   => decide
  | 2   => decide
  | 3   => decide
  | n+4 =>
    rw [div_eq, if_pos]
    refine succ_lt_succ (Nat.lt_trans ?_ (lt_succ_self _))
    exact @div2_lt (n + 2) (by simp_arith)
    simp_arith

/--
Evaluates `b^e mod m`
-/
def powMod (m b e : Nat) : Nat :=
  let rec go (b e r : Nat) : Nat :=
    if h : e = 0 then r
    else
      let e' := e / 2
      have : e' < e := 
      by exact Nat.div2_lt h
      if e % 2 = 0
      then go ((b*b) % m) e' r              -- TODO : Use Montgomery multiplication here to avoid
      else go ((b*b) % m) e' ((r*b) % m)    --        calculating `mod` at every step
  go b e 1

/-- A legendre symbol denotes the value of `a^((p - 1)/2) mod p`
-/
def legendre (a : Nat) (p : Nat) : Nat :=  -- TODO : Use a pre-calculated `(p - 1) / 2 ` AddChain
  powMod p a ((p - 1) / 2)                 --        and AddChain `fastExp` here

/--
The Tonelli-Shanks algorithm solves the equation having the form
`x^2 = n mod p`, whenever it exists
-/
def tonelli (n : Nat) (p : Nat) : Option (Nat × Nat) :=
  if legendre n p != 1 then none else Id.run do
  let mut q := p - 1
  let mut s := 0
  while q % 2 == 0 do
    q := q / 2
    s := s + 1
  if s == 1 then
    let r := powMod p n ((p + 1) / 4)
    return some (r, p - r)
  let mut zMax := 2
  for z in [2 : p] do
    zMax := z
    if p - 1 == legendre z p then break
  let mut c := powMod p zMax q
  let mut r := powMod p n $ (q + 1) / 2  -- TODO : Group together these two exponetiations into a 
  let mut t := powMod p n q              --        bached Exp to avoid re-calculating some powers
  let mut m := s
  while (t - 1) % p != 0 do
    let mut t2 := (t * t) % p
    let mut iMax := 1
    for i in [1:m] do
      iMax := i
      if (t2 - 1) % p == 0 then
        break
      t2 := (t2 * t2) % p
    let b := powMod p c (2^(m - iMax - 1))
    r := (r * b) % p
    c := (b * b) % p
    t := (t * c) % p
    m := iMax
  return some (r, p - r)

/-- Prints a `Nat` in its hexadecimal form, given the wanted length -/
def asHex (n : Nat) (length : Nat) : String := 
  if n < USize.size then 
    toString n 
  else 
    let tail := Nat.toDigits 16 n
    let pad := List.replicate (length - tail.length) '0'
    "0x" ++  List.asString (pad ++ tail)

def subDigitChar (n : Nat) : Char :=
  if n = 0 then '₀' else
  if n = 1 then '₁' else
  if n = 2 then '₂' else
  if n = 3 then '₃' else
  if n = 4 then '₄' else
  if n = 5 then '₅' else
  if n = 6 then '₆' else
  if n = 7 then '₇' else
  if n = 8 then '₈' else
  if n = 9 then '₉' else
  '*'

partial def toSubDigitsAux : Nat → List Char → List Char
  | n, ds =>
    let d  := subDigitChar <| n % 10;
    let n' := n / 10;
    if n' = 0 then d::ds
    else toSubDigitsAux n' (d::ds)

def toSubDigits (n : Nat) : List Char :=
  toSubDigitsAux n []

def toSubscriptString (n : Nat) : String :=
  (toSubDigits n).asString

end Nat

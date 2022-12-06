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

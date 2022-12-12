import YatimaStdLib.Nat
import YatimaStdLib.Array

inductive Endian where
  | big    : Endian
  | little : Endian
  deriving Repr, DecidableEq, Inhabited

inductive Bit where
  | zero
  | one
  deriving DecidableEq, Inhabited

instance : ToString Bit where
  toString
    | .one  => "1"
    | .zero => "0"

instance : OfNat Bit (nat_lit 0) where
  ofNat := .zero

instance : OfNat Bit (nat_lit 1) where
  ofNat := .one

section bit_methods

namespace Bit

def xOr : Bit → Bit → Bit
  | one, zero
  | zero, one => one
  | _, _      => zero

def toNat : Bit → Nat
  | zero => 0
  | one  => 1

instance : Coe Bit Nat := ⟨toNat⟩

def toUInt8 : Bit → UInt8 :=
  Nat.toUInt8 ∘ Bit.toNat

end Bit

end bit_methods

namespace Bit

def arrayXOr (bs : Array Bit) : Bit :=
  bs.foldl (fun b b' => b.xOr b') zero

def arrayToNat (bs : Array Bit) : Nat :=
  bs.foldl (fun b b' => b * 2 + b'.toNat) 0

def listPad (n : Nat) (bs : List Bit) : List Bit :=
  let l := bs.length
  if l >= n then bs else List.replicate (n - l) zero ++ bs

-- Interprets a `List Bit` as a `Nat`, taking `Endian`ness into consideration.
def bitsToNat (l: List Bit) (en : Endian := default) : Nat :=
  let rec go
    | [], acc => acc
    | b :: bs, acc => go bs $ acc * 2 + (if b = zero then 0 else 1)
  let bits := if en = .big then l else List.reverse l
  go bits default

-- Takes first `n` elems of the `List Bit` and interprets them as a `Nat`.
-- Returns `none` if the list is shorter than `n`.
def someBitsToNat? (n : Nat) (l: List Bit) (en : Endian := default) : Option Nat :=
  if n > l.length || n = 0 then .none else .some $ bitsToNat (l.take n) en

end Bit

def Nat.toBits : Nat → List Bit
  | 0 => [.zero]
  | 1 => [.one]
  | n + 2 =>
    have h₁ : n + 2 ≠ 0 := by simp_arith
    Nat.toBits ((n + 2) / 2) ++ (if n % 2 = 0 then [.zero] else [.one])
  decreasing_by exact Nat.div2_lt h₁;

def UInt8.toBits (u : UInt8) : List Bit :=
  Bit.listPad 8 $ Nat.toBits $ UInt8.toNat u

def ByteArray.toBits (ba : ByteArray) : List Bit :=
  List.join $ List.map UInt8.toBits $ ByteArray.toList ba

/-- Generates the array of binary expansions between `0` and `2^n` -/
def getBits (n : Nat) : Array (Array Bit) := Id.run do
  let mut answer := #[(.mkArray n 0)]
  for x in [1:2^n] do
    let xBits := x |> (Nat.toDigits 2 ·) 
                   |>.map (fun c => c.toNat - 48)
                   |>.map (fun n => if n == 0 then .zero else .one)
                   |>.reverse
                   |>.toArray
                   |>.pad 0 n
    answer := answer.push xBits
  return answer

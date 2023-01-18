import YatimaStdLib.ByteArray
import Std.Data.Nat.Lemmas

structure ByteVector (n : Nat) where
  data  : ByteArray
  valid : data.size = n
  deriving Ord

namespace ByteVector

instance : Inhabited (ByteVector n) where
  default := ⟨.mk $ .mkArray n 0, by simp [ByteArray.size]⟩

instance : BEq (ByteVector n) where
  beq x y := x.data == y.data

def toString (vec : ByteVector n) : String :=
  let str := s!"⟨{", ".intercalate (vec.data.data.data.map ToString.toString)}⟩"
  s!"{n.toSubscriptString}{str}"

instance : ToString (ByteVector n) := ⟨toString⟩

def ofByteArray (bytes : ByteArray) : ByteVector bytes.size :=
  ⟨bytes, rfl⟩

def get (vec : ByteVector n) (i : Nat) (h : i < n) : UInt8 :=
  vec.data.get ⟨i, by simp only [vec.valid, h]⟩

def get' (vec : ByteVector n) (i : Fin n) : UInt8 :=
  vec.data.get ⟨i, by simp only [vec.valid, i.isLt]⟩

def get! (vec : ByteVector n) (i : Nat) : UInt8 :=
  vec.data.get! i

def set (vec : ByteVector n) (i : Nat) (h : i < n) (u : UInt8) : ByteVector n :=
  let data := vec.data.set ⟨i, by simp only [vec.valid, h]⟩ u
  ⟨data, by rw [ByteArray.set_size, vec.valid]⟩

def set' (vec : ByteVector n) (i : Fin n) (u : UInt8) : ByteVector n :=
  let data := vec.data.set ⟨i, by simp only [vec.valid, i.isLt]⟩ u
  ⟨data, by rw [ByteArray.set_size, vec.valid]⟩

def set! (vec : ByteVector n) (i : Nat) (u : UInt8) : ByteVector n :=
  let data := vec.data.set! i u
  ⟨data, by rw [ByteArray.set!_size, vec.valid]⟩

def genWith (f : Fin n → UInt8) : ByteVector n := Id.run do
  let mut res := default
  for h : i in [0 : n] do
    have := Membership.mem.upper h
    res := res.set i this (f $ Fin.mk i this)
  return res  

def ofNat (n capacity : Nat) : ByteVector capacity :=
  ⟨n.toByteArrayLE.slice 0 capacity, ByteArray.slice_size⟩

@[extern "lean_byte_vector_to_uint16"]
opaque toUInt16 : @& ByteVector 2 → UInt16

@[extern "lean_byte_vector_to_uint32"]
opaque toUInt32 : @& ByteVector 4 → UInt32

@[extern "lean_byte_vector_to_uint64"]
opaque toUInt64 : @& ByteVector 8 → UInt64

def map (v : ByteVector n) (f : UInt8 → UInt8) : ByteVector n := Id.run do
  let mut res := default
  for h : i in [0 : n] do
    have := Membership.mem.upper h
    res := res.set i this (f $ v.get i this)
  pure res

def zipWith (x y : ByteVector n) (f : UInt8 → UInt8 → UInt8) : ByteVector n := Id.run do
  let mut res := default
  for h : i in [0 : n] do
    have := Membership.mem.upper h
    res := res.set i this (f (x.get i this) (y.get i this))
  pure res

def shiftRight1 (x : ByteVector n) : ByteVector n := 
  ⟨x.data.slice 1 n, ByteArray.slice_size⟩

def shiftRight (x : ByteVector n) : Nat → ByteVector n
  | 0     => x
  | m + 1 => shiftRight (shiftRight1 x) m

-- Boolean and arithmetic operations

def lor (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  x.zipWith y UInt8.lor

def and (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  x.zipWith y UInt8.land

def xor (x : ByteVector n) (y : ByteVector n) : ByteVector n :=
  x.zipWith y UInt8.xor

def not (x : ByteVector n) : ByteVector n :=
  x.map (255 - ·)

def add (x y : ByteVector n) : ByteVector n := Id.run do
  let mut res := default
  let mut cin := 0
  for h : i in [0 : n] do
    have := Membership.mem.upper h
    let (r, o) := UInt8.sum3 cin (x.get i this) (y.get i this)
    res := res.set i this r
    cin := o
  return res

instance : Add (ByteVector n) where
  add := add

-- TODO: is it correct?
instance : Sub (ByteVector n) where
  sub x y := x + ByteVector.not y

private def uInt8OverFlowMul (u₁ u₂ : UInt8) : UInt8 × UInt8 := 
  let u16 := u₁.toUInt16 * u₂.toUInt16
  (u16 >>> 8 |>.toUInt8, u16.toUInt8)

private def uInt8OverFlowAdd (u₁ u₂ : UInt8) : UInt8 × UInt8 :=
  let u16 := u₁.toUInt16 + u₂.toUInt16
  (u16 >>> 8 |>.toUInt8, u16.toUInt8)

private def uInt8Mul (x : ByteVector n) (u : UInt8) : ByteVector n := Id.run do
  let mut carry: UInt8 := 0
  let mut answer: ByteVector n := default

  for idx in [: n] do
    let (carry1, res') := uInt8OverFlowMul (x.get! idx) u
    let (carry2, res) := uInt8OverFlowAdd carry res'
    answer := answer.set! idx res
    carry := carry1 + carry2

  return answer

instance : HMul (ByteVector n) UInt8 (ByteVector n) where
  hMul := uInt8Mul

private def naiiveMul (x y : ByteVector n) : ByteVector n := Id.run do
  let mut answer: ByteVector n := default

  for (idx, u) in x.data.data.toList.enum do
    let temp := y * u
    answer := answer + (shiftRight temp idx)
  
  answer

def split (x : ByteVector n) (size₁ size₂ : Nat) : ByteVector size₁ × ByteVector size₂ :=
  let left := x.data.slice 0 size₁
  let right := x.data.slice size₁ size₂
  (⟨left, ByteArray.slice_size⟩, ⟨right, ByteArray.slice_size⟩)

open Array in
def append (x : ByteVector n) (y : ByteVector m) : ByteVector (n + m) := 
  let ⟨xData, xSize⟩ := x
  let ⟨yData, ySize⟩ := y
  ⟨⟨xData.data ++ yData.data⟩, append_size xData.data yData.data xSize ySize⟩

def karatsubaMulAux (x y : ByteVector n) (carry : UInt8) :  UInt8 × ByteVector n := 
  match h : n with
  | 0 => (0, ⟨.mk #[], rfl⟩)
  | 1 =>
    have : 0 < x.data.data.size := by -- TODO : Refactor this so the proof isn't copied twice
      cases x
      rename_i data2 valid
      cases data2
      unfold ByteArray.size at *
      dsimp at valid
      simp [valid] 
    have : 0 < y.data.data.size := by
      cases y
      rename_i data2 valid
      cases data2
      unfold ByteArray.size at valid
      dsimp at valid
      simp [valid] 
    let xData := x.data.data[0]
    let yData := y.data.data[0]
    let (carry', res) := uInt8OverFlowMul xData yData
    (carry', .ofNat (res + carry).toNat 1)
  | r@((_ + 1) + 1) =>
    let low := r / 2
    let high := r - low

    have low_lt_r : low < r := by
      rename_i n' h'
      apply Nat.div2_lt
      rw [h']
      apply Nat.succ_ne_zero

    have high_lt_r : high < r := by
      apply Nat.sub_lt
      · rename_i n' h'
        rw [h']
        apply Nat.zero_lt_succ
      · have : 2 ≤ r := by
          rename_i n' h'
          rw [h']
          simp_arith
        have : 1 ≤ low := by
          rw [Nat.le_div_iff_mul_le]
          simp_arith
          exact this
          decide
        simp_arith
        exact this

    have add_low_high : low + high = r := by
      apply Nat.add_sub_of_le
      apply Nat.le_of_lt low_lt_r

    let (tailX, headX) := x.split low high
    let (tailY, headY) := y.split low high

    let (carry0, z0) := karatsubaMulAux tailX tailY 0
    let (carry1, z1) : UInt8 × ByteVector 0 := sorry -- karatsubaMulAux (tailX + headX) (tailY + headY) 0
    let (carry2, z2) := karatsubaMulAux headX headY 0

    sorry

def karatsubaMul (x y : ByteVector n) : ByteVector n := karatsubaMulAux x y 0 |>.snd

instance : Mul (ByteVector n) where
  mul := naiiveMul

end ByteVector

@[extern "lean_byte_array_blake3"]
opaque ByteArray.blake3 : @& ByteArray → ByteVector 32

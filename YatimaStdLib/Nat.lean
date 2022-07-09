namespace Nat

def toByteArrayCore : Nat → Nat → ByteArray → ByteArray
  | 0, _, bytes => bytes
  | fuel + 1, n, bytes =>
    let b: UInt8 := UInt8.ofNat (n % 256);
    let n' := n / 256;
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
    let n' := n / 256;
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
    fromByteListCore fuel bs (n.shiftLeft 8 + (UInt8.toNat b))

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

end Nat

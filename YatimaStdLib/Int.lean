import Std.Data.Int.Basic
import YatimaStdLib.Nat

namespace Int

def quotRem (a : Nat) (b : Nat) : Nat × Nat :=
  (a / b, a % b)

/-- 
Return `(x, y, g)` where `g` is the greatest common divisor of `a` and `b`, and `x`, `y` satisfy

`x * a + y * b = g`
-/
def gcdExtNat (a : Nat) (b : Nat) : Int × Int × Int :=
  match h : b with
    | 0 => (1, 0, a)
    | k + 1 =>
      let p := quotRem a b
      let q := p.1
      let r := p.2
      have : r < k.succ := by
        have h2 := k.succ_ne_zero
        rw [← h] at *
        apply Nat.mod_lt
        exact Nat.zero_lt_of_ne_zero h2
      let (s, t, g) := gcdExtNat b r
      (t, s - q * t, g)
  termination_by _ => b

def gcdExt (a : Int) (b : Int) : Int × Int × Int := 
  gcdExtNat (Int.natAbs a) (Int.natAbs b)

def modInv (a : Int) (m : Int) : Int :=
  let (i, _, g) := Int.gcdExt a m
  let mkPos (x : Int) := if x < 0 then x + m else x
  if g == 1 then mkPos i else 0

def modToNat : Int → Nat → Nat
  | .ofNat x,   n => x % n
  | .negSucc x, n => n - x % n - 1

def isEven (x : Int) : Bool :=
  if x / 2 == 0 then true else false

def powMod (m b e : Int) : Int :=
  let rec go (b e r : Int) : Int :=
    match e with
      | 0 => r
      | y =>
        if h : y % 2 = 0
        then go ((b*b) % m) (y % 2) r
        else go ((b*b) % m) (y / 2) ((r*b) % m)
  go b e 1

def legendre (a : Int) (p : Int) : Int :=
  powMod p a ((p - 1) / 2)

def foo (t : Nat) (m : Nat) (p : Nat) : Nat := Id.run do
  let mut t2 := (t * t) % p
  while t - 1 % p != 0 do
    t2 := (t * t) % p
    for i in [1:m] do
      if (t2 - 1) % p == 0
      then break
      else t2 := (t2 * t2) % p
  return t

def tonelli (n : Int) (p : Int) : Option (Int × Int) :=
  match legendre n p == 1 with
    | false => none
    | true =>
      let s := Nat.divCount (Int.natAbs $ p - 1)
      let q := ofNat $ Nat.shiftLeft (Int.toNat (p - 1)) s
      if s == 1
      then
        let r := powMod p n ((p+1) / 4)
        some (r, p - r)
      else
        let l :=
          List.map ofNat $
            List.map Nat.succ $
            List.reverse $
            List.iota $ natAbs $ p - 2
        let z :=
          2 + (List.length $ List.takeWhile (fun i => not (p - 1 == legendre i p)) l)
        let rec loop (m c r t : Int) : Option (Int × Int) :=
          match (t - 1) % p == 0 with
            | true => some (r, p - r)
            | false => 
            let iter (t : Nat) (m : Nat) (p : Nat) : Nat := Id.run do
              let mut t := t
              while (t - 1) % p != 0 do
                let mut t2 := (t * t) % p
                for i in [1:m] do
                if (t2 - 1) % p == 0 then break
                else t2 := (t2 * t2) % p
              return t
            let i := iter (Int.toNat t) (Int.toNat m) (Int.toNat p)
            let deg := ofNat (2^((Int.toNat m) - i - 1))
            let b := powMod p c deg
            let r' := (r*b) % p
            let c' := (b*b) % p
            let t' := (t*c') % p
            loop i c' r' t'
        loop s
            (powMod p z q)
            (powMod p n $ (q+1) / 2)
            (powMod p n q)

theorem modToNat_ofNat : modToNat (ofNat a) n = a % n := rfl
theorem modToNat_negSucc : modToNat (negSucc a) n = n - a % n - 1 := rfl

theorem modToNat_le {n : Nat} : modToNat a n.succ < n.succ := by 
  cases a with 
  | ofNat x => simp only [modToNat_ofNat, x.mod_lt (n.succ_pos)]
  | negSucc x =>
    let y := x % n.succ
    have : n.succ - y - 1 ≤ n := by
      have : n.succ - y - 1 = n - y := n.add_sub_add_right 1 y
      rw [this]
      exact n.sub_le y
    exact Nat.lt_succ_of_le this

end Int

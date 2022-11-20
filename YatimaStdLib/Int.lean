import Std.Data.Int.Basic

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

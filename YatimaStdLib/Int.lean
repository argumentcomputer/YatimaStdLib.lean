namespace Int

def quotRem (a : Nat) (b : Nat) : Nat × Nat :=
  (a / b, Nat.mod a b)

def gcdExtNat (a : Nat) (b : Nat) : Int × Int × Int :=
  match h : b with
    | 0 => (1, 0, a)
    | k + 1 =>
      let p := quotRem a b
      let q := p.1
      let r := p.2
      have : r < Nat.succ k := by
        have h2 := Nat.succ_ne_zero k
        rw [←h] at *
        apply Nat.mod_lt
        exact Nat.zero_lt_of_ne_zero h2
      let (s, t, g) := gcdExtNat b r
      (t, s - q * t, g)
  termination_by _ => b

def Int.gcdExt (a : Int) (b : Int) : Int × Int × Int := 
  gcdExtNat (Int.natAbs a) (Int.natAbs b)

def Int.modInv (a : Int) (m : Int) : Option Int :=
  let (i, _, g) := Int.gcdExt a m
  let mkPos (x : Int) := if x < 0 then x + m else x
  if g == 1 then Option.some (mkPos i) else .none

end Int

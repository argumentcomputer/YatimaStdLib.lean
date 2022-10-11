namespace Polynomial

def Polynomial R := Array R

instance : Append (Polynomial A) where
  append := Array.append

def tail (ar : Polynomial A) : Polynomial A :=
  match ar.data with
    | [] => Array.empty
    | (_ :: xs) => Array.mk xs

variable {A : Type} [Add A] [Mul A] [HPow A Nat A] [OfNat A 1] [ofnat : OfNat A 0] 
                    [hab : Inhabited A] [eq : BEq A] [Div A] [Neg A]

def dropWhile (p : A → Bool) (f : Polynomial A) : Polynomial A :=
  match f with
    | { data := xs } => Array.mk $ List.dropWhile p xs

def norm (f : Polynomial A) : Polynomial A :=
  dropWhile (fun (x : A) => x == 0) f

def degree (f : Polynomial A) : Nat :=
  Array.size (norm f) - 1

def isZero (f : Polynomial A) : Bool :=
  if f.size == 1 && Array.getD f 0 0 == 0 then true else false

def isMonic (f : Polynomial A) : Bool :=
  let f' := norm f
  if Array.getD f' 0 0 == 1 then true else false

def lead (f : Polynomial A) : A := Array.getD f 0 0

def mulByConst (a : A) (f : Polynomial A) : Polynomial A :=
  Array.map (fun x => x * a) f

instance : HMul A (Polynomial A) (Polynomial A) where
  hMul := mulByConst

def eval (f : Polynomial A) (a : A) : A :=
  let action (i : Fin f.size) _ :=
    match (i : Nat) with
      | 0 => (Array.getD f 0 0) * a ^ (degree f)
      | (Nat.succ _) => (Array.getD f i 0) * a ^ (degree f - i : Nat)
  Array.foldr (. + .) 0 (Array.mapIdx f action)

def zeros (n : Nat) : Polynomial A := mkArray n 0

def zero : Polynomial A := #[0]

def shift (f : Polynomial A) (n : Nat) : Polynomial A :=
  f ++ zeros n

def polyAdd (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  let action (f₁ : Polynomial A) (f₂ : Polynomial A) := Array.map (fun (x, y) => x + y) (Array.zip f₁ f₂)
  if f.size < g.size
  then
    action (shift f (g.size - f.size)) g
  else
    if f.size > g.size
    then action f (shift g (f.size - g.size))
    else action f g

instance : Add (Polynomial A) where
  add := polyAdd

def polySub (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  polyAdd f (Array.map Neg.neg g)

def polyMul (f : Polynomial A) : Polynomial A → Polynomial A :=
  Array.foldr (fun x acc => polyAdd (mulByConst x f) (zero ++ acc)) (#[] : Polynomial A)

instance : Mul (Polynomial A) where
  mul := polyMul

instance : Sub (Polynomial A) where
  sub := polySub

def polyDiv (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  let rec polDiv' f' g' (n : Nat) :=
    match n with
      | 0 => Array.empty
      | k + 1 =>
        if k + 1 < g'.size then Array.empty
        else
          let x := Array.getD f' 0 0
          let y := Array.getD g' 0 0
          let z := x / y
          #[z] ++ polDiv' (tail (polySub f' (polyMul #[z] g'))) g' k 
  Array.reverse $ polDiv' (Array.reverse f) (Array.reverse g) (f.size)

def polyMod (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
    let rec polyMod' f' g' (n : Nat) :=
    match n with
      | 0 => Array.empty
      | k + 1 =>
        if k + 1 < g'.size then f'
        else
          let x := Array.getD f' 0 0
          let y := Array.getD g' 0 0
          let z := x / y
          polyMod' (tail (polySub f' (polyMul #[z] g'))) g' k 
  Array.reverse $ polyMod' (Array.reverse f) (Array.reverse g) (f.size)

def rootsToPoly (a : List A) : Polynomial A :=
  match a with
    | [] => #[1]
    | (root :: roots) => 
      let monom : Polynomial A := #[root,-1]
      monom * (rootsToPoly roots)

instance [OfNat A 1] : OfNat (Polynomial A) 1 where
  ofNat := #[1]

instance [OfNat A 0] : OfNat (Polynomial A) 0 where
  ofNat := zero

end Polynomial
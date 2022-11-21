/-!
# Polynomials

In this module we define univariate polynomials over a type `R`, together with basic functions
defining their evaluation, arithmetic, and divisibility.
-/

/-- 
The type of a polynomial with coefficients in `R`. 

NOTE : We encode polynomials in such a way so that the `i`th entry of the array corresponds to the
degree `i-1` coefficient. For example `#[a,b,c]` <--> `a + b x + c x^2`
-/
def Polynomial R := Array R

namespace Polynomial

def ofArray : Array R → Polynomial R := id

def toArray : Polynomial R → Array R := id

/-- A useful coercion to write polynomial literals in terms of elements of type `R` -/
instance : Coe (Array R) (Polynomial R) where
  coe := id

instance [Inhabited R] : Inhabited (Polynomial R) where
  default := #[default]

instance : Append (Polynomial A) where
  append := .append

private def tail (ar : Polynomial A) : Polynomial A := ar.eraseIdx 0

variable {A : Type _ } [Add A] [Mul A] [HPow A Nat A] [OfNat A (nat_lit 1)] [OfNat A (nat_lit 0)] 
                       [BEq A] [Div A] [Neg A]

/-- Returns a "normalized" form for a polynomial, dropping the leading zeroes -/
def norm (f : Polynomial A) : Polynomial A := 
  let ans := f.popWhile (· == 0)
  if ans.size == 0 then #[0] else ans

instance : BEq $ Polynomial A where
  beq a b := a.norm.toArray == b.norm.toArray

/-- Returns the degree of a polynomial -/
def degree (f : Polynomial A) : Nat :=
  Array.size (norm f) - 1

/-- Tests whether a polynomial is zero -/
def isZero (f : Polynomial A) : Bool := f.norm.size == 1 && f.getD 0 0 == 0

/-- Returns the constant term of a polynomial -/
def constant (f : Polynomial A) : A := if f.isZero then 0 else f.getD 0 0

/-- Returns the leading coefficient of a polynomial -/
def lead (f : Polynomial A) : A := f.getD f.degree 0

/-- Tests whether a polynomial is monic-/
def isMonic (f : Polynomial A) : Bool := f.lead == 1

/-- Scales a polynomial by an element of the base type -/
def mulByConst (a : A) (f : Polynomial A) : Polynomial A := f.map (· * a)

instance : HMul A (Polynomial A) (Polynomial A) where
  hMul := mulByConst

def makeMonic (f : Polynomial A) : Polynomial A := (1 / f.lead) * f

/-- Evaluates a polynomial at a particular value `a : A` -/
def eval (f : Polynomial A) (a : A) : A :=
  let f := f.norm
  let action (i : Fin f.size) c := c * a ^ (i : Nat)
  Array.foldr (. + .) 0 (f.mapIdx action)

private def zeros (n : Nat) : Polynomial A := mkArray n 0

/-- The zero polynomial -/
def zero : Polynomial A := #[0]

private def padZeroes (f : Polynomial A) (n : Nat) : Polynomial A :=
  f ++ zeros n 

/-- Returns the addition addition of two polynomials -/
def polyAdd (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  let (f, g) := (f.norm, g.norm)
  let action (f₁ : Polynomial A) (f₂ : Polynomial A) := f₁.zip f₂ |>.map (fun (x, y) => x + y)
  if f.size < g.size
  then
    action (padZeroes f (g.size - f.size)) g
  else
    if f.size > g.size
    then action f (padZeroes g (f.size - g.size))
    else action f g

instance : Add (Polynomial A) where
  add := polyAdd

instance : Neg (Polynomial A) where
  neg := Array.map Neg.neg

/-- Returns the subtraction of two polynomials -/
def polySub (f : Polynomial A) (g : Polynomial A) : Polynomial A := f + (-g)

instance : Sub (Polynomial A) where
  sub := polySub

/-- Returns the multiplication of two polynomials -/
def polyMul (f : Polynomial A) : Polynomial A → Polynomial A :=
  Array.foldr (fun x (acc : Polynomial A) => (x * f) + (zero ++ acc)) (#[] : Polynomial A)

instance : Mul (Polynomial A) where
  mul := polyMul

/-- 
Returns `(q, r)` where `q` is the quotient of division of polynomial `f` by `g` and `r` is the
remainder
-/
def polyQuotRem (f : Polynomial A) (g : Polynomial A) : Polynomial A × Polynomial A :=
  let rec polyQRAux (f' g' : Polynomial A) (n : Nat) : Polynomial A × Polynomial A :=
    match n with
    | 0     => (#[], #[])
    | k + 1 => 
      if k + 1 < g'.size then (#[],f')
      else
        let x := f'.getD 0 0
        let y := g'.getD 0 0
        let z := x / y
        let (q', r') := polyQRAux (tail $ f' - g' * (ofArray #[z])) g' k
        (#[z] ++ q'.toArray, r')
  if g == #[0] then (#[0], f) else
  let (f, g) := (f.norm, g.norm)
  let (q, r) := polyQRAux (f.reverse) (g.reverse) (f.size)
  (q.reverse, r.reverse)

/-- Returns the quotient of the division of the polynomial `f` by `g` -/
def polyDiv (f g : Polynomial A) : Polynomial A := polyQuotRem f g |>.fst

/-- Returns the remainder of the division of the polynomial `f` by `g` -/
def polyMod (f g : Polynomial A) : Polynomial A := polyQuotRem f g |>.snd

/-- 
Returns `(a, b, d)` where `d` is the greatest common divisor of `f` and `g` and `a`, `b` satisfy

`a * f + b * g = d `

TODO : Eliminate `partial` using `termination_by _ => g.degree` and a proof that `polyQuotRem`
reduces degree.
-/
partial def polyEuc [ToString A] [Inhabited A] [Div A] (f g : Polynomial A) : Polynomial A × Polynomial A × Polynomial A 
  := if g.isZero then 
       (#[1 / f.lead], #[0], f.makeMonic) else
       let (q, r) := polyQuotRem f g
       let (s, t, d) := polyEuc g r
       (t, s - q * t, d)

/-- 
Returns the monic polynomial with the roots taken from the list `a`.
-/
def rootsToPoly (as : List A) : Polynomial A :=
  match as with
  | [] => #[1]
  | (root :: roots) => 
    let monom : Polynomial A := #[-root,1]
    monom * (rootsToPoly roots)

instance : OfNat (Polynomial A) (nat_lit 1) where
  ofNat := #[1]

instance : OfNat (Polynomial A) (nat_lit 0) where
  ofNat := zero

end Polynomial

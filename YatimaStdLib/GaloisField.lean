import YatimaStdLib.Polynomial
import YatimaStdLib.Zmod

/-!
# Galois Fields

This module provides the basic data structures necessary to define and work with prime fields
and their extensions.

Here we post some definitions from https://hackage.haskell.org/package/galois-field-1.0.2

TODO : 
* Add a normalize function for elements in an extension field
* Add a function to calculate Legendre symbol
* Add more documentation
-/

/-- The structure of a Galois field on t-/
class GaloisField (K : Type _) where
  plus : K → K → K
  times : K → K → K
  null : K
  ein : K
  minus : K → K → K
  divis : K → K → K
  -- Characteristic `p` of field and order of prime subfield.
  char : Nat
  -- Degree `q` of field as extension field over prime subfield.
  deg : Nat
  -- Frobenius endomorphism `x ↦ x^p` of prime subfield.
  frob : K → K

namespace GaloisField

instance [GaloisField K] : Inhabited K where
  default := null

instance [GaloisField K] : Add K where
  add := plus

instance [GaloisField K] : Mul K where
  mul := times

instance [GaloisField K] : OfNat K (nat_lit 1) where
  ofNat := ein

instance [GaloisField K] : OfNat K (nat_lit 0) where
  ofNat := null

instance [GaloisField K] : Div K where
  div := divis

instance [GaloisField K] : Sub K where
  sub := minus

def galPow [GaloisField K] : K → Nat → K
  | _, 0 => 1
  | x, (k + 1) => x * (galPow x k)

instance [GaloisField K] : HPow K Nat K where
  hPow := galPow

instance [GaloisField K] : Neg K where
  neg x := 0 - x

/-- Order p^q of field.-/
def order [GaloisField K] : Nat := (char K)^(deg K)

instance : GaloisField (Zmod p) where
  plus := (. + .)
  times := (. * .)
  null := 0
  ein := 1
  minus := (. - .)
  divis := (. / .)
  char := p
  deg := 1
  frob r := r ^ p

/-- The class of a prime subfield of a GaloisField -/
class PrimeField (K : Type _) [GaloisField K] where
  fromP : K → Int

instance : PrimeField (Zmod p) where
  fromP := id

open Polynomial

/-- 
Pre-computed evaluations of the Frobenius for a Galois field for small degree (2 and 3) extensions.

`frobenius Q P` evaluates the Frobenius of `Q` in the extension of `K` defined by `P`. 

-/
def frobenius [GaloisField K] [BEq K] :
  Polynomial K → Polynomial K → Option (Polynomial K)
  | #[], _ => .some #[]
  | #[a],_ => .some #[frob a]
  | #[a,b], #[x,y,z] =>
    if y == 0 && z == 1 then
      if (deg K) == 2 then .some #[a, -b] else
      if (char K) == 2 then .some #[frob a - frob b * x]
      else
        let nxq : K := (-x) ^ (char K >>> 1)
        .some #[frob a, frob b * nxq]
      else .none
  | #[a,b], #[x,y₁,y₂,z] =>
    if y₁ == 0 && y₂ == 0 && z == 1 then
      let (q,r) := Int.quotRem ((char K)) 3
      let nxq : K := (-x) ^ q
      if (char K) == 3 then .some #[frob a - frob b * x] else
      if r == 1 then .some #[frob a, frob b * nxq] else
      .some #[frob a, 0, frob b * nxq]
    else .none
  | #[a,b,c], #[x,y₁,y₂,z] =>
    if y₁ == 0 && y₂ == 0 && z == 1 then
      let (q,r) := Int.quotRem ((char K)) 3
      let nxq : K := (-x) ^ q
      if (char K) == 3 then .some #[frob a - (frob b - frob c * x) * x] else
      if r == 1 then .some #[frob a, frob b * nxq, frob c * nxq * nxq] else
      .some #[frob a, frob c * (-x) * nxq * nxq, frob b * nxq]
    else .none
  | _,_ => .none

/-- 
The inductive representing field elements in an Extension field of `K` defined by a polynomial `P`
-/
def Extension (K : Type _) [GaloisField K] (_ : Polynomial K) := Polynomial K

instance {P : Polynomial K} [GaloisField K] : Coe (Polynomial K) (Extension K P) where
  coe := id

def Extension.defPoly {K : Type _} [GaloisField K] {P : Polynomial K} (_ : Extension K P) 
  : Polynomial K := P

/-- The irreducible monic associated to an extension field `Extension K P` of `K` -/
class IrreducibleMonic (K : Type _) [GaloisField K] where
  poly : Polynomial K

instance : IrreducibleMonic (Zmod p) where
  poly := #[0, 1]

-- instance [GaloisField K] : IrreducibleMonic (Extension K P) where
--   poly := P

-- class ExtensionField (K : Type) [GaloisField K] where
--   fromE [GaloisField (Extension K P)] [IrreducibleMonic K P] : Extension K P → Polynomial K

/-- 
Calculates powers of polynomials

TODO : Add this to YatimaStdLib
TODO : Add a repeated-squares implementation
-/
def polyPow {K : Type _} [GaloisField K] [BEq K] : Polynomial K → Nat → Polynomial K
  | _, 0 => #[1]
  | p, k + 1 => polyMul p (polyPow p k)

def polyInv {K : Type _} [GaloisField K] [BEq K] (Q P : Polynomial K) : Polynomial K :=
  let (a, _, g) := polyEuc Q P
  if g == #[1] then a else #[0]

open IrreducibleMonic in
instance [GaloisField K] [BEq K]: GaloisField (Extension K P) where
  plus := polyAdd
  times := polyMul
  null := #[0]
  ein := #[1]
  minus := polySub
  divis f g := polyMul (polyInv g P) f
  char := char K
  deg := (deg K) * degree (P)
  frob e :=
      match frobenius e P with
      | .some z => z
      | .none => polyPow e (char K)

instance [GaloisField K] [BEq K] : BEq (Extension K P) where
  beq a b := polyMod a P == polyMod b P

class TowerOfFields (K : Type _) (L : Type _) [GaloisField K] [GaloisField L] where
  embed : K → L

instance extensionFieldTower [GaloisField K] [BEq K] : TowerOfFields K (Extension K P) where
  embed x := #[x]

instance [GaloisField L] [GaloisField K] [BEq K] [BEq L]
         [t₁ : TowerOfFields K L] : TowerOfFields K (Extension L Q) where
  embed := 
    let t₂ := extensionFieldTower
    t₂.embed ∘ t₁.embed

-- fields with square roots
inductive LegendreSymbol where
  | Zero
  | QuadraticResidue
  | QuadraticNonResidue

class SqrtField (F : Type _) where
  legendre : F → LegendreSymbol
  sqrt : F → Option F

end GaloisField
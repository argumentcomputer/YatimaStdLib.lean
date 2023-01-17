import YatimaStdLib.Array
import YatimaStdLib.Nat

/-!
# AddChain

This module implements an efficient representation of numbers in terms of the double-and-add 
algorithm.

The finding an `AddChain` with `minChain` can be used to pre-calculate the function which
implements a double-and-add or square-and-multiply represention of a natural number.

The types are left polymorphic to allow for more efficient implementations of `double` in the 
case of `Chainable`, or `square` for `Square`.

## References

* Implementation taken from: https://crates.io/crates/addchain
* Algorithm based on _Addition Chains using Continued Fractions_ by Bergeron, Berstel, Brlek, Duboc
  (https://www.sciencedirect.com/science/article/abs/pii/0196677489900369)
-/

/-- The typeclass which implements efficient `add`, `mul`, `double`, and `doubleAdd` methods -/
class Chainable (α : Type _) extends BEq α, OfNat α (nat_lit 1) where
  add : α → α → α 
  mul : α → α → α 
  double : α → α := fun x => add x x
  doubleAdd : α → α → α := fun x y => add (double x) y 

/-
In this section we include the basic instances for `Chainable` that exist in the core 
numerical libraries of Lean
-/
section instances

instance (priority := low) [Add α] [Mul α] [BEq α] [OfNat α (nat_lit 1)] : Chainable α where
  add := Add.add
  mul := Mul.mul

instance [Chainable α] : Inhabited α where
  default := 1

instance [Chainable α] : HAdd α α α where
  hAdd := Chainable.add

instance [Chainable α] : HMul α α α where
  hMul := Chainable.mul

end instances

/-- The steps that can appear in an `AddChain` -/
inductive ChainStep | add (idx₁ idx₂ : Nat) | double (idx : Nat)
deriving Repr

/--
The chain of operations that can be used to represent a `Chainable` n in terms of the 
double-and-add algorithm
-/
def AddChain (α : Type _) [Chainable α] := Array α

instance [Chainable α] : Inhabited (AddChain α) where
  default := #[1]

instance [Chainable α] : HAdd (AddChain α) α (AddChain α) where
  hAdd ch n := ch.push (n + ch.back)

instance [Chainable α] : Mul (AddChain α) where
  mul ch₁ ch₂ := 
    let last := ch₁.back
    let ch₂' := ch₂.last.map (fun x => x * last) 
    ch₁.append ch₂'

/- 
In this section we implement an efficient algorithm to calculate the minimal AddChain for a natural 
number
-/
section nat
namespace Nat

mutual 

private partial def addChain (n k : Nat) : AddChain Nat := 
  let (q, r) := n.quotRem k
  if r == 0 || r == 1 then
    minChain k * minChain q + r else
    addChain k r * minChain q + r

/-- An implementation of the algorithm of BBBD to find the minimal addChain for a natural number -/
partial def minChain (n : Nat) : AddChain Nat :=
  let logN := n.log2
  if n == (1 <<< logN) then
    Array.iota logN |>.map fun k => 2^k 
  else if n == 3 then
    #[1, 2, 3] else
    let k := n / (1 <<< (logN/2))
    addChain n k

end

end Nat
end nat

namespace AddChain

private def findStep [Chainable α] (ch : AddChain α) (idx : Nat) : ChainStep := Id.run do
  let val := ch.get! idx

  for (j, left) in ch.toList.enum do
    for (k, right) in ch[:j + 1].toArray.toList.enum do
      if val == left + right then
        if j == k then
          return .double j else
          return .add j k

  return .double 0

/-- Reconstructs the double and add operations taken to generate the add-chain `ch` -/
def buildSteps [Chainable α] (ch : AddChain α) : Array ChainStep := Id.run do
  let mut answer := #[]
  let ch' := ch[1:].toArray

  for (idx, _) in ch'.toList.enum do
    answer := answer.push $ findStep ch (idx + 1)

  return answer

end AddChain

/-- 
The function which returns the `AddChain` and the `Array ChainStep` to represent the natural number 
`n` in terms of the double-and-add representation
-/
def Nat.buildAddChain (n : Nat) : AddChain Nat × Array ChainStep :=
  let ch := n.minChain
  (ch, ch.buildSteps)

/-- A typeclass that implements an efficient squaring operation to calculate fast exponentiation -/
class Square (α : Type _) extends Mul α, OfNat α (nat_lit 1) where
  square : α → α

instance [Square α] : Inhabited α where
  default := 1

instance : Square Nat where 
  square n := n ^ 2

namespace Square 

/-- Given a `steps : Array Chainstep` for an exponent `exp`, calculates `n ^ exp` -/
@[specialize] def chainExp [Square α] (steps : Array ChainStep) (n : α) : α := Id.run do
  let mut answer := #[n]

  for step in steps.toList do
    match step with
    | .add left right => 
      answer := answer.push (answer[left]! * answer[right]!)
    | .double idx => 
      answer := answer.push (square answer[idx]!)
  
  answer.back

end Square

open Square in
/-- Returns the function `n ↦ n ^ exp` by pre-calculating the `AddChain` for `exp`. -/
@[specialize] def fastExpFunc [Square α] (exp : Nat) : α → α := 
  let (_ , steps) := exp.buildAddChain
  chainExp steps

/-- A fast implementation of exponentation based off an `AddChain` representation of `exp`. -/
@[specialize] def fastExp [Square α] (n : α) (exp : Nat) : α := fastExpFunc exp n

@[default_instance] instance [Square α] : HPow α Nat α where
  hPow n pow := fastExp n pow 

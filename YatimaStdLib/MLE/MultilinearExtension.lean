import YatimaStdLib.MLE.MultilinearLagrangePolynomial
import YatimaStdLib.Bit

namespace MLE

/-- Computes the multilinear extension of a function `f : {0, 1}^ν → Zmod n` -/
def multilinearExtension (f : Nat → Zmod n) (ν : Nat) (c : Curve) :
    MultilinearPolynomial $ Zmod c.fSize :=
  .prune $ List.range (1 <<< ν) |>.foldl (init := default) fun acc w =>
    let pol := match c.cache.find? (ν, w) with
      | some pol => pol
      | none => multilinearLagrangePolynomial ν w
    acc + .scale pol (f w)

namespace Tests

open LSpec

/- A couple random functions for testing (Random number generator: My brain)-/
private def f₁ : Nat → Zmod 13
  | 0 => 7
  | 1 => 11
  | 2 => 3
  | 3 => 5
  | 4 => 12
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | _ => 0

private def f₂ : Nat → Zmod 29
  | 0 | 5 | 13 => 19
  | 1 | 12 => 7
  | 2 | 7 => 1
  | 3 => 0
  | 4 | 10 | 14 => 9
  | 6 => 28
  | 8 => 3
  | 9 | 11 => 11
  | 15 => 3
  | _ => 0

def buildCases (f : Nat → Zmod n) (ν : Nat) : Array (Zmod n) := Id.run do
  let mut answer := #[]
  for i in [:2^ν] do
    answer := answer.push (f i)
  return answer

open MultilinearPolynomial in
def buildTests (f : Nat → Zmod n) (ν : Nat) : Bool := Id.run do
  let mut comps := #[]
  let bins := getBits ν
  let results := buildCases f ν 
  let mle := multilinearExtension f ν .pallas
  for t in [:2^ν] do
    let b := eval mle bins[t]! == results[t]!
    comps := comps.push b
  dbg_trace comps
  comps.all (· == true)

#lspec
  test "Multilinear extension works 1" (buildTests f₁ 3) $
  test "Multilinear extension works 2" (buildTests f₂ 4) 

end Tests

end MLE

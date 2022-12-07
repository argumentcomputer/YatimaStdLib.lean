import YatimaStdLib.MultilinearPolynomial
import YatimaStdLib.Zmod
import YatimaStdLib.Ord
import YatimaStdLib.Array

namespace MLE

def multilinearLagrangePolynomial (w ν : Nat) : MultilinearPolynomial $ Zmod n :=
  List.range ν |>.foldl (init := .ofSummandsL [(1, [])]) fun acc i =>
    let wᵢ := w >>> i % 2
    acc * .ofPairs [(1 <<< i, 2 * wᵢ - 1), (0, 1 - wᵢ)]

def multilinearExtension (f : Nat → Zmod n) (ν : Nat) : MultilinearPolynomial $ Zmod n :=
  .prune $ List.range (1 <<< ν) |>.foldl (init := default) fun acc w =>
    acc + .scale (multilinearLagrangePolynomial w ν) (f w)

def printCache (r n : Nat) : IO Unit := do
  let mut pols : Array String := #[]
  for i in [0 : r + 1] do
    for j in [0 : r + 1] do
      let pol := @multilinearLagrangePolynomial n i j
      pols := pols.push s!"(({i}, {j}), .ofPairs {pol.toList})"
  IO.println $ ",\n".intercalate (← pols.shuffle (some 42)).data

-- #eval printCache 4 10

/-- TODO : proper caching -/
def multilinearLagrangePolynomialCache :
    Std.RBMap (Nat × Nat) (MultilinearPolynomial $ Zmod n) compare := .ofList [
((1, 1), .ofPairs [(0, 0), (1, 1)]),
((3, 1), .ofPairs [(0, 0), (1, 1)]),
((4, 4), .ofPairs [(0, 0), (1, 0), (2, 0), (3, 0), (4, 1), (5, -1), (6, -1), (7, 1), (8, 0), (9, 0), (10, 0), (11, 0), (12, -1), (13, 1), (14, 1), (15, -1)]),
((1, 3), .ofPairs [(0, 0), (1, 1), (2, 0), (3, -1), (4, 0), (5, -1), (6, 0), (7, 1)]),
((3, 4), .ofPairs [(0, 0), (1, 0), (2, 0), (3, 1), (4, 0), (5, 0), (6, 0), (7, -1), (8, 0), (9, 0), (10, 0), (11, -1), (12, 0), (13, 0), (14, 0), (15, 1)]),
((2, 3), .ofPairs [(0, 0), (1, 0), (2, 1), (3, -1), (4, 0), (5, 0), (6, -1), (7, 1)]),
((0, 4), .ofPairs [(0, 1), (1, -1), (2, -1), (3, 1), (4, -1), (5, 1), (6, 1), (7, -1), (8, -1), (9, 1), (10, 1), (11, -1), (12, 1), (13, -1), (14, -1), (15, 1)]),
((0, 0), .ofPairs [(0, 1)]),
((3, 2), .ofPairs [(0, 0), (1, 0), (2, 0), (3, 1)]),
((1, 0), .ofPairs [(0, 1)]),
((3, 3), .ofPairs [(0, 0), (1, 0), (2, 0), (3, 1), (4, 0), (5, 0), (6, 0), (7, -1)]),
((2, 2), .ofPairs [(0, 0), (1, 0), (2, 1), (3, -1)]),
((1, 2), .ofPairs [(0, 0), (1, 1), (2, 0), (3, -1)]),
((3, 0), .ofPairs [(0, 1)]),
((0, 3), .ofPairs [(0, 1), (1, -1), (2, -1), (3, 1), (4, -1), (5, 1), (6, 1), (7, -1)]),
((4, 0), .ofPairs [(0, 1)]),
((4, 2), .ofPairs [(0, 1), (1, -1), (2, -1), (3, 1)]),
((0, 1), .ofPairs [(0, 1), (1, -1)]),
((2, 4), .ofPairs [(0, 0), (1, 0), (2, 1), (3, -1), (4, 0), (5, 0), (6, -1), (7, 1), (8, 0), (9, 0), (10, -1), (11, 1), (12, 0), (13, 0), (14, 1), (15, -1)]),
((0, 2), .ofPairs [(0, 1), (1, -1), (2, -1), (3, 1)]),
((4, 1), .ofPairs [(0, 1), (1, -1)]),
((2, 0), .ofPairs [(0, 1)]),
((4, 3), .ofPairs [(0, 0), (1, 0), (2, 0), (3, 0), (4, 1), (5, -1), (6, -1), (7, 1)]),
((1, 4), .ofPairs [(0, 0), (1, 1), (2, 0), (3, -1), (4, 0), (5, -1), (6, 0), (7, 1), (8, 0), (9, -1), (10, 0), (11, 1), (12, 0), (13, 1), (14, 0), (15, -1)]),
((2, 1), .ofPairs [(0, 1), (1, -1)])
] _

def multilinearExtension' (f : Nat → Zmod n) (ν : Nat) : MultilinearPolynomial $ Zmod n :=
  .prune $ List.range (1 <<< ν) |>.foldl (init := default) fun acc w =>
    let pol := match multilinearLagrangePolynomialCache.find? (w, ν) with
      | some pol => pol
      | none => multilinearLagrangePolynomial w ν
    acc + .scale pol (f w)

namespace Tests

open LSpec

/-- TODO : proper testing -/
def f : Nat → Zmod 5 := fun _ => 0

#lspec
  test "" (multilinearExtension f 0 == multilinearExtension' f 0) $
  test "" (multilinearExtension f 0 == .ofSummandsL [])

end Tests

end MLE

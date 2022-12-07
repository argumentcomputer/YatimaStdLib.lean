import YatimaStdLib.MultilinearPolynomial
import YatimaStdLib.Zmod
import YatimaStdLib.MLE.Cache
import YatimaStdLib.Array
import YatimaStdLib.Ord

namespace MLE

/--
Computes the multilinear Lagrange basis polynomial with interpolating set
{0, 1}^ν.
-/
def multilinearLagrangePolynomial (w ν : Nat) : MultilinearPolynomial $ Zmod n :=
  List.range ν |>.foldl (init := .ofPairs [(0, 1)]) fun acc i =>
    let wᵢ := w >>> i % 2
    acc * .prune (.ofPairs [(1 <<< i, 2 * wᵢ - 1), (0, 1 - wᵢ)])

/-- Computes the multilinear extension of a function `f : {0, 1}^ν → Zmod n` -/
def multilinearExtension (f : Nat → Zmod n) (ν : Nat) : MultilinearPolynomial $ Zmod n :=
  .prune $ List.range (1 <<< ν) |>.foldl (init := default) fun acc w =>
    acc + .scale (multilinearLagrangePolynomial w ν) (f w)

def mkCacheContent (pols : String) : String :=
s!"import YatimaStdLib.MLE.CacheDSL
open MLE.DSL in
def MLE.multilinearLagrangePolynomialCacheData : List $ (Nat × Nat) × (List $ Nat × Int) := ⟪
{pols}⟫"

def writeCache (r n : Nat) : IO Unit := do
  let mut pols : Array String := #[]
  for i in [0 : r + 1] do
    for j in [0 : r + 1] do
      let pol := @multilinearLagrangePolynomial n i j
      let polStr := " ".intercalate (pol.toList.map fun (b, c) => s!"({b} {c})")
      pols := pols.push s!"  {i} {j} # {polStr}"
  let polsStr := ",\n".intercalate (← pols.shuffle (some 42)).data
  IO.FS.writeFile ⟨"YatimaStdLib/MLE/Cache.lean"⟩ (mkCacheContent polsStr)

-- Uncomment this line to write the cache file (be careful with the parameters)
-- #eval writeCache 4 10

def multilinearLagrangePolynomialCache :
    Std.RBMap (Nat × Nat) (MultilinearPolynomial $ Zmod n) compare :=
  multilinearLagrangePolynomialCacheData.foldl (init := default) fun acc (k, v) =>
    acc.insert k (.ofList v _)

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

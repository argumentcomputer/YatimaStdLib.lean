import YatimaStdLib.MLE.Cache
import YatimaStdLib.Array
import YatimaStdLib.Ord

namespace MLE

/--
Computes the multilinear Lagrange basis polynomial with interpolating set
{0, 1}^ν.
-/
def multilinearLagrangePolynomial (ν w : Nat) : MultilinearPolynomial $ Zmod n :=
  List.range ν |>.foldl (init := .ofPairs [(0, 1)]) fun acc i =>
    let wᵢ := w >>> i % 2
    acc * .prune (.ofPairs [(1 <<< i, 2 * wᵢ - 1), (0, 1 - wᵢ)])

open Lean (Json)

def jsonCache (νMax : Nat) : Array Json :=
  List.range νMax.succ |>.foldl (init := #[]) fun acc ν =>
    List.range νMax.succ |>.foldl (init := acc) fun acc w =>
      let pol := @multilinearLagrangePolynomial 0 ν w
        |>.foldl (init := #[]) fun acc b c => acc.push $ .arr #[b, c]
      acc.push $ .arr #[ν, w, .arr pol]

def writeCache (νMax : Nat) : IO Unit := do
  let json : Json := .arr $ ← (jsonCache νMax).shuffle (some 42)
  IO.FS.writeFile ⟨"YatimaStdLib/MLE/cache.json"⟩ (json.pretty 200)

-- Uncomment this line to write the cache file (be careful with the parameter)
-- #eval writeCache 4

/-- Computes the multilinear extension of a function `f : {0, 1}^ν → Zmod n` -/
def multilinearExtension (f : Nat → Zmod n) (ν : Nat) : MultilinearPolynomial $ Zmod n :=
  .prune $ List.range (1 <<< ν) |>.foldl (init := default) fun acc w =>
    acc + .scale (multilinearLagrangePolynomial ν w) (f w)

def multilinearLagrangePolynomialCache :
    Std.RBMap (Nat × Nat) (MultilinearPolynomial $ Zmod n) compare :=
  cachedMLPData.foldl (init := default) fun acc (k, v) =>
    acc.insert k (.ofList v _)

def multilinearExtension' (f : Nat → Zmod n) (ν : Nat) : MultilinearPolynomial $ Zmod n :=
  .prune $ List.range (1 <<< ν) |>.foldl (init := default) fun acc w =>
    let pol := match multilinearLagrangePolynomialCache.find? (ν, w) with
      | some pol => pol
      | none => multilinearLagrangePolynomial ν w
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

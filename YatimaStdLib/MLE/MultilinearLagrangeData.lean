import YatimaStdLib.MultilinearPolynomial
import YatimaStdLib.Zmod
import YatimaStdLib.Array
import Lean.Data.Json

namespace MLE

/--
Computes the multilinear Lagrange basis polynomial with interpolating set
`{0, 1}^ν` for a given `w`.
-/
def multilinearLagrangePolynomial (ν w : Nat) : MultilinearPolynomial $ Zmod n :=
  List.range ν |>.foldl (init := .ofPairs [(0, 1)]) fun acc i =>
    let wᵢ := w >>> i % 2
    acc * .prune (.ofPairs [(1 <<< i, 2 * wᵢ - 1), (0, 1 - wᵢ)])

open Lean (Json)

/--
Creates an array of JSON data, each element encoding a polynomial. Adding `1` to
the coefficients saves a few `-` characters because `-1`s turn into `0`s.
-/
def buildJsonCache (νMax : Nat) : Array Json :=
  List.range νMax.succ |>.foldl (init := #[]) fun acc ν =>
    List.range νMax.succ |>.foldl (init := acc) fun acc w =>
      let pol := @multilinearLagrangePolynomial 3 ν w
        |>.foldl (init := #[]) fun acc b c => acc.push $ .arr #[b, c + (1 : Int)]
      acc.push $ .arr #[ν, w, .arr pol]

/-- Writes cached polynomials as a JSON file -/
def writeJsonCache (νMax : Nat) : IO Unit := do
  let json := Json.arr $ buildJsonCache νMax
  IO.FS.writeFile ⟨"YatimaStdLib/MLE/cache.json"⟩ json.compress

-- Uncomment to write the cache file (be careful with the parameter):
-- #eval writeJsonCache 17

open Lean (Json)

abbrev MLPData := (Nat × Nat) × List (Nat × Int)

/-- Extracts data for one MLP from a `Json.arr` node -/
def jsonToMLP : Json → Except String MLPData
  | .arr #[ν, w, .arr summands] => do
    let summands ← summands.foldlM (init := []) fun acc s => do
      match s with
      | .arr #[b, c] => pure $ (← b.getNat?, (← c.getInt?) - 1) :: acc
      | x => throw s!"Unexpected JSON for MLP summand: {x.pretty}"
    return ((← ν.getNat?, ← w.getNat?), summands)
  | x => throw s!"Unexpected JSON for MLP: {x.pretty}"

/-- Extracts data for many MLPs from a `Json.arr` node -/
def jsonToArrayMLP : Json → Except String (Array MLPData)
  | .arr MLPs => MLPs.mapM jsonToMLP
  | x => throw s!"Unexpected JSON for MLP array: {x.pretty}"

def readCachedMLPData : IO $ Array MLPData := do
  match Json.parse (← IO.FS.readFile ⟨"YatimaStdLib/MLE/cache.json"⟩) with
  | .error e => panic! e
  | .ok cachedJson => match jsonToArrayMLP cachedJson with
    | .error e => panic! e
    | .ok data => data.shuffle (some 42)

initialize cachedMLPData : Array MLPData ← readCachedMLPData

end MLE

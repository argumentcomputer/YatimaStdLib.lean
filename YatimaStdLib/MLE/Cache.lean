import YatimaStdLib.MultilinearPolynomial
import YatimaStdLib.Zmod
import Lean.Data.Json

namespace MLE

open Lean (Json)

abbrev MLPData := (Nat × Nat) × List (Nat × Int)

def jsonToCachedMLP : Json → Except String MLPData
  | .arr #[ν, w, .arr summands] => do
    let mlpData ← summands.foldlM (init := []) fun acc s => do
      match s with
      | .arr #[b, c] => pure $ (← b.getNat?, ← c.getInt?) :: acc
      | x => throw s!"Unexpected JSON for MLP summand: {x.pretty}"
    return ((← ν.getNat?, ← w.getNat?), mlpData)
  | x => throw s!"Unexpected JSON for MLP: {x.pretty}"

def jsonToCachedMLPs : Json → Except String (Array MLPData)
  | .arr cachedMLPs => cachedMLPs.mapM jsonToCachedMLP
  | x => throw s!"Unexpected JSON for cached MLPs: {x.pretty}"

def readCache : IO $ Array MLPData := do
  match Json.parse (← IO.FS.readFile ⟨"YatimaStdLib/MLE/cache.json"⟩) with
  | .error e => panic! e
  | .ok cachedJson => match jsonToCachedMLPs cachedJson with
    | .error e => panic! e
    | .ok cache => pure cache

initialize cachedMLPData : Array MLPData ← readCache

end MLE

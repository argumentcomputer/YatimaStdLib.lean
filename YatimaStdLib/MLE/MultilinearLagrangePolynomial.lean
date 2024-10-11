import YatimaStdLib.MLE.MultilinearLagrangeData
import YatimaStdLib.Ord

namespace MLE

scoped instance : Coe (List (Nat × Int)) (List (Nat × Zmod n)) where
  coe x := x.map fun (n, i) => (n, i)

/-- Reads cached polynomials from a JSON file -/
def polynomialsFromCache :
    IO $ Batteries.RBMap (Nat × Nat) (MultilinearPolynomial $ Zmod n) compare :=
  return cachedMLPData.foldl (fun acc (k, v) => acc.insert k (.ofPairs v)) default

def pallasFSize := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
def vestaFSize  := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

initialize pallasCache :
  Batteries.RBMap (Nat × Nat) (MultilinearPolynomial $ Zmod pallasFSize) compare
    ← polynomialsFromCache

initialize vestaCache :
  Batteries.RBMap (Nat × Nat) (MultilinearPolynomial $ Zmod vestaFSize) compare
    ← polynomialsFromCache

inductive Curve
  | pallas
  | vesta

def Curve.fSize : Curve → Nat
  | .pallas => pallasFSize
  | .vesta  => vestaFSize

def Curve.cache : (c : Curve) →
    Batteries.RBMap (Nat × Nat) (MultilinearPolynomial $ Zmod c.fSize) compare
  | .pallas => pallasCache
  | .vesta  => vestaCache

end MLE

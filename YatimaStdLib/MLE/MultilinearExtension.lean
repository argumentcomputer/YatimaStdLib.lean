import YatimaStdLib.MLE.MultilinearLagrangePolynomial
import YatimaStdLib.Bit

namespace MLE

/-- Computes the multilinear extension of a function `f : {0, 1}^ν → Zmod n` -/
def multilinearExtension (c : Curve) (f : Nat → Zmod c.fSize) (ν : Nat) :
    MultilinearPolynomial $ Zmod c.fSize :=
  .prune $ List.range (1 <<< ν) |>.foldl (init := default) fun acc w =>
    let pol := match c.cache.find? (ν, w) with
      | some pol => pol
      | none => multilinearLagrangePolynomial ν w
    acc + .scale pol (f w)

end MLE

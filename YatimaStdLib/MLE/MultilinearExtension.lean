import YatimaStdLib.MLE.MultilinearLagrangePolynomial

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

/-- TODO : proper testing -/
def f : Nat → Zmod 5 := fun _ => 0

#lspec
  test "" (multilinearExtension f 0 .pallas == .ofSummandsL [])

end Tests

end MLE

namespace Identity

structure Identity (A : Type α) where
  runIdentity : A

@[inline] instance idToA : Coe (Identity A) A where
  coe a := a.runIdentity

@[inline] instance aToIdA : Coe A (Identity A) where
  coe a := Identity.mk a

end Identity
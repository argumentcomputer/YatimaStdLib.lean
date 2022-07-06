namespace Identity

structure Identity (A : Type α) where
  runIdentity : A

instance : Coe A (Identity A) where
  coe a := Identity.mk a

end Identity
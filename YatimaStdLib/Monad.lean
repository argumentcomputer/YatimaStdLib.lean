namespace Monad

def seqComp {M : Type u → Type v} [Monad M] (ma : M A) (mb : M B) :=
  ma >>= fun _ => mb

end Monad
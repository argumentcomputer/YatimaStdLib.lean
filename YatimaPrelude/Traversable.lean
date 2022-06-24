import YatimaPrelude.Foldable

namespace Traversable

class Traversable (T : Type → Type) [Functor T] [Foldable.Foldable T] where
  traverse : [Applicative F] → (A → F B) → T A → F (T B)
 
def sequenceA [Applicative F] [Functor T] [Foldable.Foldable T] [Traversable T] : T (F A) → F (T A) :=
  Traversable.traverse id

def mapM [Monad M] [Functor T] [Foldable.Foldable T] [Traversable T] : (A → M B) → T A → M (T B) :=
  Traversable.traverse

def sequence [Monad M] [Functor T] [Foldable.Foldable T] [Traversable T] : T (M A) → M (T A) :=
  sequenceA

end Traversable
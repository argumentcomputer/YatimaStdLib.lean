import YatimaStdLib.Applicative
import YatimaStdLib.Foldable

/-
Functors representing data structures that can be transformed to structures of the same shape by
performing an Applicative (or, therefore, Monad) action on each element from left to right.

Inspired by:
https://hackage.haskell.org/package/base-4.16.1.0/docs/Data-Traversable.html#t:Traversable
-/
class Traversable (T : Type u → Type u) [Functor T] [Foldable T] where
  traverse : [Applicative F] → (A → F B) → T A → F (T B)

namespace Traversable

universe u

def sequenceA [Applicative F] [Functor T] [Foldable T] [Traversable T] : T (F A) → F (T A) :=
  Traversable.traverse id

def mapM [Monad M] [Functor T] [Foldable T] [Traversable T] : (A → M B) → T A → M (T B) :=
  Traversable.traverse

def sequence [Monad M] [Functor T] [Foldable T] [Traversable T] : T (M A) → M (T A) :=
  sequenceA

end Traversable

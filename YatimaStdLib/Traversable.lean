import YatimaStdLib.Applicative
import YatimaStdLib.Foldable
import YatimaStdLib.List
import YatimaStdLib.NonEmpty

namespace Traversable

/-
Functors representing data structures that can be transformed to structures of the same shape by 
performing an Applicative (or, therefore, Monad) action on each element from left to right.

Inspired by:
https://hackage.haskell.org/package/base-4.16.1.0/docs/Data-Traversable.html#t:Traversable
-/
class Traversable (T : Type → Type) [Functor T] [Foldable T] where
  traverse : [Applicative F] → (A → F B) → T A → F (T B)
 
def sequenceA [Applicative F] [Functor T] [Foldable T] [Traversable T] : T (F A) → F (T A) :=
  Traversable.traverse id

def mapM [Monad M] [Functor T] [Foldable T] [Traversable T] : (A → M B) → T A → M (T B) :=
  Traversable.traverse

def sequence [Monad M] [Functor T] [Foldable T] [Traversable T] : T (M A) → M (T A) :=
  sequenceA

instance funList : Functor List where
  map := List.map

instance trList : Traversable List where
  traverse f :=
    let cons_f x ys := Applicative.liftA₂ (fun x xs => x :: xs) (f x) ys
    List.foldr cons_f (pure [])

end Traversable

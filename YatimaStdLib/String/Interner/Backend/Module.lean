import YatimaStdLib.String.Interner.Backend.Buffer
/-!

# Backends 

Backends for the `StringInterner`.

The backend is the method or strategy that handles the actual interning.
There are trade-offs for the different kinds of backends. A user should
find the backend that suits their use case best.

# Acknowledgements

This implementation is entirely based on the Rust `string-intern` crate 
located [here](https://github.com/robbepop/string-interner). 
All credits should be given to them. 

-/

namespace StringInterner 

-- inductive Backend where 
--   | bucket | buffer | simple | string

class MonadBackend (m : Type → Type) where 
  intern : String → m Nat
  resolve! : Nat → m String

-- idk, should this be a thing?
-- export MonadBackend (intern resolve)

instance (m : Type → Type) (n : Type → Type) 
  [MonadLift m n] [MonadBackend m] : MonadBackend n := {
    intern := fun s => liftM (MonadBackend.intern s : m _),
    resolve! := fun n => liftM (MonadBackend.resolve! n : m _)
}


instance : MonadBackend BufferM := {
  intern := BufferM.pushString,
  resolve! := BufferM.resolveIndexToStr
}

end StringInterner
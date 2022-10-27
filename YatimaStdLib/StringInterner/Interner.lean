import YatimaStdLib.StringInterner.Backend.Module
import Std.Data.HashMap

/-!
# String Interner

Data structure to intern and resolve strings.

Caches strings efficiently, with minimal memory footprint and associates them
with unique symbols. These symbols allow constant time comparisons and look-ups
to the underlying interned strings.

The following API covers the main functionality:

- [`StringInterner.getOrIntern`]: To intern a new string.
    - This maps from `string` type to `symbol` type.
- [`StringInterner.resolve`]: To resolve your already interned strings.
    - This maps from `symbol` type to `string` type.

# Acknowledgements

This implementation is entirely based on the Rust `string-intern` crate located
[here](https://github.com/robbepop/string-interner). All credits should be given
to them.

# TODO

Implement tests with LSpec
-/

abbrev StringInterner.Symbol := Nat

abbrev StringInterner.SymbolMap := Std.HashMap UInt64 StringInterner.Symbol

abbrev StringInterner :=
  StateT StringInterner.SymbolMap StringInterner.BufferM

namespace StringInterner

def run (state : StringInterner α) (b : Buffer := default)
    (map : SymbolMap := default) : (α × SymbolMap) × Buffer :=
  StateT.run (StateT.run state map) b

def run' (state : StringInterner α) (b : Buffer := default)
    (map : SymbolMap := default) : α :=
  StateT.run' (StateT.run' state map) b

@[inline] def insert (hash : UInt64) (symbol : Symbol) : StringInterner Unit :=
  modify fun s => s.insert hash symbol

def getOrIntern (str : String) : StringInterner Symbol := do
  let hash := str.hash
  match (← get).find? hash with
    | some sym => return sym
    | none =>
      let symbol ← MonadBackend.intern str
      insert hash symbol
      return symbol

def get (str : String) : StringInterner (Option Symbol) := do
  return (← StateT.get).find? str.hash

def resolve! (symbol : Symbol) : StringInterner String :=
  MonadBackend.resolve! symbol

end StringInterner

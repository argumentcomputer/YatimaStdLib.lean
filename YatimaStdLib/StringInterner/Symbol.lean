/-!

# Symbols

Types implementing this trait can be used as symbols for string interners.

The `StringInterner.getOrIntern` method returns `Symbol` types that allow
to look-up the original string using `StringInterner::resolve`.

# Note

Optimal symbols allow for efficient comparisons and have a small memory footprint.

# Acknowledgements

This implementation is entirely based on the Rust `string-intern` crate
located [here](https://github.com/robbepop/string-interner).
All credits should be given to them.

-/

namespace StringInterner

-- TODO: leave unimplemented for now
-- class Symbol (α : Type _) where
--   /-- Creates a symbol from a `usize`.
--     Returns `None` if `index` is out of bounds for the symbol. -/
--   tryFromUSize : USize → Option α
--   /-- Returns the `usize` representation of `self`. -/
--   toUSize : α → USize

-- def Symbol.ofUSize! [Inhabited α] [Symbol α] (index : USize) : α :=
--   tryFromUSize index |>.get!

end StringInterner

import LSpec
import YatimaStdLib.Nat

open Lean LSpec Nat

#lspec test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 5 == 8) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 100 == 128) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 1000 == 1024) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 0 == 1) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 30000 = 32768)
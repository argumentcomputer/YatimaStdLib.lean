import LSpec
import YatimaStdLib.Nat

open Lean LSpec Nat

#lspec test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 5 == 8) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 100 == 128) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 1000 == 1024) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 0 == 1) $
       test "nextPowerOfTwo' is correct" (nextPowerOfTwo' 30000 = 32768)

#lspec test "powMod is correct" (powMod 3 17 21 == 2) $
       test "powMod is correct" (powMod 4 78 101 == 0) $
       test "powMod is correct" (powMod 27 98 317 == 8) $
       test "powMod is correct" (powMod 14 5 801 == 13) $
       test "powMod is correct" (powMod 56 2 55 == 16) $
       test "powMod is correct" (powMod 4 7 91 == 3)

#lspec test "legendre is correct" (legendre 31 5 == 1) $
       test "legendre is correct" (legendre 87 9 == 0) $
       test "legendre is correct" (legendre 4 3 == 1) $
       test "legendre is correct" (legendre 73 103 == 102) $
       test "legendre is correct" (legendre 7 19 == 1) $
       test "legendre is correct" (legendre 3 113 == 112)

#lspec test "tonelli is correct" (tonelli 10 13 == some (7, 6)) $
       test "tonelli is correct" (tonelli 56 101 == some (37,64)) $
       test "tonelli is correct" (tonelli 1030 10009 == some (1632,8377)) $
       test "tonelli is correct" (tonelli 1032 10009 == none) $
       test "tonelli is correct" (tonelli 44402 100049 == some (30468,69581)) $
       test "tonelli is correct" (tonelli 665820697 1000000009 == some (378633312,621366697))
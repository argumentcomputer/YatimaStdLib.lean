import LSpec
import YatimaStdLib.Nat

open Lean LSpec Nat

#lspec test "next_power_of_two works" (nextPowerOfTwo 5 == 8) $
       test "next_power_of_two works" (nextPowerOfTwo 100 == 128) $
       test "next_power_of_two works" (nextPowerOfTwo 1000 == 1024) $
       test "next_power_of_two works" (nextPowerOfTwo 0 == 1) $
       test "next_power_of_two works" (nextPowerOfTwo 30000 = 32768)
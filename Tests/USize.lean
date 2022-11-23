import LSpec
import YatimaStdLib.USize

open Lean LSpec USize

#lspec test "next_power_of_two works" (next_power_of_two 5 == 8) $
       test "next_power_of_two works" (next_power_of_two 100 == 128) $
       test "next_power_of_two works" (next_power_of_two 1000 == 1024) $
       test "next_power_of_two works" (next_power_of_two 0 == 1) $
       test "next_power_of_two works" (next_power_of_two 30000 = 32768)
import YatimaStdLib.Arithmetic
import LSpec

open LSpec

def mRTests : TestSeq := 
  test "MR Finds small primes" (millerRabinTest 71 5 == true) $
  test "MR Finds small primes 2" (millerRabinTest 821 5 == true) $
  test "MR Detects non-primes" (millerRabinTest 885 5 == false) $
  test "MR Detects non-primes 2" (millerRabinTest 1083 5 == false) $
  test "MR Works for big primes" (millerRabinTest 234092388421 5 == true)

def dLogTests : TestSeq := 
  test "DL works on small inputs" (dLog 53 68 463 == some 434) $
  test "DL works on small inputs 2" (dLog 5 39 61 == some 13) $
  test "DL works with no solutions" (dLog 49 483 653 == none) $
  test "DL works on big inputs" (dLog 39 519726712005 843929400311 == some 83483865923) $
  test "DL works on big inputs 2" (dLog 391033 239491023123 738239493991 == some 323072654827)

def main := lspecIO $
  mRTests ++ dLogTests

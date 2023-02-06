import YatimaStdLib.Arithmetic
import LSpec

open LSpec

def main := lspecIO $
  test "works on big inputs" (dLog 39
         519726712005
         843929400311 == 
         some 83483865923)

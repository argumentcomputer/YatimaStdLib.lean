import YatimaStdLib.Arithmetic
import LSpec

open LSpec

def main := lspecIO $
  test "works on big inputs" (dLog 37
         18094411505653743630246040579337206337386467465616016462821305448438411906485
         0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 == 
         some 0x72eda753299d7d473339d80809a1d80553bda402fffe5bfeffffffff00000001)

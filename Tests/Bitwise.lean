import LSpec
import YatimaStdLib.Bitwise

open LSpec Bitwise

def landTests : TestSeq :=
  group "bitwise AND" $
    test "pos pos" (land   42    15  = 10) $
    test "pos neg" (land   42  (-15) = 32) $
    test "neg pos" (land (-42)   15  = 6)  $
    test "neg neg" (land (-42) (-15) = -48)

def lorTests : TestSeq :=
  group "bitwise OR" $
    test "pos pos" (lor   42    15  = 47)  $
    test "pos neg" (lor   42  (-15) = -5)  $
    test "neg pos" (lor (-42)   15  = -33) $
    test "neg neg" (lor (-42) (-15) = -9)

def lxorTests : TestSeq :=
  group "bitwise XOR" $
    test "pos pos" (lxor   42    15  = 37)  $
    test "pos neg" (lxor   42  (-15) = -37) $
    test "neg pos" (lxor (-42)   15  = -39) $
    test "neg neg" (lxor (-42) (-15) = 39)

def shiftlTests : TestSeq :=
  group "shift left" $
    test "pos pos" (shiftLeft 16      2  = 64)  $
    test "pos neg" (shiftLeft 16    (-2) = 4)   $
    test "neg pos" (shiftLeft (-16)   2  = -64) $
    test "neg neg" (shiftLeft (-16) (-2) = -4)

def shiftrTests : TestSeq :=
  group "shift right" $
    test "pos pos" (shiftRight 16      2  = 4)  $
    test "pos neg" (shiftRight 16    (-2) = 64) $
    test "neg pos" (shiftRight (-16)   2  = -4) $
    test "neg neg" (shiftRight (-16) (-2) = -64)

def main := lspecIO $
  landTests ++ lorTests ++ lxorTests ++ shiftlTests ++ shiftrTests

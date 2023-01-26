import LSpec
import Lean.Data.Rat
import YatimaStdLib.Polynomial

open Lean LSpec Polynomial

def normTests : TestSeq := 
       (test "norm works" (norm #[1,2,3] == #[1,2,3])) ++
       (test "norm works 2" (norm #[1,2,3, 0, 0, 0, 0] == #[1,2,3])) ++
       (test "norm works 3" (norm #[0] == #[0])) ++
       (test "norm works 4" (norm #[0,0,0,0] == #[0]))

def degreeTests : TestSeq :=
       (test "degree works" (degree #[1] == 0)) ++
       (test "degree works 2" (degree #[0,1,2,3,4,5] == 5)) ++
       (test "degree works 3" (degree #[0,1,2,3,4,0,0,0,0] == 4))

def isZeroTests : TestSeq :=
       (test "isZero works" (isZero #[0])) ++
       (test "isZero works 2 " (not $ isZero #[1,0,0])) ++
       (test "isZero works 3" (isZero #[0,0,0,0]))

def constantTests : TestSeq :=
       (test "constant works" (constant #[3, 2, 1] == 3)) ++
       (test "constant works 2" (constant #[] == 0)) ++
       (test "constant works 3" (constant #[1] == 1))

def leadTests : TestSeq :=
       (test "lead works" (lead #[0,1,2,3] == 3)) ++
       (test "lead works 2" (lead #[1,2,3,0,0,0] == 3)) ++
       (test "lead works 3" (lead #[] == 0))

def isMonicTests : TestSeq :=
       (test "isMonic works" (isMonic #[3,2,1])) ++
       (test "isMonic works 2" (not $ isMonic #[1,2,3])) ++
       (test "isMonic works 3" (isMonic #[3,2,1, 0, 0, 0])) ++
       (test "isMonic works 4" (not $ isMonic #[]))

def evalTests : TestSeq :=
       (test "eval works" (eval #[3,2,1] 3 == 18)) ++
       (test "eval works 2" (eval #[1, -2, 1, 0, 0, 0] 1 == 0)) ++
       (test "eval works 3" (eval #[] 6 == 0)) ++
       (test "eval works 4" (eval #[1] 5 == 1))

def addTests : TestSeq :=
       (test "add works" (polyAdd #[3,2,1] #[1,2,3, 0, 0] == #[4, 4, 4])) ++
       (test "add works 2" (polyAdd #[0] #[1,2,3] == #[1,2,3])) ++
       (test "add works 3" (polyAdd #[0,0,0,1] #[1,2,3] == #[1,2,3,1,0]))

def negTests : TestSeq :=
       (test "neg works" (- (ofArray #[(0 : Int)]) == #[0])) ++ 
       (test "neg works 2" (- (ofArray #[-1,-2,3]) == #[1,2,-3]))

def mulTests : TestSeq :=
       (test "mul works" (polyMul #[1] #[3, 4, -1] == #[3, 4, -1])) ++
       (test "mul works 2" (polyMul #[1, 2, 3, 4, 5] #[0] == #[0])) ++
       (test "mul works 3" (polyMul #[0, 4, 3, 2] #[-1, -1, 2, 4, 0, 0] == #[0, -4, -7, 3, 20, 16, 8]))

def divTests : TestSeq :=
       (test "div works" (polyDiv #[1,0,1] #[1,1,0] == #[-1, 1])) ++
       (test "div works 2" (polyDiv #[-1,0,1,0] #[-1,1,0] == #[1,1])) ++
       (test "div works 3" (polyDiv (#[1,2,1] : Polynomial Rat) #[2] == #[1/2, 1, 1/2])) ++
       (test "div works 4" (polyDiv (#[1,2,3] : Polynomial Rat) #[4,4] == #[-1/4, 3/4])) ++
       (test "div works 5" (polyDiv (#[1,2,3] : Polynomial Rat) #[0] == #[0])) ++
       (test "div works 6" (polyDiv (#[1,2,3,4] : Polynomial Rat) #[1,2,3] == #[1/9, 4/3]))

def modTests : TestSeq :=
       (test "mod works" (polyMod (#[1,2,3,0] : Polynomial Rat) #[4,4,0] == #[2])) ++
       (test "mod works 2" (polyMod #[-1,0,1,0] #[-1,1,0]  == #[0])) ++
       (test "mod works 3" (polyMod #[1,2,3] #[1,2,3] == #[0])) ++
       (test "mod works 4" (polyMod #[1,2,3] #[1,2,3,4] == #[1,2,3])) ++
       (test "mod works 5" (polyMod (#[1,2,3,4] : Polynomial Rat) #[1,2,3] == #[8/9, 4/9])) ++
       (test "mod works 6" (polyMod #[1,2,3] #[0] == #[1,2,3]))

def polyEucTests : TestSeq :=
       (test "polyEuc works" 
       (polyEuc (#[-1, 3, 2, 7] : Polynomial Rat) #[1, 0, 1] == 
       (#[-3/25, 4/25], #[22/25, 13/25, -28/25], #[1]))) ++
       (test "polyEuc works 2"
       (polyEuc (#[1, -2, 1] : Polynomial Rat) #[1, 0, -1] == 
       (#[-1/2], #[-1/2], #[-1, 1]))) ++
       (test "polyEuc works 3"
       (polyEuc #[(1 : Rat), 1] #[1] == (#[0], #[1], #[1]))) ++
       (test "polyEuc works 4"
       (polyEuc #[(1 : Rat), 1] #[0] == (#[1], #[0], #[1, 1]))) ++
       (test "polyEuc works 5"
       (polyEuc #[(24 : Rat), -50, 35, -10, 1] #[90, -153, 77, -15, 1] == 
       (#[11/8,-5/24], #[-1/3,5/24], #[3, -4, 1])))

def rootsToPolyTests : TestSeq :=
       (test "rootsToPoly works" (rootsToPoly [0,0,0] == #[0,0,0,1])) ++
       (test "rootsToPoly works 2" (rootsToPoly [1, -1] == #[-1, 0, 1])) ++
       (test "rootsToPoly works 3" (rootsToPoly [0,1,2,3] == #[0,-6, 11, -6, 1])) ++
       (test "rootsToPoly works 4" (rootsToPoly [] == #[1]))

def main := lspecIO $
       normTests ++ degreeTests ++ isZeroTests ++ constantTests ++ leadTests ++ isMonicTests ++ 
       evalTests ++ addTests ++ negTests ++ mulTests ++ divTests ++ modTests ++ polyEucTests ++
       rootsToPolyTests
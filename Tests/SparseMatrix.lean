import LSpec
import Lean.Data.Rat
import YatimaStdLib.SparseMatrix

open Lean LSpec SparseMatrix

def mat₁ : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0), 4), ((0,1),7), ((1,0),5), ((1,1),3)]

def mat₂ : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0), 7), ((0,1),5), ((1,0),6), ((1,1),6)]

def res : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0), 11), ((0,1),12), ((1,0),11), ((1,1),9)]

def mat1 : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0), 0), ((0,1),1), ((1,0),5), ((1,1),3)]

def mat2 : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0), 4), ((0,1),5), ((1,0),5), ((1,1),6)]

def res' : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0), 4), ((0,1),6), ((1,0),10), ((1,1),9)]

def res'' : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0),0), ((0,1),2), ((1,0),10), ((1,1),6)]

#eval mat1 + mat1

#lspec test "addition works" (mat₁ + mat₂ == res) $
       test "addition works" (mat1 + mat2 == res') $
       test "addition works" (mat1 + mat1 == res'')
#lspec test "dim works" (mat1.dim == (2,2))
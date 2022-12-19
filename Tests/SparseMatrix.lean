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

def resProd : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0),70), ((0,1),62), ((1,0),53), ((1,1),43)]

def resProd' : SparseMatrix Int :=
  ofArrayWithDims 2 2 #[((0,0),5), ((0,1),6), ((1,0),35), ((1,1),43)]

def anotherMat : SparseMatrix Int :=
  ofArrayWithDims 3 3
    #[ ((0,0), 56), ((0,1), 32), ((0,2), 21),
       ((1,0), 34), ((1,1), 24), ((1,2), 21),
       ((2,0), 43), ((2,1), 53), ((2,2), 24)
    ]

def anotherMat' : SparseMatrix Int :=
  ofArrayWithDims 3 3
    #[ ((0,0), 75), ((0,1), 54), ((0,2), 8),
       ((1,0), 234), ((1,1), 34), ((1,2), 35),
       ((2,0), 42), ((2,1), 34), ((2,2), 4)
    ]

def anotherMat'' : SparseMatrix Int :=
  ofArrayWithDims 3 2 
    #[ ((0,0), 43), ((0,1), 76),
       ((1,0), 32), ((1,1), 45),
       ((2,0), 21), ((2,1), 7)
     ]

def prodRes : SparseMatrix Int :=
  ofArrayWithDims 3 2
    #[ ((0,0), 3873), ((0,1), 5843),
       ((1,0), 2671), ((1,1), 3811),
       ((2,0), 4049), ((2,1), 5821)
     ]

def hadamardRes : SparseMatrix Int :=
  ofArrayWithDims 3 3
    #[ ((0,0), 4200), ((0,1), 1728), ((0,2), 168),
       ((1,0), 7956), ((1,1), 816), ((1,2), 735),
       ((2,0), 1806), ((2,1), 1802), ((2,2), 96)
    ]

#lspec test "addition works" (mat₁ + mat₂ == res) $
       test "addition works" (mat1 + mat2 == res') $
       test "addition works" (mat1 + mat1 == res'')
#lspec test "multiplication works" (mat₁ * mat₂ == resProd) $
       test "multiplication works" (mat1 * mat2 == resProd') $
       test "multiplication works" (anotherMat * anotherMat'' == prodRes)
#lspec test "dim works" (mat1.dim == (2,2))
#lspec test "hadamard works" (hadamard anotherMat anotherMat' == hadamardRes)

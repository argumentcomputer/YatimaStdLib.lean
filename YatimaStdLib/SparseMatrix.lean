import YatimaStdLib.Array
import YatimaStdLib.Ring
import Std.Data.RBMap

def ordCmp (a : Nat × Nat) (b : Nat × Nat) : Ordering :=
  match a.1 < b.1 && a.2 < b.2 with
    | true => .lt
    | _    => if a == b then .eq else .gt

abbrev SparseMatrix (R : Type) := Std.RBMap (Nat × Nat) R ordCmp

variable {R : Type} [Ring R] [Coe Nat R]

open Std.RBMap

def SparseMatrix.rows (m : SparseMatrix R) : Nat :=
  Array.foldr max 0 $ Array.map (fun p => p.1) $ keysArray m

def SparseMatrix.cols (m : SparseMatrix R) : Nat :=
  Array.foldr max 0 $ Array.map (fun p => p.2) $ keysArray m

def SparseMatrix.dim (m : SparseMatrix R) : Nat × Nat :=
  (rows m, cols m) 

instance : Functor SparseMatrix where
  map f m := Std.RBMap.mapVal (fun _ x => f x) m

def SparseMatrix.addition
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R := Id.run do
  let cij i j := findD m₁ (i,j) 0 + findD m₂ (i,j) 0
  if dim m₁ == dim m₂ then
    let mut acc : SparseMatrix R := empty
    for i in [0:m₁.rows] do
      for j in [0:m₁.cols] do
        acc := insert acc (i,j) $ cij i j
      pure acc
  else panic "wrong dim"

def SparseMatrix.multiplication
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R := sorry

def SparseMatrix.hadamard
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R := sorry

def SparseMatrix.dotProduct
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : R := sorry

def sparseMatrixVecProduct (m : SparseMatrix R) (numRows : USize) (z : Array R) : Array R :=
  let vals := Array.map
      (fun i =>
        let (row, col, val) := Array.getD m i (0, 0, 0)
        (row, val * Array.getD z col 0))
      (Array.iota m.size)
  Array.foldr
    (fun (r,v) mz => Array.setD mz r (v + Array.getD mz r 0))
    #[0, numRows.val]
    vals

def SparseMatrix.scale
  (r : R) (m : SparseMatrix R) : SparseMatrix R := (fun x => x * r) <$> m
import YatimaStdLib.Array
import YatimaStdLib.Ring
import Std.Data.RBMap

def ordCmp (a : Nat × Nat) (b : Nat × Nat) : Ordering :=
  match a.1 < b.1 && a.2 < b.2 with
    | true => .lt
    | _    => if a == b then .eq else .gt

abbrev SparseMatrix (R : Type) := Std.RBMap (Nat × Nat) R ordCmp
abbrev Row (R : Type) := Std.RBMap Nat R instOrdNat.compare
abbrev Col (R : Type) := Std.RBMap Nat R instOrdNat.compare

variable {R : Type} [Ring R] [Coe Nat R]

open Std.RBMap

def SparseMatrix.rows (m : SparseMatrix R) : Nat :=
  1 + (Array.foldr max 0 $ Array.map (fun p => p.1) $ keysArray m)

def SparseMatrix.cols (m : SparseMatrix R) : Nat :=
  1 + (Array.foldr max 0 $ Array.map (fun p => p.2) $ keysArray m)

def SparseMatrix.dim (m : SparseMatrix R) : Nat × Nat :=
  (rows m, cols m) 

def SparseMatrix.row (m : SparseMatrix R) (i : Nat) : Row R :=
  Std.RBMap.filter m (fun j _ => i == j.1)

def SparseMatrix.col (m : SparseMatrix R) (i : Nat) : Col R :=
  Std.RBMap.filter m (fun j _ => i == j.2)

instance : Functor SparseMatrix where
  map f m := Std.RBMap.mapVal (fun _ x => f x) m

def SparseMatrix.addition
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R := Id.run do
  let cij i j := findD m₁ (i,j) 0 + findD m₂ (i,j) 0
  let (cols, rows) := (m₁.cols, m₁.rows)
  if dim m₁ == dim m₂ then
    let mut acc : SparseMatrix R := empty
    for i in [0:rows] do
      for j in [0:cols] do
        acc := insert acc (i,j) $ cij i j
    pure acc
  else panic "wrong dim"

/-
def SparseMatrix.ofList (l : List ((Nat × Nat) × R)) : SparseMatrix R :=
  Std.RBMap.ofList l ordCmp
 
def mat1 : SparseMatrix Int := SparseMatrix.ofList [((0,0),4), ((0,1),5), ((1,0),5), ((1,1),5)]

def mat2 : SparseMatrix Int := SparseMatrix.ofList [((0,0),3), ((0,1),9), ((1,0),4), ((1,1),2)]

#eval findD mat2 (0,1) 0
#eval SparseMatrix.addition mat1 mat2
-/

def SparseMatrix.multiplication
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R :=
  let cols₂ := m₂.cols
  let rows₁ := m₁.rows
  if rows₁ == cols₂ then
    let cij i j := sorry
  else panic "wrong dim"

def SparseMatrix.hadamard
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R := sorry

def SparseMatrix.dotProduct
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : R := sorry

def SparseMatrix.vecProduct (m : SparseMatrix R) (numRows : USize) (z : Array R) : Array R :=
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
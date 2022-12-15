import YatimaStdLib.Array
import YatimaStdLib.Ord
import YatimaStdLib.Ring
import YatimaStdLib.RBMap
import Std.Data.RBMap

structure SparseMatrix (R : Type _) where
  entries : Std.RBMap (Nat × Nat) R compare
  rows : Nat
  cols : Nat

instance [ToString R] : ToString (SparseMatrix R) where
  toString m := toString ∘ Std.RBMap.Values.toArray $ m.entries

open Std.RBMap

/--
Empty matrix
-/
def SparseMatrix.empty (col : Nat) (row : Nat) : SparseMatrix R :=
  SparseMatrix.mk Std.RBMap.empty col row

/--
Insert a triple
-/
def SparseMatrix.insert
  (col : Nat) (row : Nat) (a : R) (m : SparseMatrix R) : SparseMatrix R :=
  SparseMatrix.mk
    (Std.RBMap.insert m.entries (col,row) a)
    m.rows
    m.cols

/--
Creates a sparse matrix from a list
-/
def ofListWithDims
  (rows : Nat) (cols : Nat) (l : List ((Nat × Nat) × R)) : SparseMatrix R :=
  SparseMatrix.mk
    (Std.RBMap.ofList l compare)
    rows
    cols

/--
Creates a sparse matrix from an array
-/
def ofArrayWithDims
  (rows : Nat) (cols : Nat) (l : Array ((Nat × Nat) × R)) : SparseMatrix R :=
  SparseMatrix.mk
    (Std.RBMap.ofArray l compare)
    rows
    cols

instance : Functor SparseMatrix where
  map f m :=
  SparseMatrix.mk
    (Std.RBMap.mapVal (fun _ x => f x) m.entries)
    m.rows
    m.cols

abbrev Row (R : Type) := Array R
abbrev Col (R : Type) := Array R

instance : Inhabited (SparseMatrix R) where
  default := SparseMatrix.empty 0 0

/--
Matrix dimension
-/
def SparseMatrix.dim (m : SparseMatrix R) : Nat × Nat :=
  (rows m, cols m)

/--
Returns a particular row by an index
-/
def SparseMatrix.row (m : SparseMatrix R) (i : Nat) : Row R :=
  Std.RBMap.valuesArray $
    Std.RBMap.mapKeys
      (Std.RBMap.filter m.entries (fun j _ => i == j.1))
      (fun (a,_) => a)

/--
Returns a particular column by an index
-/
def SparseMatrix.col (m : SparseMatrix R) (i : Nat) : Col R :=
  Std.RBMap.valuesArray $
    Std.RBMap.mapKeys
      (Std.RBMap.filter m.entries (fun j _ => i == j.2))
      (fun (_,b) => b)

/--
Transpose a sparse matrix
-/
def SparseMatrix.transpose (m : SparseMatrix R) : SparseMatrix R :=
  SparseMatrix.mk
    (Std.RBMap.mapKeys m.entries $ fun (a,b) => (b,a))
    m.cols
    m.rows

variable {R : Type} [Ring R] [Coe Nat R] [BEq R]

/--
Returns a triple by given indices
-/
def SparseMatrix.findEntry (m : SparseMatrix R) (p : Nat × Nat) : Nat × Nat × R :=
  let ((row, col), val) := Option.getD (Std.RBMap.findEntry? m.entries p) ((0,0),0)
  (row, col, val)

/--
Returns an element by indices, whenever it exists, or 0 otherwise
-/
def SparseMatrix.findElem (m : SparseMatrix R) (p : Nat × Nat) : R :=
  (SparseMatrix.findEntry m p).2.2

/--
Sparse matrix addition. This implementation assumes that the matrices are
compatible w.r.t. addition and sets the dimension of the resulting matrix as the
dimension of the one provided in the first argument.

Efficiency note: if you know which matrix is the most sparse one, provide it as
the second argument of this function.
-/
def SparseMatrix.addition (m₁ m₂ : SparseMatrix R) : SparseMatrix R :=
  { m₁ with entries := m₂.entries.foldl (init := m₁.entries) fun acc k v₂ =>
    match m₁.entries.find? k with
    | none => acc.insert k v₂
    | some v₁ => acc.insert k (v₁ + v₂) }

instance : Add (SparseMatrix R) where
  add := SparseMatrix.addition

/--
Computes a product between a sparse matrix and an array
-/
def SparseMatrix.vecProduct (m : SparseMatrix R) (v : Col R) : Col R := Id.run do
  let (rows,cols) := (m.rows, m.cols)
  let vals : Array (Nat × R) := Id.run do
    let mut acc := Array.empty
    for i in [0:rows] do
      for k in [0:cols] do
        let (row, col, val) := SparseMatrix.findEntry m (i,k)
        acc := Array.push acc (row, val * Array.getD v col 0)
    pure acc
  Array.foldr 
    (fun (r,v) mz => Array.setD mz r (v + Array.getD mz r 0)) 
    #[0, rows] 
    vals

instance : HMul (SparseMatrix R) (Array R) (Array R) where
  hMul := SparseMatrix.vecProduct

/--
Sparse matrix multiplication
-/
def SparseMatrix.multiplication
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R := Id.run do
  let cols₂ := m₂.cols
  let rows₁ := m₁.rows
  if rows₁ == cols₂ then
    let cij i j : R :=
      Array.foldr (. + .) 0
        (Array.map (fun (a, b) => a * b) (Array.zip (m₁.col i) (m₂.row j)))
    let mut acc : SparseMatrix R := SparseMatrix.empty rows₁ cols₂
    for i in [0:rows₁] do
      for j in [0:cols₂] do
      acc := SparseMatrix.insert i j (cij i j) acc
    pure acc
  else
    panic! "wrong dim"

instance : Mul (SparseMatrix R) where
  mul := SparseMatrix.multiplication

/--
Sparse matrix Hadamard multiplication
-/
def SparseMatrix.hadamard
  (m₁ : SparseMatrix R) (m₂ : SparseMatrix R) : SparseMatrix R := Id.run do
  if m₁.dim == m₂.dim then
    let mut acc : SparseMatrix R := SparseMatrix.empty m₁.rows m₂.cols
    let (rows, cols) := m₁.dim
    for i in [0:rows] do
      for j in [0:cols] do
      acc :=
        SparseMatrix.insert i j
          (SparseMatrix.findElem m₁ (i,j) * SparseMatrix.findElem m₂ (i,j))
          acc
    pure acc
  else
    panic! "wrong dim"

def SparseMatrix.scale
  (r : R) (m : SparseMatrix R) : SparseMatrix R := (fun x => x * r) <$> m
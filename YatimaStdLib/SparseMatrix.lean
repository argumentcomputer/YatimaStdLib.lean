import Batteries.Data.RBMap
import YatimaStdLib.Array
import YatimaStdLib.Ord
import YatimaStdLib.Ring
import YatimaStdLib.RBMap

structure SparseMatrix (R : Type _) where
  entries : Batteries.RBMap (Nat × Nat) R compare
  rows : Nat
  cols : Nat

instance [ToString R] : ToString (SparseMatrix R) where
  toString m :=
  let print (p : (Nat × Nat) × R) :=
    match p with
      | ((i,j), v) =>
        "row:" ++
        toString i ++
        " col:" ++
        toString j ++
        " " ++
        toString v ++ "\n"
  let triples :=
    print <$> Batteries.RBMap.toList m.entries
  List.foldr (. ++ .) "" triples

open Batteries.RBMap

namespace SparseMatrix

/--
Empty matrix
-/
def empty (col : Nat) (row : Nat) : SparseMatrix R :=
  SparseMatrix.mk Batteries.RBMap.empty col row

/--
Insert a triple
-/
def insert (m : SparseMatrix R) (col row : Nat) (a : R) : SparseMatrix R :=
  SparseMatrix.mk
    (Batteries.RBMap.insert m.entries (col,row) a)
    m.rows
    m.cols

/--
Creates a sparse matrix from a list
-/
def ofListWithDims
  (rows : Nat) (cols : Nat) (l : List ((Nat × Nat) × R)) : SparseMatrix R :=
  SparseMatrix.mk
    (Batteries.RBMap.ofList l compare)
    rows
    cols

/--
Creates a sparse matrix from an array
-/
def ofArrayWithDims
  (rows : Nat) (cols : Nat) (l : Array ((Nat × Nat) × R)) : SparseMatrix R :=
  SparseMatrix.mk
    (Batteries.RBMap.ofArray l compare)
    rows
    cols

instance : Functor SparseMatrix where
  map f m :=
  SparseMatrix.mk
    (Batteries.RBMap.mapVal (fun _ x => f x) m.entries)
    m.rows
    m.cols

instance : Inhabited (SparseMatrix R) where
  default := SparseMatrix.empty 0 0

/--
Matrix dimension
-/
def dim (m : SparseMatrix R) : Nat × Nat :=
  (m.rows, m.cols)

/--
Transpose a sparse matrix
-/
def transpose (m : SparseMatrix R) : SparseMatrix R :=
  SparseMatrix.mk
    (Batteries.RBMap.mapKeys m.entries $ fun (a,b) => (b,a))
    m.cols
    m.rows

variable [Ring R] [BEq R]

/--
Sparse matrix addition. This implementation assumes that the matrices have the
same dimensions and sets the dimension of the resulting matrix as the dimensions
of the one provided in the first argument.

Efficiency note: if you know which matrix is the most sparse one, provide it as
the second argument of this function.
-/
def addition (m₁ m₂ : SparseMatrix R) : SparseMatrix R :=
  { m₁ with entries := m₂.entries.foldl (init := m₁.entries) fun acc k v₂ =>
    match m₁.entries.find? k with
    | none => acc.insert k v₂
    | some v₁ => acc.insert k (v₁ + v₂) }

instance : Add (SparseMatrix R) where
  add := SparseMatrix.addition

abbrev SparseArray R := Batteries.RBMap Nat R compare

def SparseArray.zipProd (x y : SparseArray R) : SparseArray R :=
  y.foldl (init := default) fun acc k v => match x.find? k with
    | none => acc
    | some v' => acc.insert k (v * v')

def SparseArray.sum (x : SparseArray R) : R :=
  x.foldl (init := 0) fun acc _ v => acc + v

/-- Removes all entries whose value is zero -/
def SparseArray.prune (x : SparseArray R) : SparseArray R :=
  x.foldl (init := default) fun acc k v =>
    if v == 0 then acc else acc.insert k v

instance : BEq (SparseArray R) where
  beq x y := x.prune == y.prune

def Array.toSparse (x : Array R) : SparseArray R :=
  SparseArray.prune $ Batteries.RBMap.fromArray $ Array.zip (Array.iota x.size) (x : Array R)

def collectRows (m : SparseMatrix R) : Batteries.RBMap Nat (SparseArray R) compare :=
  m.entries.foldl (init := default) fun acc (i, j) v => match acc.find? i with
    | some arr => acc.insert i (arr.insert j v)
    | none => acc.insert i (.single j v)

def collectCols (m : SparseMatrix R) : Batteries.RBMap Nat (SparseArray R) compare :=
  m.entries.foldl (init := default) fun acc (i, j) v => match acc.find? j with
    | some arr => acc.insert j (arr.insert i v)
    | none => acc.insert j (.single i v)

/--
Sparse matrix multiplication. Assumes that the input matrices are compatible
w.r.t. multiplication
-/
def multiplication (m₁ m₂ : SparseMatrix R) : SparseMatrix R :=
  let rCols := collectCols m₂
  let entries := collectRows m₁ |>.foldl (init := default) fun acc i r =>
    rCols.foldl (init := acc) fun acc j c =>
      acc.insert (i, j) (r.zipProd c).sum
  ⟨entries, m₁.rows, m₂.cols⟩

instance : Mul (SparseMatrix R) where
  mul := multiplication

instance : HMul (SparseMatrix R) (SparseArray R) (SparseArray R) where
  hMul m v := m.collectRows |>.foldl (init := default)
    fun acc i r => acc.insert i (r.zipProd v).sum

/--
Sparse matrix Hadamard multiplication. This implementation assumes that the
matrices have the same dimensions and sets the dimension of the resulting matrix
as the dimensions of the one provided in the first argument.

Efficiency note: if you know which matrix is the most sparse one, provide it as
the second argument of this function.
-/
def hadamard (m₁ m₂ : SparseMatrix R) : SparseMatrix R :=
  { m₁ with entries := m₂.entries.foldl (init := default) fun acc k v =>
    match m₁.entries.find? k with
    | none => acc
    | some v' => acc.insert k (v * v') }

/-- Multiplies each element in the `SparseMatrix R` by a scalar `r : R` -/
def scale (m : SparseMatrix R) (r : R) : SparseMatrix R :=
  if r == 0 then default else (fun x => x * r) <$> m

/-- Removes all entries whose value is zero -/
def prune (m : SparseMatrix R) : SparseMatrix R :=
  { m with entries := m.entries.foldl (init := default) fun acc k v =>
    if v == 0 then acc else acc.insert k v }

instance : BEq (SparseMatrix R) where
  beq x y :=
    let (x, y) := (x.prune, y.prune)
    x.dim == y.dim && x.entries == y.entries

end SparseMatrix

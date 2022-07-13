import YatimaStdLib.String

inductive Tree (α : Type) where 
  | empty : Tree α
  | node  : α → List (Tree α) → Tree α
  deriving BEq, Repr

namespace Tree

def isEmpty : Tree α → Bool
  | empty  => true
  | _      => false

instance : Inhabited (Tree α) :=
  ⟨empty⟩

open String in
partial def toString [ToString α] (t : Tree α) : String :=
  let rec aux (indent : Nat) : Tree α → String
  | empty => s!"{blankIndent indent}⟦⟧"
  | node x ts =>
    if ts.isEmpty then s!"{blankIndent indent}⟦{x}⟧"
    else s!"{blankIndent indent}⟦{x}\n{"\n".intercalate $ ts.map $ aux (indent + 1)}⟧"
  aux 0 t

instance [ToString α] : ToString (Tree α) :=
  ⟨toString⟩

partial def size : Tree α → Nat
  | empty     => 0
  | node _ ts => 1 + (ts.map size).foldl (init := 0) (· + ·)

@[inline] protected def pure (a : α) : Tree α :=
  node a []

@[inline] partial def bind : Tree α → (α → Tree β) → Tree β :=
  fun x b => match x with 
  | empty     => empty 
  | node x ts => 
    match b x with 
    | empty       => empty
    | node x' ts' => node x' (ts' ++ List.map (fun ta => bind ta b) ts)

instance : Monad Tree where
  pure := .pure
  bind := .bind

mutual

  partial def preorder : Tree α → List α
    | empty     => []
    | node x ts => x :: preorderF ts
  
  partial def preorderF (ts : List $ Tree α) : List α :=
    (ts.map preorder).join

end

mutual

  partial def postorder : Tree α → List α
    | empty     => []
    | node x ts => postorderF ts ++ [x]
  
  partial def postorderF (ts : List $ Tree α) : List α :=
    (ts.map postorder).join

end

end Tree

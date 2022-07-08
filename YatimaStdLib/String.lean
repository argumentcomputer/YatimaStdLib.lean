import YatimaStdLib.List

namespace String

def splitAtString (n : Nat) (str : String) : String × String :=
  match List.splitAt n str.data with
    | (s₁,s₂) => (String.mk s₁, String.mk s₂)

end String

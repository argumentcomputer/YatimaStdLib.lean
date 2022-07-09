namespace Option

def option (b : B) (f : A → B) (oa : Option A) : B :=
  match oa with
    | none   => b
    | some x => f x

end Option
